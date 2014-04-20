;caculate distence between each pair of cities
(defrule calcdist
	?c <- (city ?dptcity to ?destcity ?dist $?rest)
	=>
	(retract ?c)
	(assert (distance ?dptcity ?destcity ?dist))
	(assert (city ?dptcity to $?rest))
)

(defrule prefacts "PreselectTruck ?truck ?package ?pickuptime"
	(not (PreselectTruck ? ? ?))
	=>
	(assert (PreselectTruck 0 0 9999))
)

;select the truck which can arrive earliset
(defrule selecttruck1
	?pkg <- (package ?npkg ?dpt ?dlr ?psize ?ot ?edet)
	(not (package $? ?ot1&:(< ?ot1 ?ot) ?))
	?pre <- (PreselectTruck ? ? ?putime)
	(distance ?current ?dpt ?dist)
	?trk <- (truck ?ntrk ?current ? ?tsize&:(>= ?tsize ?psize) ?trktime&:(<= ?trktime ?ot)&:(< (+ ?ot ?dist) ?putime) idle none)
	=>
	(retract ?pre)
	(assert (PreselectTruck ?ntrk ?npkg (+ ?dist ?ot)))
)

(defrule selecttruck2
	?pkg <- (package ?npkg ?dpt ?dlr ?psize ?ot ?edet)
	(not (package $? ?ot1&:(< ?ot1 ?ot) ?))
	?pre <- (PreselectTruck ? ? ?putime)
	(distance ?current ?dpt ?dist)
	?trk <- (truck ?ntrk ?current ? ?tsize&:(>= ?tsize ?psize) ?trktime&:(> ?trktime ?ot)&:(< (+ ?dist ?trktime) ?putime) idle none)
	=>
	(retract ?pre)
	(assert (PreselectTruck ?ntrk ?npkg (+ ?dist ?trktime)))
)

;generate simulations of transport
(defrule gensimulation
	?pkg <- (package ?npkg ?dpt ?dlr ?psize ?ot ?edet)
	?trk <- (truck ?ntrk ?current none ?tsize ?trktime idle none)
	?pre <- (PreselectTruck ?ntrk&:(!= ?ntrk 0) ?npkg ?trkarrtime)
	(distance ?current ?dpt ?dist1)
	(distance ?dpt ?dlr ?dist2)
	=>
	(retract ?pkg ?trk ?pre)
	(assert (PreselectTruck 0 0 9999))
	(assert (truck ?ntrk ?dlr none ?tsize (+ ?trkarrtime ?dist2) idle none))
	(assert (Simulation (- ?trkarrtime ?dist1) ?npkg ?ntrk dispatched ?dpt ?trkarrtime))
	(assert (Simulation ?trkarrtime ?npkg ?ntrk delivering ?dlr (+ ?trkarrtime ?dist2)))
	(assert (delivered ?npkg ?dpt ?dlr ?psize ?ot ?edet (+ ?trkarrtime ?dist2)))
)


;get the finish time and initialize average report
(defrule finishTime
	(not (package $?))
	(not (FinishTime ?))
	?last <- (delivered ? ? ? ? ? ? ?lasttime)
	(not (delivered ? ? ? ? ? ? ?lt&:(> ?lt ?lasttime)))
	(not (avgPkg $?))
	(not (already print truck))
	(not (already print package))
	=>
	(assert (FinishTime ?lasttime))
	(assert (avgPkg wait 0 ontNo 0 lateNo 0 lateness 0))
)

;initialize truck report
(defrule ini_truckreport
	(truck ?ntrk $?)
	(not (trkReport ?ntrk $?))
	=>
	(assert (trkReport ?ntrk busy 0 pkgQty 0 ocp 0 tdlr 0 ))
)

;calculate datas of on time packages
(defrule calcdatas_ontime
	?s1 <- (Simulation ?start ?npkg ?ntrk dispatched ? ?pickup)
	?s2 <- (Simulation ?pickup ?npkg ?ntrk delivering ? ?deliver)
	?d <- (delivered ?npkg ? ? ?pkgsize ?ot ?expde ?deliver&:(<= ?deliver ?expde))
	?avg <- (avgPkg wait ?wait ontNo ?ontNo lateNo ?lateNo lateness ?lateness)
	?trk <- (trkReport ?ntrk busy ?busy pkgQty ?pkgQty ocp ?ocp tdlr ?tdlr )
	=>
	(retract ?s1 ?s2 ?d ?avg ?trk)
	(assert (avgPkg wait (+ ?wait (- ?pickup ?ot)) ontNo (+ ?ontNo 1) lateNo ?lateNo lateness ?lateness))
	(assert (trkReport ?ntrk busy (+ ?busy (- ?deliver ?start)) pkgQty (+ ?pkgQty 1) ocp (+ ?ocp ?pkgsize) tdlr (+ ?tdlr (- ?deliver ?pickup))))
	(assert (pkgReport ?npkg  wait (- ?pickup ?ot) puT ?pickup dlrT ?deliver ont yes lateness 0))
)

;calculate datas of late packages
(defrule calcdatas_late
	?s1 <- (Simulation ?start ?npkg ?ntrk dispatched ? ?pickup)
	?s2 <- (Simulation ?pickup ?npkg ?ntrk delivering ? ?deliver)
	?d <- (delivered ?npkg ? ? ?pkgsize ?ot ?expde ?deliver&:(> ?deliver ?expde))
	?avg <- (avgPkg wait ?wait ontNo ?ontNo lateNo ?lateNo lateness ?lateness)
	?trk <- (trkReport ?ntrk busy ?busy pkgQty ?pkgQty ocp ?ocp tdlr ?tdlr )
	=>
	(retract ?s1 ?s2 ?d ?avg ?trk)
	(assert (avgPkg wait (+ ?wait (- ?pickup ?ot)) ontNo ?ontNo lateNo (+ ?lateNo 1) lateness (+ ?lateness (- ?deliver ?expde))))
	(assert (trkReport ?ntrk busy (+ ?busy (- ?deliver ?start)) pkgQty (+ ?pkgQty 1) ocp (+ ?ocp ?pkgsize) tdlr (+ ?tdlr (- ?deliver ?pickup))))
	(assert (pkgReport ?npkg  wait (- ?pickup ?ot) puT ?pickup dlrT ?deliver ont no lateness (- ?deliver ?expde)))
)


;calculate truck report
(defrule truckreport1
	(not (Simulation $?))
	(trkReport ?ntrk busy ?totalbusy pkgQty ?totalpkg&:(!= ?totalpkg 0) ocp ?totalocp tdlr ?totaldlr)
	?trk <- (truck ?ntrk ? none ?size ? idle none)
	(FinishTime ?lasttime)
	(not (TrkRpt ?ntrk $?))	
	=>
	(retract ?trk)
	(bind ?wait (- ?lasttime ?totalbusy))
	(bind ?busyP  (/ (integer (* 10000 (/ ?totalbusy ?lasttime))) 100))
	(bind ?ocpP (/ (integer (* 10000 (/ ?totalocp (* ?totalpkg ?size))))100))
	(bind ?nondlr (- ?totalbusy ?totaldlr))
	(bind ?dlrP (/ (integer (* 10000 (/ ?totaldlr ?totalbusy)))100))
	(assert (TrkRpt ?ntrk ?wait ?totalbusy ?busyP ?totalpkg ?ocpP ?nondlr ?dlrP))
)

(defrule truckreport2
	(not (Simulation $?))
	(trkReport ?ntrk busy ?totalbusy pkgQty 0 ocp ?totalocp tdlr ?totaldlr)
	?trk <- (truck ?ntrk $?)	
	(FinishTime ?lasttime)
	(not (TrkRpt ?ntrk $?))	
	=>
	(retract ?trk)
	(assert (TrkRpt ?ntrk ?lasttime 0 0.00 0 0.00 0 0.00))
)

;print truck report title
(defrule printtruck
	(not (already print truck))
	=>
	(assert (already print truck))
	(printout t Truck Report: crlf)
	(printout t Truck_No. Total_waittime Total_busytime %_of_busytime #_packages %_of_occupied Non_delivery_time %_of_delivering_time crlf)
)


;print truck report
(defrule truckreport
	(already print truck)
	?t <- (TrkRpt ?ntrk ?wait ?totalbusy ?busyP ?totalpkg ?ocpP ?nondlr ?dlrP)
	(not (TrkRpt ?nt&:(< ?nt ?ntrk) $?))
	=>
	(retract ?t)
	(printout t ?ntrk "	" ?wait "	" ?totalbusy "	" ?busyP "	" ?totalpkg "	" ?ocpP "	" ?nondlr "	" ?dlrP crlf)
)

;print package report title
(defrule printpackage
	(not (already print package))
	=>
	(assert (already print package))
	(printout t Package Report: crlf)
	(printout t PackageReport Package_No. Wait_time Pickup_time Delivery_time On_time Lateness crlf)
)

;print package report
(defrule packagereport
	(already print package)
	(not (Simulation $?))
	?pkg<-(pkgReport ?nkpg wait ?w puT ?p dlrT ?d ont ?o lateness ?l)
	(not (pkgReport ?n&:(< ?n ?nkpg) $?))
	=>
	(retract ?pkg)
	(printout t ?nkpg "	" ?w "	" ?p "	" ?d "	" ?o "	" ?l crlf)
)

;Print average package report
(defrule average
	(not (Simulation $?))
	(not (TrkRpt $?))	
	(not (pkgReport $?))
	?avgpkg<-(avgPkg wait ?wait ontNo ?ontNo lateNo ?lateNo lateness ?totallate)
	=>
	(printout t "Average Package Information " crlf)
	(printout t "Average wait time: " (/ ?wait (+ ?lateNo ?ontNo)) crlf)
	(printout t "On time packages: " ?ontNo crlf)
	(printout t "Late packages: " ?lateNo crlf)
	(printout t "Average lateness of late ones: " (/ ?totallate ?lateNo) crlf)
	(printout t "Average lateness of all: " (/ ?totallate (+ ?lateNo ?ontNo)) crlf)
	(printout t "--------" crlf)
)
