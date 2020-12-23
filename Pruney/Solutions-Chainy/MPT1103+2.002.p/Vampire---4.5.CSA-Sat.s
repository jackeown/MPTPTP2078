%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:34 EST 2020

% Result     : CounterSatisfiable 5.93s
% Output     : Saturation 5.93s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 100 expanded)
%              Number of leaves         :  100 ( 100 expanded)
%              Depth                    :    0
%              Number of atoms          :  127 ( 127 expanded)
%              Number of equality atoms :   91 (  91 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u1445,negated_conjecture,
    ( ~ ( sK2 != k2_struct_0(sK1) )
    | sK2 != k2_struct_0(sK1) )).

tff(u1444,axiom,(
    ! [X4] : k2_xboole_0(X4,X4) = X4 )).

tff(u1443,axiom,(
    ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) )).

tff(u1442,axiom,(
    ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),X0) )).

tff(u1441,axiom,(
    ! [X3,X2] : k2_xboole_0(X3,X2) = k2_xboole_0(k2_xboole_0(X3,X2),X2) )).

tff(u1440,axiom,(
    ! [X3,X2] : k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3)) )).

tff(u1439,axiom,(
    ! [X3,X4] : k2_xboole_0(X3,X4) = k2_xboole_0(X4,k2_xboole_0(X3,X4)) )).

tff(u1438,axiom,(
    ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) )).

tff(u1437,axiom,(
    ! [X55,X56] : k2_xboole_0(X55,X56) = k5_xboole_0(X55,k4_xboole_0(k2_xboole_0(X55,X56),X55)) )).

tff(u1436,axiom,(
    ! [X56,X57] : k2_xboole_0(X57,X56) = k5_xboole_0(X56,k4_xboole_0(k2_xboole_0(X57,X56),X56)) )).

tff(u1435,axiom,(
    ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 )).

tff(u1434,axiom,(
    ! [X1,X2] : k2_xboole_0(X2,k3_xboole_0(X1,X2)) = X2 )).

tff(u1433,axiom,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 )).

tff(u1432,axiom,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 )).

tff(u1431,axiom,(
    ! [X9,X10] : k2_xboole_0(k3_xboole_0(X9,X10),X9) = X9 )).

tff(u1430,axiom,(
    ! [X11,X12] : k2_xboole_0(k3_xboole_0(X12,X11),X11) = X11 )).

tff(u1429,axiom,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 )).

tff(u1428,axiom,(
    ! [X3,X2] : k3_xboole_0(X2,k2_xboole_0(X2,X3)) = X2 )).

tff(u1427,axiom,(
    ! [X3,X4] : k3_xboole_0(X3,k2_xboole_0(X4,X3)) = X3 )).

tff(u1426,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0) )).

tff(u1425,axiom,(
    ! [X3,X2] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) )).

tff(u1424,axiom,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X5,k3_xboole_0(X5,X6)) )).

tff(u1423,axiom,(
    ! [X1,X2] : k3_xboole_0(X2,X1) = k3_xboole_0(X1,k3_xboole_0(X2,X1)) )).

tff(u1422,axiom,(
    ! [X3,X4] : k3_xboole_0(X4,X3) = k3_xboole_0(k3_xboole_0(X4,X3),X3) )).

tff(u1421,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) )).

tff(u1420,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) )).

tff(u1419,axiom,(
    ! [X44,X43] : k3_xboole_0(k2_xboole_0(X43,X44),X43) = X43 )).

tff(u1418,axiom,(
    ! [X44,X45] : k3_xboole_0(k2_xboole_0(X45,X44),X44) = X44 )).

tff(u1417,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 )).

tff(u1416,negated_conjecture,
    ( k4_xboole_0(sK2,sK2) != k4_xboole_0(sK2,u1_struct_0(sK1))
    | k4_xboole_0(sK2,sK2) = k4_xboole_0(sK2,u1_struct_0(sK1)) )).

tff(u1415,axiom,(
    ! [X3,X2] : k4_xboole_0(X2,X3) = k4_xboole_0(X2,k3_xboole_0(X2,X3)) )).

tff(u1414,axiom,(
    ! [X11,X10] : k4_xboole_0(X11,k3_xboole_0(X10,X11)) = k4_xboole_0(X11,X10) )).

tff(u1413,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) )).

tff(u1412,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) )).

tff(u1411,axiom,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) )).

tff(u1410,axiom,(
    ! [X29,X30] : k4_xboole_0(k2_xboole_0(X29,X30),X29) = k5_xboole_0(k2_xboole_0(X29,X30),X29) )).

tff(u1409,axiom,(
    ! [X31,X30] : k4_xboole_0(k2_xboole_0(X31,X30),X30) = k5_xboole_0(k2_xboole_0(X31,X30),X30) )).

tff(u1408,axiom,(
    ! [X5,X6] : k4_xboole_0(k3_xboole_0(X5,X6),X5) = k5_xboole_0(k3_xboole_0(X5,X6),k3_xboole_0(X5,X6)) )).

tff(u1407,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(sK1),sK2) != k5_xboole_0(u1_struct_0(sK1),sK2)
    | k4_xboole_0(u1_struct_0(sK1),sK2) = k5_xboole_0(u1_struct_0(sK1),sK2) )).

tff(u1406,negated_conjecture,
    ( ~ r1_tarski(sK2,sK2)
    | ! [X0] : k4_xboole_0(sK2,X0) = k7_subset_1(sK2,sK2,X0) )).

tff(u1405,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) )).

tff(u1404,axiom,(
    ! [X20,X22,X21] : k7_subset_1(k2_xboole_0(X20,X21),X20,X22) = k4_xboole_0(X20,X22) )).

tff(u1403,axiom,(
    ! [X22,X21,X23] : k7_subset_1(k2_xboole_0(X22,X21),X21,X23) = k4_xboole_0(X21,X23) )).

tff(u1402,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u1401,axiom,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 )).

tff(u1400,axiom,(
    ! [X1,X0] : k5_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 )).

tff(u1399,axiom,(
    ! [X7,X6] : k5_xboole_0(k3_xboole_0(X6,k2_xboole_0(X6,X7)),k1_xboole_0) = X6 )).

tff(u1398,axiom,(
    ! [X9,X8] : k5_xboole_0(k3_xboole_0(X8,k2_xboole_0(X9,X8)),k1_xboole_0) = X8 )).

tff(u1397,axiom,(
    ! [X1,X2] : k5_xboole_0(k3_xboole_0(X2,X1),k4_xboole_0(X1,X2)) = X1 )).

tff(u1396,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(sK1),k4_xboole_0(sK2,sK2)) != k2_xboole_0(sK2,u1_struct_0(sK1))
    | k5_xboole_0(u1_struct_0(sK1),k4_xboole_0(sK2,sK2)) = k2_xboole_0(sK2,u1_struct_0(sK1)) )).

tff(u1395,axiom,(
    ! [X1,X2] : k4_xboole_0(k3_xboole_0(X2,X1),X1) = k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X2,X1)) )).

tff(u1394,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) )).

tff(u1393,axiom,(
    ! [X7] : k1_xboole_0 = k3_xboole_0(X7,k1_xboole_0) )).

tff(u1392,axiom,(
    ! [X7] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X7) )).

tff(u1391,axiom,(
    ! [X3,X2] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,X3),X2) )).

tff(u1390,axiom,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(X3,X3) )).

tff(u1389,axiom,(
    ! [X1,X2] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,X1),X1) )).

tff(u1388,axiom,(
    ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) )).

tff(u1387,axiom,(
    ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0)) )).

tff(u1386,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK2,u1_struct_0(sK1))
    | k1_xboole_0 = k4_xboole_0(sK2,u1_struct_0(sK1)) )).

tff(u1385,axiom,(
    ! [X28] : k1_xboole_0 = k5_xboole_0(X28,X28) )).

tff(u1384,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2) )).

tff(u1383,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK1),sK2,sK2)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),sK2,sK2) )).

tff(u1382,axiom,(
    ! [X5,X4] : k1_xboole_0 = k7_subset_1(X4,k1_xboole_0,X5) )).

tff(u1381,axiom,(
    ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

tff(u1380,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u1379,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK1),sK2,X0) = k4_xboole_0(sK2,X0) )).

tff(u1378,axiom,(
    ! [X1,X0,X2] : k7_subset_1(X0,k3_xboole_0(X0,X1),X2) = k4_xboole_0(k3_xboole_0(X0,X1),X2) )).

tff(u1377,axiom,(
    ! [X1,X0,X2] : k7_subset_1(X0,k3_xboole_0(X1,X0),X2) = k4_xboole_0(k3_xboole_0(X1,X0),X2) )).

tff(u1376,negated_conjecture,
    ( u1_struct_0(sK1) != k2_xboole_0(sK2,u1_struct_0(sK1))
    | u1_struct_0(sK1) = k2_xboole_0(sK2,u1_struct_0(sK1)) )).

tff(u1375,negated_conjecture,
    ( u1_struct_0(sK1) != k2_xboole_0(u1_struct_0(sK1),sK2)
    | u1_struct_0(sK1) = k2_xboole_0(u1_struct_0(sK1),sK2) )).

tff(u1374,negated_conjecture,
    ( u1_struct_0(sK1) != k5_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK1),sK2))
    | u1_struct_0(sK1) = k5_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK1),sK2)) )).

tff(u1373,negated_conjecture,
    ( sK2 != k3_xboole_0(sK2,u1_struct_0(sK1))
    | sK2 = k3_xboole_0(sK2,u1_struct_0(sK1)) )).

tff(u1372,negated_conjecture,
    ( sK2 != k3_xboole_0(u1_struct_0(sK1),sK2)
    | sK2 = k3_xboole_0(u1_struct_0(sK1),sK2) )).

tff(u1371,axiom,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) )).

tff(u1370,axiom,(
    ! [X1,X3,X2] :
      ( ~ r1_tarski(X2,X1)
      | k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) )).

tff(u1369,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) )).

tff(u1368,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u1367,axiom,(
    ! [X27,X28] : r1_tarski(X27,k2_xboole_0(X27,X28)) )).

tff(u1366,axiom,(
    ! [X29,X28] : r1_tarski(X28,k2_xboole_0(X29,X28)) )).

tff(u1365,axiom,(
    ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) )).

tff(u1364,axiom,(
    ! [X7,X8] : r1_tarski(k3_xboole_0(X8,X7),X7) )).

tff(u1363,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) )).

tff(u1362,negated_conjecture,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),k1_xboole_0)
    | r1_tarski(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),k1_xboole_0) )).

tff(u1361,negated_conjecture,
    ( ~ r1_tarski(sK2,u1_struct_0(sK1))
    | r1_tarski(sK2,u1_struct_0(sK1)) )).

tff(u1360,negated_conjecture,
    ( ~ r1_tarski(sK2,sK2)
    | r1_tarski(sK2,sK2) )).

tff(u1359,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) )).

tff(u1358,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) )).

tff(u1357,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) )).

tff(u1356,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u1355,axiom,(
    ! [X25,X26] : m1_subset_1(X25,k1_zfmisc_1(k2_xboole_0(X25,X26))) )).

tff(u1354,axiom,(
    ! [X27,X26] : m1_subset_1(X26,k1_zfmisc_1(k2_xboole_0(X27,X26))) )).

tff(u1353,axiom,(
    ! [X1,X0] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0)) )).

tff(u1352,axiom,(
    ! [X5,X6] : m1_subset_1(k3_xboole_0(X6,X5),k1_zfmisc_1(X5)) )).

tff(u1351,axiom,(
    ! [X2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2)) )).

tff(u1350,negated_conjecture,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),k1_zfmisc_1(k1_xboole_0))
    | m1_subset_1(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),k1_zfmisc_1(k1_xboole_0)) )).

tff(u1349,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) )).

tff(u1348,axiom,(
    ! [X1] : ~ sP0(k2_struct_0(X1),X1) )).

tff(u1347,axiom,(
    ! [X1,X0] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0) ) )).

tff(u1346,negated_conjecture,
    ( ~ sP0(sK2,sK1)
    | sP0(sK2,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:35:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (27399)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (27400)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (27397)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.37/0.56  % (27397)Refutation not found, incomplete strategy% (27397)------------------------------
% 1.37/0.56  % (27397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (27399)Refutation not found, incomplete strategy% (27399)------------------------------
% 1.37/0.56  % (27399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.57  % (27413)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.37/0.57  % (27397)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.57  
% 1.37/0.57  % (27397)Memory used [KB]: 1663
% 1.37/0.57  % (27397)Time elapsed: 0.120 s
% 1.37/0.57  % (27397)------------------------------
% 1.37/0.57  % (27397)------------------------------
% 1.37/0.57  % (27422)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.63/0.57  % (27401)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.63/0.57  % (27399)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.57  
% 1.63/0.57  % (27399)Memory used [KB]: 10874
% 1.63/0.57  % (27399)Time elapsed: 0.128 s
% 1.63/0.57  % (27399)------------------------------
% 1.63/0.57  % (27399)------------------------------
% 1.63/0.57  % (27403)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.63/0.58  % (27410)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.63/0.58  % (27405)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.63/0.58  % (27414)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.63/0.58  % (27414)Refutation not found, incomplete strategy% (27414)------------------------------
% 1.63/0.58  % (27414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % (27414)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.58  
% 1.63/0.58  % (27414)Memory used [KB]: 10618
% 1.63/0.58  % (27414)Time elapsed: 0.145 s
% 1.63/0.58  % (27414)------------------------------
% 1.63/0.58  % (27414)------------------------------
% 1.63/0.59  % (27419)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.63/0.59  % (27422)Refutation not found, incomplete strategy% (27422)------------------------------
% 1.63/0.59  % (27422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.59  % (27422)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.59  
% 1.63/0.59  % (27422)Memory used [KB]: 6652
% 1.63/0.59  % (27422)Time elapsed: 0.149 s
% 1.63/0.59  % (27422)------------------------------
% 1.63/0.59  % (27422)------------------------------
% 1.63/0.59  % (27408)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.63/0.59  % (27412)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.63/0.59  % (27402)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.63/0.59  % (27408)Refutation not found, incomplete strategy% (27408)------------------------------
% 1.63/0.59  % (27408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.59  % (27408)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.59  
% 1.63/0.59  % (27408)Memory used [KB]: 10618
% 1.63/0.59  % (27408)Time elapsed: 0.165 s
% 1.63/0.59  % (27408)------------------------------
% 1.63/0.59  % (27408)------------------------------
% 1.63/0.60  % (27420)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.63/0.60  % (27398)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.63/0.60  % (27420)Refutation not found, incomplete strategy% (27420)------------------------------
% 1.63/0.60  % (27420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.60  % (27420)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.60  
% 1.63/0.60  % (27420)Memory used [KB]: 1663
% 1.63/0.60  % (27420)Time elapsed: 0.151 s
% 1.63/0.60  % (27420)------------------------------
% 1.63/0.60  % (27420)------------------------------
% 1.63/0.60  % (27404)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.63/0.60  % (27405)Refutation not found, incomplete strategy% (27405)------------------------------
% 1.63/0.60  % (27405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.60  % (27405)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.60  
% 1.63/0.60  % (27405)Memory used [KB]: 10874
% 1.63/0.60  % (27405)Time elapsed: 0.140 s
% 1.63/0.60  % (27405)------------------------------
% 1.63/0.60  % (27405)------------------------------
% 1.63/0.60  % (27419)Refutation not found, incomplete strategy% (27419)------------------------------
% 1.63/0.60  % (27419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.60  % (27419)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.60  
% 1.63/0.60  % (27419)Memory used [KB]: 10746
% 1.63/0.60  % (27419)Time elapsed: 0.155 s
% 1.63/0.60  % (27419)------------------------------
% 1.63/0.60  % (27419)------------------------------
% 1.63/0.60  % (27425)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.63/0.61  % (27406)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.63/0.61  % (27418)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.63/0.61  % (27421)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.63/0.61  % (27424)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.63/0.61  % (27401)Refutation not found, incomplete strategy% (27401)------------------------------
% 1.63/0.61  % (27401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.61  % (27401)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.61  
% 1.63/0.61  % (27401)Memory used [KB]: 6268
% 1.63/0.61  % (27401)Time elapsed: 0.176 s
% 1.63/0.61  % (27401)------------------------------
% 1.63/0.61  % (27401)------------------------------
% 1.63/0.61  % (27417)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.63/0.62  % (27412)Refutation not found, incomplete strategy% (27412)------------------------------
% 1.63/0.62  % (27412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.62  % (27412)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.62  
% 1.63/0.62  % (27412)Memory used [KB]: 6140
% 1.63/0.62  % (27412)Time elapsed: 0.003 s
% 1.63/0.62  % (27412)------------------------------
% 1.63/0.62  % (27412)------------------------------
% 1.63/0.62  % (27416)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.63/0.62  % (27411)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.63/0.62  % (27415)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.63/0.63  % (27426)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.63/0.63  % (27409)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.63/0.63  % (27423)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.63/0.63  % (27417)Refutation not found, incomplete strategy% (27417)------------------------------
% 1.63/0.63  % (27417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.63  % (27417)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.63  
% 1.63/0.63  % (27417)Memory used [KB]: 10746
% 1.63/0.63  % (27417)Time elapsed: 0.200 s
% 1.63/0.63  % (27417)------------------------------
% 1.63/0.63  % (27417)------------------------------
% 1.63/0.63  % (27407)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.63/0.64  % (27404)Refutation not found, incomplete strategy% (27404)------------------------------
% 1.63/0.64  % (27404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.65  % (27402)Refutation not found, incomplete strategy% (27402)------------------------------
% 1.63/0.65  % (27402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.65  % (27402)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.65  
% 1.63/0.65  % (27402)Memory used [KB]: 6652
% 1.63/0.65  % (27402)Time elapsed: 0.202 s
% 1.63/0.65  % (27402)------------------------------
% 1.63/0.65  % (27402)------------------------------
% 1.63/0.65  % (27418)Refutation not found, incomplete strategy% (27418)------------------------------
% 1.63/0.65  % (27418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.65  % (27418)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.65  
% 1.63/0.65  % (27418)Memory used [KB]: 1918
% 1.63/0.65  % (27418)Time elapsed: 0.207 s
% 1.63/0.65  % (27418)------------------------------
% 1.63/0.65  % (27418)------------------------------
% 1.63/0.65  % (27407)Refutation not found, incomplete strategy% (27407)------------------------------
% 1.63/0.65  % (27407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.65  % (27407)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.65  
% 1.63/0.65  % (27407)Memory used [KB]: 10618
% 1.63/0.65  % (27407)Time elapsed: 0.199 s
% 1.63/0.65  % (27407)------------------------------
% 1.63/0.65  % (27407)------------------------------
% 2.20/0.66  % (27404)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.66  
% 2.20/0.66  % (27404)Memory used [KB]: 6652
% 2.20/0.66  % (27404)Time elapsed: 0.157 s
% 2.20/0.66  % (27404)------------------------------
% 2.20/0.66  % (27404)------------------------------
% 2.33/0.69  % (27457)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.33/0.69  % (27456)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.33/0.70  % (27454)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.33/0.71  % (27459)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.51/0.73  % (27458)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.54/0.74  % (27460)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.54/0.75  % (27461)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.54/0.75  % (27463)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.54/0.75  % (27458)Refutation not found, incomplete strategy% (27458)------------------------------
% 2.54/0.75  % (27458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.54/0.75  % (27458)Termination reason: Refutation not found, incomplete strategy
% 2.54/0.75  
% 2.54/0.75  % (27458)Memory used [KB]: 10874
% 2.54/0.75  % (27458)Time elapsed: 0.116 s
% 2.54/0.75  % (27458)------------------------------
% 2.54/0.75  % (27458)------------------------------
% 2.54/0.75  % (27466)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 2.54/0.75  % (27455)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.54/0.76  % (27462)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.54/0.76  % (27454)Refutation not found, incomplete strategy% (27454)------------------------------
% 2.54/0.76  % (27454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.54/0.77  % (27398)Refutation not found, incomplete strategy% (27398)------------------------------
% 2.54/0.77  % (27398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.54/0.77  % (27398)Termination reason: Refutation not found, incomplete strategy
% 2.54/0.77  
% 2.54/0.77  % (27398)Memory used [KB]: 6268
% 2.54/0.77  % (27398)Time elapsed: 0.321 s
% 2.54/0.77  % (27398)------------------------------
% 2.54/0.77  % (27398)------------------------------
% 2.54/0.77  % (27454)Termination reason: Refutation not found, incomplete strategy
% 2.54/0.77  
% 2.54/0.77  % (27454)Memory used [KB]: 6908
% 2.54/0.77  % (27454)Time elapsed: 0.136 s
% 2.54/0.77  % (27454)------------------------------
% 2.54/0.77  % (27454)------------------------------
% 2.54/0.78  % (27464)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 2.54/0.78  % (27462)Refutation not found, incomplete strategy% (27462)------------------------------
% 2.54/0.78  % (27462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.54/0.78  % (27462)Termination reason: Refutation not found, incomplete strategy
% 2.54/0.78  
% 2.54/0.78  % (27462)Memory used [KB]: 1791
% 2.54/0.78  % (27462)Time elapsed: 0.134 s
% 2.54/0.78  % (27462)------------------------------
% 2.54/0.78  % (27462)------------------------------
% 2.54/0.79  % (27467)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 2.54/0.79  % (27467)Refutation not found, incomplete strategy% (27467)------------------------------
% 2.54/0.79  % (27467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.54/0.79  % (27467)Termination reason: Refutation not found, incomplete strategy
% 2.54/0.79  
% 2.54/0.79  % (27467)Memory used [KB]: 1663
% 2.54/0.79  % (27467)Time elapsed: 0.081 s
% 2.54/0.79  % (27467)------------------------------
% 2.54/0.79  % (27467)------------------------------
% 2.54/0.79  % (27465)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 2.54/0.80  % (27460)Refutation not found, incomplete strategy% (27460)------------------------------
% 2.54/0.80  % (27460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.54/0.80  % (27460)Termination reason: Refutation not found, incomplete strategy
% 2.54/0.80  
% 2.54/0.80  % (27460)Memory used [KB]: 2302
% 2.54/0.80  % (27460)Time elapsed: 0.159 s
% 2.54/0.80  % (27460)------------------------------
% 2.54/0.80  % (27460)------------------------------
% 2.54/0.80  % (27470)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 3.26/0.87  % (27511)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 3.26/0.89  % (27517)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 3.26/0.90  % (27528)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 3.26/0.90  % (27455)Refutation not found, incomplete strategy% (27455)------------------------------
% 3.26/0.90  % (27455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.26/0.90  % (27455)Termination reason: Refutation not found, incomplete strategy
% 3.26/0.90  
% 3.26/0.90  % (27455)Memory used [KB]: 6140
% 3.26/0.90  % (27455)Time elapsed: 0.254 s
% 3.26/0.90  % (27455)------------------------------
% 3.26/0.90  % (27455)------------------------------
% 3.26/0.91  % (27521)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 3.26/0.91  % (27531)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 3.26/0.91  % (27466)Refutation not found, incomplete strategy% (27466)------------------------------
% 3.26/0.91  % (27466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.26/0.91  % (27466)Termination reason: Refutation not found, incomplete strategy
% 3.26/0.91  
% 3.26/0.91  % (27466)Memory used [KB]: 2174
% 3.26/0.91  % (27466)Time elapsed: 0.232 s
% 3.26/0.91  % (27466)------------------------------
% 3.26/0.91  % (27466)------------------------------
% 3.26/0.91  % (27526)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 3.74/0.97  % (27409)Time limit reached!
% 3.74/0.97  % (27409)------------------------------
% 3.74/0.97  % (27409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.74/0.97  % (27409)Termination reason: Time limit
% 3.74/0.97  
% 3.74/0.97  % (27409)Memory used [KB]: 9083
% 3.74/0.97  % (27409)Time elapsed: 0.532 s
% 3.74/0.97  % (27409)------------------------------
% 3.74/0.97  % (27409)------------------------------
% 3.97/1.03  % (27613)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 3.97/1.04  % (27425)Time limit reached!
% 3.97/1.04  % (27425)------------------------------
% 3.97/1.04  % (27425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.97/1.04  % (27425)Termination reason: Time limit
% 3.97/1.04  
% 3.97/1.04  % (27425)Memory used [KB]: 8827
% 3.97/1.04  % (27425)Time elapsed: 0.603 s
% 3.97/1.04  % (27425)------------------------------
% 3.97/1.04  % (27425)------------------------------
% 5.37/1.05  % (27597)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 5.37/1.06  % (27413)Time limit reached!
% 5.37/1.06  % (27413)------------------------------
% 5.37/1.06  % (27413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.37/1.06  % (27413)Termination reason: Time limit
% 5.37/1.06  
% 5.37/1.06  % (27413)Memory used [KB]: 14967
% 5.37/1.06  % (27413)Time elapsed: 0.618 s
% 5.37/1.06  % (27413)------------------------------
% 5.37/1.06  % (27413)------------------------------
% 5.37/1.06  % (27457)Time limit reached!
% 5.37/1.06  % (27457)------------------------------
% 5.37/1.06  % (27457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.37/1.06  % (27457)Termination reason: Time limit
% 5.37/1.06  
% 5.37/1.06  % (27457)Memory used [KB]: 8443
% 5.37/1.06  % (27457)Time elapsed: 0.412 s
% 5.37/1.06  % (27457)------------------------------
% 5.37/1.06  % (27457)------------------------------
% 5.37/1.09  % (27628)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 5.93/1.13  % SZS status CounterSatisfiable for theBenchmark
% 5.93/1.13  % (27526)# SZS output start Saturation.
% 5.93/1.13  tff(u1445,negated_conjecture,
% 5.93/1.13      ((~(sK2 != k2_struct_0(sK1))) | (sK2 != k2_struct_0(sK1)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1444,axiom,
% 5.93/1.13      (![X4] : ((k2_xboole_0(X4,X4) = X4)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1443,axiom,
% 5.93/1.13      (![X1, X0] : ((k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1442,axiom,
% 5.93/1.13      (![X1, X0] : ((k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),X0))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1441,axiom,
% 5.93/1.13      (![X3, X2] : ((k2_xboole_0(X3,X2) = k2_xboole_0(k2_xboole_0(X3,X2),X2))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1440,axiom,
% 5.93/1.13      (![X3, X2] : ((k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3)))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1439,axiom,
% 5.93/1.13      (![X3, X4] : ((k2_xboole_0(X3,X4) = k2_xboole_0(X4,k2_xboole_0(X3,X4)))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1438,axiom,
% 5.93/1.13      (![X1, X0] : ((k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1437,axiom,
% 5.93/1.13      (![X55, X56] : ((k2_xboole_0(X55,X56) = k5_xboole_0(X55,k4_xboole_0(k2_xboole_0(X55,X56),X55)))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1436,axiom,
% 5.93/1.13      (![X56, X57] : ((k2_xboole_0(X57,X56) = k5_xboole_0(X56,k4_xboole_0(k2_xboole_0(X57,X56),X56)))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1435,axiom,
% 5.93/1.13      (![X1, X0] : ((k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1434,axiom,
% 5.93/1.13      (![X1, X2] : ((k2_xboole_0(X2,k3_xboole_0(X1,X2)) = X2)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1433,axiom,
% 5.93/1.13      (![X2] : ((k2_xboole_0(X2,k1_xboole_0) = X2)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1432,axiom,
% 5.93/1.13      (![X1] : ((k2_xboole_0(k1_xboole_0,X1) = X1)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1431,axiom,
% 5.93/1.13      (![X9, X10] : ((k2_xboole_0(k3_xboole_0(X9,X10),X9) = X9)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1430,axiom,
% 5.93/1.13      (![X11, X12] : ((k2_xboole_0(k3_xboole_0(X12,X11),X11) = X11)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1429,axiom,
% 5.93/1.13      (![X0] : ((k3_xboole_0(X0,X0) = X0)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1428,axiom,
% 5.93/1.13      (![X3, X2] : ((k3_xboole_0(X2,k2_xboole_0(X2,X3)) = X2)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1427,axiom,
% 5.93/1.13      (![X3, X4] : ((k3_xboole_0(X3,k2_xboole_0(X4,X3)) = X3)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1426,axiom,
% 5.93/1.13      (![X1, X0] : ((k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1425,axiom,
% 5.93/1.13      (![X3, X2] : ((k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1424,axiom,
% 5.93/1.13      (![X5, X6] : ((k3_xboole_0(X5,X6) = k3_xboole_0(X5,k3_xboole_0(X5,X6)))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1423,axiom,
% 5.93/1.13      (![X1, X2] : ((k3_xboole_0(X2,X1) = k3_xboole_0(X1,k3_xboole_0(X2,X1)))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1422,axiom,
% 5.93/1.13      (![X3, X4] : ((k3_xboole_0(X4,X3) = k3_xboole_0(k3_xboole_0(X4,X3),X3))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1421,axiom,
% 5.93/1.13      (![X1, X0] : ((k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1420,axiom,
% 5.93/1.13      (![X1, X0] : ((k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1419,axiom,
% 5.93/1.13      (![X44, X43] : ((k3_xboole_0(k2_xboole_0(X43,X44),X43) = X43)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1418,axiom,
% 5.93/1.13      (![X44, X45] : ((k3_xboole_0(k2_xboole_0(X45,X44),X44) = X44)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1417,axiom,
% 5.93/1.13      (![X1] : ((k4_xboole_0(X1,k1_xboole_0) = X1)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1416,negated_conjecture,
% 5.93/1.13      ((~(k4_xboole_0(sK2,sK2) = k4_xboole_0(sK2,u1_struct_0(sK1)))) | (k4_xboole_0(sK2,sK2) = k4_xboole_0(sK2,u1_struct_0(sK1))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1415,axiom,
% 5.93/1.13      (![X3, X2] : ((k4_xboole_0(X2,X3) = k4_xboole_0(X2,k3_xboole_0(X2,X3)))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1414,axiom,
% 5.93/1.13      (![X11, X10] : ((k4_xboole_0(X11,k3_xboole_0(X10,X11)) = k4_xboole_0(X11,X10))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1413,axiom,
% 5.93/1.13      (![X1, X0] : ((k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1412,axiom,
% 5.93/1.13      (![X1, X2] : ((k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1411,axiom,
% 5.93/1.13      (![X0] : ((k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1410,axiom,
% 5.93/1.13      (![X29, X30] : ((k4_xboole_0(k2_xboole_0(X29,X30),X29) = k5_xboole_0(k2_xboole_0(X29,X30),X29))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1409,axiom,
% 5.93/1.13      (![X31, X30] : ((k4_xboole_0(k2_xboole_0(X31,X30),X30) = k5_xboole_0(k2_xboole_0(X31,X30),X30))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1408,axiom,
% 5.93/1.13      (![X5, X6] : ((k4_xboole_0(k3_xboole_0(X5,X6),X5) = k5_xboole_0(k3_xboole_0(X5,X6),k3_xboole_0(X5,X6)))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1407,negated_conjecture,
% 5.93/1.13      ((~(k4_xboole_0(u1_struct_0(sK1),sK2) = k5_xboole_0(u1_struct_0(sK1),sK2))) | (k4_xboole_0(u1_struct_0(sK1),sK2) = k5_xboole_0(u1_struct_0(sK1),sK2)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1406,negated_conjecture,
% 5.93/1.13      ((~r1_tarski(sK2,sK2)) | (![X0] : ((k4_xboole_0(sK2,X0) = k7_subset_1(sK2,sK2,X0)))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1405,axiom,
% 5.93/1.13      (![X1, X0] : ((k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1404,axiom,
% 5.93/1.13      (![X20, X22, X21] : ((k7_subset_1(k2_xboole_0(X20,X21),X20,X22) = k4_xboole_0(X20,X22))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1403,axiom,
% 5.93/1.13      (![X22, X21, X23] : ((k7_subset_1(k2_xboole_0(X22,X21),X21,X23) = k4_xboole_0(X21,X23))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1402,axiom,
% 5.93/1.13      (![X0] : ((k5_xboole_0(X0,k1_xboole_0) = X0)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1401,axiom,
% 5.93/1.13      (![X0] : ((k5_xboole_0(k1_xboole_0,X0) = X0)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1400,axiom,
% 5.93/1.13      (![X1, X0] : ((k5_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1399,axiom,
% 5.93/1.13      (![X7, X6] : ((k5_xboole_0(k3_xboole_0(X6,k2_xboole_0(X6,X7)),k1_xboole_0) = X6)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1398,axiom,
% 5.93/1.13      (![X9, X8] : ((k5_xboole_0(k3_xboole_0(X8,k2_xboole_0(X9,X8)),k1_xboole_0) = X8)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1397,axiom,
% 5.93/1.13      (![X1, X2] : ((k5_xboole_0(k3_xboole_0(X2,X1),k4_xboole_0(X1,X2)) = X1)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1396,negated_conjecture,
% 5.93/1.13      ((~(k5_xboole_0(u1_struct_0(sK1),k4_xboole_0(sK2,sK2)) = k2_xboole_0(sK2,u1_struct_0(sK1)))) | (k5_xboole_0(u1_struct_0(sK1),k4_xboole_0(sK2,sK2)) = k2_xboole_0(sK2,u1_struct_0(sK1))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1395,axiom,
% 5.93/1.13      (![X1, X2] : ((k4_xboole_0(k3_xboole_0(X2,X1),X1) = k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X2,X1)))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1394,axiom,
% 5.93/1.13      (![X0] : ((k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1393,axiom,
% 5.93/1.13      (![X7] : ((k1_xboole_0 = k3_xboole_0(X7,k1_xboole_0))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1392,axiom,
% 5.93/1.13      (![X7] : ((k1_xboole_0 = k4_xboole_0(k1_xboole_0,X7))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1391,axiom,
% 5.93/1.13      (![X3, X2] : ((k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,X3),X2))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1390,axiom,
% 5.93/1.13      (![X3] : ((k1_xboole_0 = k4_xboole_0(X3,X3))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1389,axiom,
% 5.93/1.13      (![X1, X2] : ((k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,X1),X1))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1388,axiom,
% 5.93/1.13      (![X1, X0] : ((k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1387,axiom,
% 5.93/1.13      (![X1, X0] : ((k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0)))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1386,negated_conjecture,
% 5.93/1.13      ((~(k1_xboole_0 = k4_xboole_0(sK2,u1_struct_0(sK1)))) | (k1_xboole_0 = k4_xboole_0(sK2,u1_struct_0(sK1))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1385,axiom,
% 5.93/1.13      (![X28] : ((k1_xboole_0 = k5_xboole_0(X28,X28))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1384,negated_conjecture,
% 5.93/1.13      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1383,negated_conjecture,
% 5.93/1.13      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),sK2,sK2))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),sK2,sK2)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1382,axiom,
% 5.93/1.13      (![X5, X4] : ((k1_xboole_0 = k7_subset_1(X4,k1_xboole_0,X5))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1381,axiom,
% 5.93/1.13      (![X1, X0] : ((k2_tarski(X0,X1) = k2_tarski(X1,X0))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1380,axiom,
% 5.93/1.13      (![X0] : ((k2_subset_1(X0) = X0)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1379,negated_conjecture,
% 5.93/1.13      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK1),sK2,X0) = k4_xboole_0(sK2,X0)))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1378,axiom,
% 5.93/1.13      (![X1, X0, X2] : ((k7_subset_1(X0,k3_xboole_0(X0,X1),X2) = k4_xboole_0(k3_xboole_0(X0,X1),X2))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1377,axiom,
% 5.93/1.13      (![X1, X0, X2] : ((k7_subset_1(X0,k3_xboole_0(X1,X0),X2) = k4_xboole_0(k3_xboole_0(X1,X0),X2))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1376,negated_conjecture,
% 5.93/1.13      ((~(u1_struct_0(sK1) = k2_xboole_0(sK2,u1_struct_0(sK1)))) | (u1_struct_0(sK1) = k2_xboole_0(sK2,u1_struct_0(sK1))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1375,negated_conjecture,
% 5.93/1.13      ((~(u1_struct_0(sK1) = k2_xboole_0(u1_struct_0(sK1),sK2))) | (u1_struct_0(sK1) = k2_xboole_0(u1_struct_0(sK1),sK2)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1374,negated_conjecture,
% 5.93/1.13      ((~(u1_struct_0(sK1) = k5_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK1),sK2)))) | (u1_struct_0(sK1) = k5_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK1),sK2))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1373,negated_conjecture,
% 5.93/1.13      ((~(sK2 = k3_xboole_0(sK2,u1_struct_0(sK1)))) | (sK2 = k3_xboole_0(sK2,u1_struct_0(sK1))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1372,negated_conjecture,
% 5.93/1.13      ((~(sK2 = k3_xboole_0(u1_struct_0(sK1),sK2))) | (sK2 = k3_xboole_0(u1_struct_0(sK1),sK2)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1371,axiom,
% 5.93/1.13      (![X0] : ((~r1_tarski(X0,k1_xboole_0) | (k1_xboole_0 = X0))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1370,axiom,
% 5.93/1.13      (![X1, X3, X2] : ((~r1_tarski(X2,X1) | (k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3)))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1369,axiom,
% 5.93/1.13      (![X1, X0] : ((~r1_tarski(X0,X1) | (k3_xboole_0(X0,X1) = X0))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1368,axiom,
% 5.93/1.13      (![X0] : (r1_tarski(X0,X0)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1367,axiom,
% 5.93/1.13      (![X27, X28] : (r1_tarski(X27,k2_xboole_0(X27,X28))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1366,axiom,
% 5.93/1.13      (![X29, X28] : (r1_tarski(X28,k2_xboole_0(X29,X28))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1365,axiom,
% 5.93/1.13      (![X1, X0] : (r1_tarski(k3_xboole_0(X0,X1),X0)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1364,axiom,
% 5.93/1.13      (![X7, X8] : (r1_tarski(k3_xboole_0(X8,X7),X7)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1363,axiom,
% 5.93/1.13      (![X0] : (r1_tarski(k1_xboole_0,X0)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1362,negated_conjecture,
% 5.93/1.13      ((~r1_tarski(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),k1_xboole_0)) | r1_tarski(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),k1_xboole_0))).
% 5.93/1.13  
% 5.93/1.13  tff(u1361,negated_conjecture,
% 5.93/1.13      ((~r1_tarski(sK2,u1_struct_0(sK1))) | r1_tarski(sK2,u1_struct_0(sK1)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1360,negated_conjecture,
% 5.93/1.13      ((~r1_tarski(sK2,sK2)) | r1_tarski(sK2,sK2))).
% 5.93/1.13  
% 5.93/1.13  tff(u1359,axiom,
% 5.93/1.13      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1358,axiom,
% 5.93/1.13      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1357,axiom,
% 5.93/1.13      (![X1, X0] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1356,axiom,
% 5.93/1.13      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1355,axiom,
% 5.93/1.13      (![X25, X26] : (m1_subset_1(X25,k1_zfmisc_1(k2_xboole_0(X25,X26)))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1354,axiom,
% 5.93/1.13      (![X27, X26] : (m1_subset_1(X26,k1_zfmisc_1(k2_xboole_0(X27,X26)))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1353,axiom,
% 5.93/1.13      (![X1, X0] : (m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1352,axiom,
% 5.93/1.13      (![X5, X6] : (m1_subset_1(k3_xboole_0(X6,X5),k1_zfmisc_1(X5))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1351,axiom,
% 5.93/1.13      (![X2] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1350,negated_conjecture,
% 5.93/1.13      ((~m1_subset_1(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),k1_zfmisc_1(k1_xboole_0))) | m1_subset_1(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),k1_zfmisc_1(k1_xboole_0)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1349,negated_conjecture,
% 5.93/1.13      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1348,axiom,
% 5.93/1.13      (![X1] : (~sP0(k2_struct_0(X1),X1)))).
% 5.93/1.13  
% 5.93/1.13  tff(u1347,axiom,
% 5.93/1.13      (![X1, X0] : ((~sP0(X0,X1) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)))))).
% 5.93/1.13  
% 5.93/1.13  tff(u1346,negated_conjecture,
% 5.93/1.13      ((~sP0(sK2,sK1)) | sP0(sK2,sK1))).
% 5.93/1.13  
% 5.93/1.13  % (27526)# SZS output end Saturation.
% 5.93/1.13  % (27526)------------------------------
% 5.93/1.13  % (27526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.93/1.13  % (27526)Termination reason: Satisfiable
% 5.93/1.13  
% 5.93/1.13  % (27526)Memory used [KB]: 6908
% 5.93/1.13  % (27526)Time elapsed: 0.292 s
% 5.93/1.13  % (27526)------------------------------
% 5.93/1.13  % (27526)------------------------------
% 5.93/1.13  % (27396)Success in time 0.754 s
%------------------------------------------------------------------------------
