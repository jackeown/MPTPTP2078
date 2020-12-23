%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:35 EST 2020

% Result     : CounterSatisfiable 3.86s
% Output     : Saturation 3.86s
% Verified   : 
% Statistics : Number of formulae       :   72 (  72 expanded)
%              Number of leaves         :   72 (  72 expanded)
%              Depth                    :    0
%              Number of atoms          :   89 (  89 expanded)
%              Number of equality atoms :   74 (  74 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u1059,negated_conjecture,
    ( ~ ( sK2 != k2_struct_0(sK1) )
    | sK2 != k2_struct_0(sK1) )).

tff(u1058,axiom,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 )).

tff(u1057,axiom,(
    ! [X3,X2] : k3_xboole_0(X2,k2_xboole_0(X2,X3)) = X2 )).

tff(u1056,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1 )).

tff(u1055,axiom,(
    ! [X11,X10] : k3_xboole_0(k2_xboole_0(X10,X11),X10) = X10 )).

tff(u1054,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 )).

tff(u1053,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u1052,axiom,(
    ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 )).

tff(u1051,axiom,(
    ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,k2_xboole_0(X0,X1)),k1_xboole_0) = X0 )).

tff(u1050,axiom,(
    ! [X20,X21] : k2_xboole_0(k4_xboole_0(X20,X21),k4_xboole_0(X20,k4_xboole_0(X20,X21))) = X20 )).

tff(u1049,axiom,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 )).

tff(u1048,axiom,(
    ! [X1] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0)) = X1 )).

tff(u1047,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u1046,axiom,(
    ! [X3,X4] : k2_xboole_0(k3_xboole_0(X4,X3),k4_xboole_0(X3,X4)) = X3 )).

tff(u1045,axiom,(
    ! [X13,X12] : k3_xboole_0(k2_xboole_0(X13,X12),X12) = X12 )).

tff(u1044,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(k3_xboole_0(X1,X2),X1) )).

tff(u1043,axiom,(
    ! [X3,X2] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) )).

tff(u1042,axiom,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X7,k3_xboole_0(X7,X8)) )).

tff(u1041,axiom,(
    ! [X1,X2] : k3_xboole_0(X2,X1) = k3_xboole_0(X1,k3_xboole_0(X2,X1)) )).

tff(u1040,axiom,(
    ! [X9,X10] : k3_xboole_0(X10,X9) = k3_xboole_0(k3_xboole_0(X10,X9),X9) )).

tff(u1039,axiom,(
    ! [X5,X6] : k4_xboole_0(X5,X6) = k3_xboole_0(k4_xboole_0(X5,X6),X5) )).

tff(u1038,axiom,(
    ! [X3,X2] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3)) )).

tff(u1037,axiom,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2) )).

tff(u1036,axiom,(
    ! [X3] : k1_xboole_0 = k3_xboole_0(X3,k1_xboole_0) )).

tff(u1035,negated_conjecture,
    ( sK2 != k3_xboole_0(sK2,u1_struct_0(sK1))
    | sK2 = k3_xboole_0(sK2,u1_struct_0(sK1)) )).

tff(u1034,negated_conjecture,
    ( sK2 != k3_xboole_0(u1_struct_0(sK1),sK2)
    | sK2 = k3_xboole_0(u1_struct_0(sK1),sK2) )).

tff(u1033,axiom,(
    ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) )).

tff(u1032,axiom,(
    ! [X5,X6] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5)) )).

tff(u1031,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) )).

tff(u1030,axiom,(
    ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0) )).

tff(u1029,axiom,(
    ! [X5,X6] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X6,X5),X5) )).

tff(u1028,axiom,(
    ! [X5,X6] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),X5) )).

tff(u1027,axiom,(
    ! [X4] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X4) )).

tff(u1026,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK2,u1_struct_0(sK1))
    | k1_xboole_0 = k4_xboole_0(sK2,u1_struct_0(sK1)) )).

tff(u1025,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK1),sK2,X0) = k4_xboole_0(sK2,X0) )).

tff(u1024,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) )).

tff(u1023,axiom,(
    ! [X18,X19] : k4_xboole_0(X19,k3_xboole_0(X18,X19)) = k4_xboole_0(X19,X18) )).

tff(u1022,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) )).

tff(u1021,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) )).

tff(u1020,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) )).

tff(u1019,axiom,(
    ! [X18,X19] : k4_xboole_0(X18,k4_xboole_0(X18,X19)) = k5_xboole_0(X18,k4_xboole_0(X18,X19)) )).

tff(u1018,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) )).

tff(u1017,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(sK1),sK2) != k5_xboole_0(u1_struct_0(sK1),sK2)
    | k4_xboole_0(u1_struct_0(sK1),sK2) = k5_xboole_0(u1_struct_0(sK1),sK2) )).

tff(u1016,axiom,(
    ! [X9,X8] : k4_xboole_0(k2_xboole_0(X8,X9),X8) = k5_xboole_0(k2_xboole_0(X8,X9),X8) )).

tff(u1015,axiom,(
    ! [X11,X10] : k4_xboole_0(k2_xboole_0(X11,X10),X10) = k5_xboole_0(k2_xboole_0(X11,X10),X10) )).

tff(u1014,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X0),k1_xboole_0) )).

tff(u1013,axiom,(
    ! [X7,X8] : k3_xboole_0(X8,X7) = k2_xboole_0(k3_xboole_0(X7,k3_xboole_0(X8,X7)),k1_xboole_0) )).

tff(u1012,axiom,(
    ! [X9,X10] : k3_xboole_0(X9,X10) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X9,k3_xboole_0(X9,X10))) )).

tff(u1011,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) )).

tff(u1010,axiom,(
    ! [X3,X2] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) )).

tff(u1009,axiom,(
    ! [X11,X10] : k2_xboole_0(X11,X10) = k2_xboole_0(X10,k4_xboole_0(k2_xboole_0(X11,X10),X10)) )).

tff(u1008,axiom,(
    ! [X9,X8] : k2_xboole_0(X8,X9) = k2_xboole_0(X8,k4_xboole_0(k2_xboole_0(X8,X9),X8)) )).

tff(u1007,negated_conjecture,
    ( u1_struct_0(sK1) != k2_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK1),sK2))
    | u1_struct_0(sK1) = k2_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK1),sK2)) )).

tff(u1006,negated_conjecture,
    ( sK2 != k2_xboole_0(sK2,k4_xboole_0(sK2,u1_struct_0(sK1)))
    | sK2 = k2_xboole_0(sK2,k4_xboole_0(sK2,u1_struct_0(sK1))) )).

tff(u1005,axiom,(
    ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

tff(u1004,axiom,(
    ! [X1,X0] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) )).

tff(u1003,axiom,(
    ! [X1,X0] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0)) )).

tff(u1002,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK1),sK2,sK2)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),sK2,sK2) )).

tff(u1001,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2) )).

tff(u1000,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) )).

tff(u999,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) )).

tff(u998,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) )).

tff(u997,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) )).

tff(u996,negated_conjecture,
    ( ~ r1_tarski(sK2,u1_struct_0(sK1))
    | r1_tarski(sK2,u1_struct_0(sK1)) )).

tff(u995,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u994,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) )).

tff(u993,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) )).

tff(u992,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) )).

tff(u991,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u990,axiom,(
    ! [X1] : ~ sP0(k2_struct_0(X1),X1) )).

tff(u989,axiom,(
    ! [X1,X0] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0) ) )).

tff(u988,negated_conjecture,
    ( ~ sP0(sK2,sK1)
    | sP0(sK2,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:50:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (32701)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (32697)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (32697)Refutation not found, incomplete strategy% (32697)------------------------------
% 0.21/0.50  % (32697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (32697)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (32697)Memory used [KB]: 6140
% 0.21/0.50  % (32697)Time elapsed: 0.102 s
% 0.21/0.50  % (32697)------------------------------
% 0.21/0.50  % (32697)------------------------------
% 0.21/0.51  % (32701)Refutation not found, incomplete strategy% (32701)------------------------------
% 0.21/0.51  % (32701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32694)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (32705)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (32693)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (32693)Refutation not found, incomplete strategy% (32693)------------------------------
% 0.21/0.51  % (32693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32693)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (32693)Memory used [KB]: 1663
% 0.21/0.51  % (32693)Time elapsed: 0.106 s
% 0.21/0.51  % (32693)------------------------------
% 0.21/0.51  % (32693)------------------------------
% 0.21/0.51  % (32703)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (32703)Refutation not found, incomplete strategy% (32703)------------------------------
% 0.21/0.51  % (32703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32703)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (32703)Memory used [KB]: 10618
% 0.21/0.51  % (32703)Time elapsed: 0.106 s
% 0.21/0.51  % (32703)------------------------------
% 0.21/0.51  % (32703)------------------------------
% 0.21/0.51  % (32709)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (32715)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (32704)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (32699)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (32704)Refutation not found, incomplete strategy% (32704)------------------------------
% 0.21/0.52  % (32704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (32704)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (32704)Memory used [KB]: 10618
% 0.21/0.52  % (32704)Time elapsed: 0.121 s
% 0.21/0.52  % (32704)------------------------------
% 0.21/0.52  % (32704)------------------------------
% 0.21/0.52  % (32707)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (32717)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (32701)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (32701)Memory used [KB]: 10746
% 0.21/0.52  % (32701)Time elapsed: 0.096 s
% 0.21/0.52  % (32701)------------------------------
% 0.21/0.52  % (32701)------------------------------
% 0.21/0.52  % (32695)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (32711)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (32695)Refutation not found, incomplete strategy% (32695)------------------------------
% 0.21/0.52  % (32695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (32695)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (32695)Memory used [KB]: 10746
% 0.21/0.52  % (32695)Time elapsed: 0.120 s
% 0.21/0.52  % (32695)------------------------------
% 0.21/0.52  % (32695)------------------------------
% 0.21/0.52  % (32698)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (32722)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (32698)Refutation not found, incomplete strategy% (32698)------------------------------
% 0.21/0.52  % (32698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (32698)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (32698)Memory used [KB]: 6268
% 0.21/0.52  % (32698)Time elapsed: 0.118 s
% 0.21/0.52  % (32698)------------------------------
% 0.21/0.52  % (32698)------------------------------
% 0.21/0.52  % (32712)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (32710)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (32716)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (32715)Refutation not found, incomplete strategy% (32715)------------------------------
% 0.21/0.53  % (32715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (32715)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (32715)Memory used [KB]: 10746
% 0.21/0.53  % (32715)Time elapsed: 0.091 s
% 0.21/0.53  % (32715)------------------------------
% 0.21/0.53  % (32715)------------------------------
% 0.21/0.53  % (32696)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (32716)Refutation not found, incomplete strategy% (32716)------------------------------
% 0.21/0.53  % (32716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (32716)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (32716)Memory used [KB]: 1791
% 0.21/0.53  % (32716)Time elapsed: 0.130 s
% 0.21/0.53  % (32716)------------------------------
% 0.21/0.53  % (32716)------------------------------
% 0.21/0.53  % (32706)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (32718)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (32700)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (32708)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (32708)Refutation not found, incomplete strategy% (32708)------------------------------
% 0.21/0.53  % (32708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (32708)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (32708)Memory used [KB]: 6140
% 0.21/0.53  % (32714)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (32708)Time elapsed: 0.001 s
% 0.21/0.53  % (32708)------------------------------
% 0.21/0.53  % (32708)------------------------------
% 0.21/0.53  % (32721)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (32714)Refutation not found, incomplete strategy% (32714)------------------------------
% 0.21/0.54  % (32714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (32714)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (32714)Memory used [KB]: 1791
% 0.21/0.54  % (32714)Time elapsed: 0.131 s
% 0.21/0.54  % (32714)------------------------------
% 0.21/0.54  % (32714)------------------------------
% 0.21/0.54  % (32720)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (32713)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (32719)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (32713)Refutation not found, incomplete strategy% (32713)------------------------------
% 0.21/0.54  % (32713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (32713)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (32713)Memory used [KB]: 10746
% 0.21/0.54  % (32713)Time elapsed: 0.142 s
% 0.21/0.54  % (32713)------------------------------
% 0.21/0.54  % (32713)------------------------------
% 1.51/0.55  % (32702)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.51/0.55  % (32702)Refutation not found, incomplete strategy% (32702)------------------------------
% 1.51/0.55  % (32702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.55  % (32702)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.55  
% 1.51/0.55  % (32702)Memory used [KB]: 10618
% 1.51/0.55  % (32702)Time elapsed: 0.148 s
% 1.51/0.55  % (32702)------------------------------
% 1.51/0.55  % (32702)------------------------------
% 1.51/0.55  % (32710)Refutation not found, incomplete strategy% (32710)------------------------------
% 1.51/0.55  % (32710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.55  % (32710)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.55  
% 1.51/0.55  % (32710)Memory used [KB]: 10618
% 1.51/0.55  % (32710)Time elapsed: 0.148 s
% 1.51/0.55  % (32710)------------------------------
% 1.51/0.55  % (32710)------------------------------
% 1.51/0.55  % (32718)Refutation not found, incomplete strategy% (32718)------------------------------
% 1.51/0.55  % (32718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.55  % (32718)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.55  
% 1.51/0.55  % (32718)Memory used [KB]: 6396
% 1.51/0.55  % (32718)Time elapsed: 0.133 s
% 1.51/0.55  % (32718)------------------------------
% 1.51/0.55  % (32718)------------------------------
% 1.59/0.56  % (32719)Refutation not found, incomplete strategy% (32719)------------------------------
% 1.59/0.56  % (32719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.56  % (32719)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.56  
% 1.59/0.56  % (32719)Memory used [KB]: 10874
% 1.59/0.56  % (32719)Time elapsed: 0.141 s
% 1.59/0.56  % (32719)------------------------------
% 1.59/0.56  % (32719)------------------------------
% 1.59/0.57  % (32700)Refutation not found, incomplete strategy% (32700)------------------------------
% 1.59/0.57  % (32700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.57  % (32700)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.57  
% 1.59/0.57  % (32700)Memory used [KB]: 6524
% 1.59/0.57  % (32700)Time elapsed: 0.171 s
% 1.59/0.57  % (32700)------------------------------
% 1.59/0.57  % (32700)------------------------------
% 2.02/0.64  % (32724)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.02/0.64  % (32725)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.02/0.64  % (32728)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.02/0.65  % (32733)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 2.02/0.65  % (32727)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.02/0.65  % (32694)Refutation not found, incomplete strategy% (32694)------------------------------
% 2.02/0.65  % (32694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.65  % (32694)Termination reason: Refutation not found, incomplete strategy
% 2.02/0.65  
% 2.02/0.65  % (32694)Memory used [KB]: 6268
% 2.02/0.65  % (32694)Time elapsed: 0.221 s
% 2.02/0.65  % (32694)------------------------------
% 2.02/0.65  % (32694)------------------------------
% 2.02/0.65  % (32727)Refutation not found, incomplete strategy% (32727)------------------------------
% 2.02/0.65  % (32727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.65  % (32727)Termination reason: Refutation not found, incomplete strategy
% 2.02/0.65  
% 2.02/0.65  % (32727)Memory used [KB]: 10746
% 2.02/0.65  % (32727)Time elapsed: 0.102 s
% 2.02/0.65  % (32727)------------------------------
% 2.02/0.65  % (32727)------------------------------
% 2.02/0.66  % (32734)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 2.02/0.66  % (32731)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.02/0.66  % (32731)Refutation not found, incomplete strategy% (32731)------------------------------
% 2.02/0.66  % (32731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.66  % (32731)Termination reason: Refutation not found, incomplete strategy
% 2.02/0.66  
% 2.02/0.66  % (32731)Memory used [KB]: 1791
% 2.02/0.66  % (32731)Time elapsed: 0.105 s
% 2.02/0.66  % (32731)------------------------------
% 2.02/0.66  % (32731)------------------------------
% 2.02/0.66  % (32730)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.02/0.66  % (32732)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.30/0.66  % (32733)Refutation not found, incomplete strategy% (32733)------------------------------
% 2.30/0.66  % (32733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.30/0.66  % (32733)Termination reason: Refutation not found, incomplete strategy
% 2.30/0.66  
% 2.30/0.66  % (32733)Memory used [KB]: 6396
% 2.30/0.66  % (32733)Time elapsed: 0.091 s
% 2.30/0.66  % (32733)------------------------------
% 2.30/0.66  % (32733)------------------------------
% 2.30/0.67  % (32723)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.30/0.67  % (32723)Refutation not found, incomplete strategy% (32723)------------------------------
% 2.30/0.67  % (32723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.30/0.67  % (32723)Termination reason: Refutation not found, incomplete strategy
% 2.30/0.67  
% 2.30/0.67  % (32723)Memory used [KB]: 6140
% 2.30/0.67  % (32723)Time elapsed: 0.129 s
% 2.30/0.67  % (32723)------------------------------
% 2.30/0.67  % (32723)------------------------------
% 2.30/0.67  % (32726)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.30/0.68  % (32729)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.30/0.68  % (32736)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 2.30/0.68  % (32736)Refutation not found, incomplete strategy% (32736)------------------------------
% 2.30/0.68  % (32736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.30/0.68  % (32736)Termination reason: Refutation not found, incomplete strategy
% 2.30/0.68  
% 2.30/0.68  % (32736)Memory used [KB]: 1663
% 2.30/0.68  % (32736)Time elapsed: 0.106 s
% 2.30/0.68  % (32736)------------------------------
% 2.30/0.68  % (32736)------------------------------
% 2.30/0.68  % (32735)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 2.30/0.69  % (32737)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 2.30/0.71  % (32739)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 2.30/0.72  % (32725)Refutation not found, incomplete strategy% (32725)------------------------------
% 2.30/0.72  % (32725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.30/0.72  % (32725)Termination reason: Refutation not found, incomplete strategy
% 2.30/0.72  
% 2.30/0.72  % (32725)Memory used [KB]: 6780
% 2.30/0.72  % (32725)Time elapsed: 0.177 s
% 2.30/0.72  % (32725)------------------------------
% 2.30/0.72  % (32725)------------------------------
% 2.30/0.73  % (32738)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 2.70/0.74  % (32729)Refutation not found, incomplete strategy% (32729)------------------------------
% 2.70/0.74  % (32729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.70/0.74  % (32729)Termination reason: Refutation not found, incomplete strategy
% 2.70/0.74  
% 2.70/0.74  % (32729)Memory used [KB]: 2174
% 2.70/0.74  % (32729)Time elapsed: 0.188 s
% 2.70/0.74  % (32729)------------------------------
% 2.70/0.74  % (32729)------------------------------
% 2.70/0.75  % (32740)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 2.87/0.77  % (32740)Refutation not found, incomplete strategy% (32740)------------------------------
% 2.87/0.77  % (32740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.87/0.77  % (32740)Termination reason: Refutation not found, incomplete strategy
% 2.87/0.77  
% 2.87/0.77  % (32740)Memory used [KB]: 6268
% 2.87/0.77  % (32740)Time elapsed: 0.098 s
% 2.87/0.77  % (32740)------------------------------
% 2.87/0.77  % (32740)------------------------------
% 2.87/0.77  % (32743)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 2.87/0.80  % (32724)Refutation not found, incomplete strategy% (32724)------------------------------
% 2.87/0.80  % (32724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.87/0.80  % (32724)Termination reason: Refutation not found, incomplete strategy
% 2.87/0.80  
% 2.87/0.80  % (32724)Memory used [KB]: 6268
% 2.87/0.80  % (32724)Time elapsed: 0.255 s
% 2.87/0.80  % (32724)------------------------------
% 2.87/0.80  % (32724)------------------------------
% 2.87/0.81  % (32745)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 2.87/0.81  % (32742)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 2.87/0.82  % (32741)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 2.87/0.82  % (32744)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 3.18/0.85  % (32746)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 3.18/0.86  % (32735)Refutation not found, incomplete strategy% (32735)------------------------------
% 3.18/0.86  % (32735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.18/0.86  % (32735)Termination reason: Refutation not found, incomplete strategy
% 3.18/0.86  
% 3.18/0.86  % (32735)Memory used [KB]: 1791
% 3.18/0.86  % (32735)Time elapsed: 0.288 s
% 3.18/0.86  % (32735)------------------------------
% 3.18/0.86  % (32735)------------------------------
% 3.37/0.87  % (32748)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 3.37/0.89  % (32748)Refutation not found, incomplete strategy% (32748)------------------------------
% 3.37/0.89  % (32748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.37/0.89  % (32748)Termination reason: Refutation not found, incomplete strategy
% 3.37/0.89  
% 3.37/0.89  % (32748)Memory used [KB]: 6140
% 3.37/0.89  % (32748)Time elapsed: 0.076 s
% 3.37/0.89  % (32748)------------------------------
% 3.37/0.89  % (32748)------------------------------
% 3.37/0.90  % (32747)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 3.37/0.91  % (32705)Time limit reached!
% 3.37/0.91  % (32705)------------------------------
% 3.37/0.91  % (32705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.37/0.91  % (32705)Termination reason: Time limit
% 3.37/0.91  
% 3.37/0.91  % (32705)Memory used [KB]: 10490
% 3.37/0.91  % (32705)Time elapsed: 0.506 s
% 3.37/0.91  % (32705)------------------------------
% 3.37/0.91  % (32705)------------------------------
% 3.69/0.95  % (32726)Time limit reached!
% 3.69/0.95  % (32726)------------------------------
% 3.69/0.95  % (32726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.69/0.95  % (32726)Termination reason: Time limit
% 3.69/0.95  
% 3.69/0.95  % (32726)Memory used [KB]: 6780
% 3.69/0.95  % (32726)Time elapsed: 0.404 s
% 3.69/0.95  % (32726)------------------------------
% 3.69/0.95  % (32726)------------------------------
% 3.69/0.96  % (32749)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 3.69/0.96  % (32749)Refutation not found, incomplete strategy% (32749)------------------------------
% 3.69/0.96  % (32749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.69/0.96  % (32749)Termination reason: Refutation not found, incomplete strategy
% 3.69/0.96  
% 3.69/0.96  % (32749)Memory used [KB]: 6140
% 3.69/0.96  % (32749)Time elapsed: 0.104 s
% 3.69/0.96  % (32749)------------------------------
% 3.69/0.96  % (32749)------------------------------
% 3.86/0.99  % (32746)Refutation not found, incomplete strategy% (32746)------------------------------
% 3.86/0.99  % (32746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.86/0.99  % (32746)Termination reason: Refutation not found, incomplete strategy
% 3.86/0.99  
% 3.86/0.99  % (32746)Memory used [KB]: 6140
% 3.86/0.99  % (32746)Time elapsed: 0.230 s
% 3.86/0.99  % (32746)------------------------------
% 3.86/0.99  % (32746)------------------------------
% 3.86/0.99  % (32750)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 3.86/1.00  % (32721)Time limit reached!
% 3.86/1.00  % (32721)------------------------------
% 3.86/1.00  % (32721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.86/1.00  % (32721)Termination reason: Time limit
% 3.86/1.00  % (32721)Termination phase: Saturation
% 3.86/1.00  
% 3.86/1.00  % (32721)Memory used [KB]: 8443
% 3.86/1.00  % (32721)Time elapsed: 0.601 s
% 3.86/1.00  % (32721)------------------------------
% 3.86/1.00  % (32721)------------------------------
% 3.86/1.00  % (32750)Refutation not found, incomplete strategy% (32750)------------------------------
% 3.86/1.00  % (32750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.86/1.00  % (32750)Termination reason: Refutation not found, incomplete strategy
% 3.86/1.00  
% 3.86/1.00  % (32750)Memory used [KB]: 10746
% 3.86/1.00  % (32750)Time elapsed: 0.109 s
% 3.86/1.00  % (32750)------------------------------
% 3.86/1.00  % (32750)------------------------------
% 3.86/1.00  % (32739)Time limit reached!
% 3.86/1.00  % (32739)------------------------------
% 3.86/1.00  % (32739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.86/1.00  % (32739)Termination reason: Time limit
% 3.86/1.00  % (32739)Termination phase: Saturation
% 3.86/1.00  
% 3.86/1.00  % (32739)Memory used [KB]: 4989
% 3.86/1.00  % (32739)Time elapsed: 0.400 s
% 3.86/1.00  % (32739)------------------------------
% 3.86/1.00  % (32739)------------------------------
% 3.86/1.01  % (32709)Time limit reached!
% 3.86/1.01  % (32709)------------------------------
% 3.86/1.01  % (32709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.86/1.01  % (32709)Termination reason: Time limit
% 3.86/1.01  % (32709)Termination phase: Saturation
% 3.86/1.01  
% 3.86/1.01  % (32709)Memory used [KB]: 16886
% 3.86/1.01  % (32709)Time elapsed: 0.602 s
% 3.86/1.01  % (32709)------------------------------
% 3.86/1.01  % (32709)------------------------------
% 3.86/1.02  % SZS status CounterSatisfiable for theBenchmark
% 3.86/1.02  % (32741)# SZS output start Saturation.
% 3.86/1.02  tff(u1059,negated_conjecture,
% 3.86/1.02      ((~(sK2 != k2_struct_0(sK1))) | (sK2 != k2_struct_0(sK1)))).
% 3.86/1.02  
% 3.86/1.02  tff(u1058,axiom,
% 3.86/1.02      (![X0] : ((k3_xboole_0(X0,X0) = X0)))).
% 3.86/1.02  
% 3.86/1.02  tff(u1057,axiom,
% 3.86/1.02      (![X3, X2] : ((k3_xboole_0(X2,k2_xboole_0(X2,X3)) = X2)))).
% 3.86/1.02  
% 3.86/1.02  tff(u1056,axiom,
% 3.86/1.02      (![X1, X2] : ((k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1)))).
% 3.86/1.02  
% 3.86/1.02  tff(u1055,axiom,
% 3.86/1.02      (![X11, X10] : ((k3_xboole_0(k2_xboole_0(X10,X11),X10) = X10)))).
% 3.86/1.02  
% 3.86/1.02  tff(u1054,axiom,
% 3.86/1.02      (![X1] : ((k4_xboole_0(X1,k1_xboole_0) = X1)))).
% 3.86/1.02  
% 3.86/1.02  tff(u1053,axiom,
% 3.86/1.02      (![X0] : ((k2_xboole_0(X0,k1_xboole_0) = X0)))).
% 3.86/1.02  
% 3.86/1.02  tff(u1052,axiom,
% 3.86/1.02      (![X1, X0] : ((k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0)))).
% 3.86/1.02  
% 3.86/1.02  tff(u1051,axiom,
% 3.86/1.02      (![X1, X0] : ((k2_xboole_0(k3_xboole_0(X0,k2_xboole_0(X0,X1)),k1_xboole_0) = X0)))).
% 3.86/1.02  
% 3.86/1.02  tff(u1050,axiom,
% 3.86/1.02      (![X20, X21] : ((k2_xboole_0(k4_xboole_0(X20,X21),k4_xboole_0(X20,k4_xboole_0(X20,X21))) = X20)))).
% 3.86/1.02  
% 3.86/1.02  tff(u1049,axiom,
% 3.86/1.02      (![X0] : ((k2_xboole_0(k1_xboole_0,X0) = X0)))).
% 3.86/1.02  
% 3.86/1.02  tff(u1048,axiom,
% 3.86/1.02      (![X1] : ((k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0)) = X1)))).
% 3.86/1.02  
% 3.86/1.02  tff(u1047,axiom,
% 3.86/1.02      (![X0] : ((k2_subset_1(X0) = X0)))).
% 3.86/1.02  
% 3.86/1.02  tff(u1046,axiom,
% 3.86/1.02      (![X3, X4] : ((k2_xboole_0(k3_xboole_0(X4,X3),k4_xboole_0(X3,X4)) = X3)))).
% 3.86/1.02  
% 3.86/1.02  tff(u1045,axiom,
% 3.86/1.02      (![X13, X12] : ((k3_xboole_0(k2_xboole_0(X13,X12),X12) = X12)))).
% 3.86/1.02  
% 3.86/1.02  tff(u1044,axiom,
% 3.86/1.02      (![X1, X2] : ((k3_xboole_0(X1,X2) = k3_xboole_0(k3_xboole_0(X1,X2),X1))))).
% 3.86/1.02  
% 3.86/1.02  tff(u1043,axiom,
% 3.86/1.02      (![X3, X2] : ((k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2))))).
% 3.86/1.02  
% 3.86/1.02  tff(u1042,axiom,
% 3.86/1.02      (![X7, X8] : ((k3_xboole_0(X7,X8) = k3_xboole_0(X7,k3_xboole_0(X7,X8)))))).
% 3.86/1.02  
% 3.86/1.02  tff(u1041,axiom,
% 3.86/1.02      (![X1, X2] : ((k3_xboole_0(X2,X1) = k3_xboole_0(X1,k3_xboole_0(X2,X1)))))).
% 3.86/1.02  
% 3.86/1.02  tff(u1040,axiom,
% 3.86/1.02      (![X9, X10] : ((k3_xboole_0(X10,X9) = k3_xboole_0(k3_xboole_0(X10,X9),X9))))).
% 3.86/1.02  
% 3.86/1.02  tff(u1039,axiom,
% 3.86/1.02      (![X5, X6] : ((k4_xboole_0(X5,X6) = k3_xboole_0(k4_xboole_0(X5,X6),X5))))).
% 3.86/1.02  
% 3.86/1.02  tff(u1038,axiom,
% 3.86/1.02      (![X3, X2] : ((k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3)))))).
% 3.86/1.02  
% 3.86/1.02  tff(u1037,axiom,
% 3.86/1.02      (![X2] : ((k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2))))).
% 3.86/1.02  
% 3.86/1.02  tff(u1036,axiom,
% 3.86/1.02      (![X3] : ((k1_xboole_0 = k3_xboole_0(X3,k1_xboole_0))))).
% 3.86/1.02  
% 3.86/1.02  tff(u1035,negated_conjecture,
% 3.86/1.02      ((~(sK2 = k3_xboole_0(sK2,u1_struct_0(sK1)))) | (sK2 = k3_xboole_0(sK2,u1_struct_0(sK1))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1034,negated_conjecture,
% 3.86/1.03      ((~(sK2 = k3_xboole_0(u1_struct_0(sK1),sK2))) | (sK2 = k3_xboole_0(u1_struct_0(sK1),sK2)))).
% 3.86/1.03  
% 3.86/1.03  tff(u1033,axiom,
% 3.86/1.03      (![X1, X0] : ((k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1032,axiom,
% 3.86/1.03      (![X5, X6] : ((k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5)))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1031,axiom,
% 3.86/1.03      (![X0] : ((k1_xboole_0 = k4_xboole_0(X0,X0))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1030,axiom,
% 3.86/1.03      (![X1, X0] : ((k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1029,axiom,
% 3.86/1.03      (![X5, X6] : ((k1_xboole_0 = k4_xboole_0(k3_xboole_0(X6,X5),X5))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1028,axiom,
% 3.86/1.03      (![X5, X6] : ((k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),X5))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1027,axiom,
% 3.86/1.03      (![X4] : ((k1_xboole_0 = k4_xboole_0(k1_xboole_0,X4))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1026,negated_conjecture,
% 3.86/1.03      ((~(k1_xboole_0 = k4_xboole_0(sK2,u1_struct_0(sK1)))) | (k1_xboole_0 = k4_xboole_0(sK2,u1_struct_0(sK1))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1025,negated_conjecture,
% 3.86/1.03      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK1),sK2,X0) = k4_xboole_0(sK2,X0)))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1024,axiom,
% 3.86/1.03      (![X1, X0] : ((k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1023,axiom,
% 3.86/1.03      (![X18, X19] : ((k4_xboole_0(X19,k3_xboole_0(X18,X19)) = k4_xboole_0(X19,X18))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1022,axiom,
% 3.86/1.03      (![X1, X0] : ((k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1021,axiom,
% 3.86/1.03      (![X1, X2] : ((k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1020,axiom,
% 3.86/1.03      (![X0] : ((k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1019,axiom,
% 3.86/1.03      (![X18, X19] : ((k4_xboole_0(X18,k4_xboole_0(X18,X19)) = k5_xboole_0(X18,k4_xboole_0(X18,X19)))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1018,axiom,
% 3.86/1.03      (![X0] : ((k1_xboole_0 = k5_xboole_0(X0,X0))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1017,negated_conjecture,
% 3.86/1.03      ((~(k4_xboole_0(u1_struct_0(sK1),sK2) = k5_xboole_0(u1_struct_0(sK1),sK2))) | (k4_xboole_0(u1_struct_0(sK1),sK2) = k5_xboole_0(u1_struct_0(sK1),sK2)))).
% 3.86/1.03  
% 3.86/1.03  tff(u1016,axiom,
% 3.86/1.03      (![X9, X8] : ((k4_xboole_0(k2_xboole_0(X8,X9),X8) = k5_xboole_0(k2_xboole_0(X8,X9),X8))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1015,axiom,
% 3.86/1.03      (![X11, X10] : ((k4_xboole_0(k2_xboole_0(X11,X10),X10) = k5_xboole_0(k2_xboole_0(X11,X10),X10))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1014,axiom,
% 3.86/1.03      (![X1, X0] : ((k3_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X0),k1_xboole_0))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1013,axiom,
% 3.86/1.03      (![X7, X8] : ((k3_xboole_0(X8,X7) = k2_xboole_0(k3_xboole_0(X7,k3_xboole_0(X8,X7)),k1_xboole_0))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1012,axiom,
% 3.86/1.03      (![X9, X10] : ((k3_xboole_0(X9,X10) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X9,k3_xboole_0(X9,X10))))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1011,axiom,
% 3.86/1.03      (![X1, X0] : ((k4_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1010,axiom,
% 3.86/1.03      (![X3, X2] : ((k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1009,axiom,
% 3.86/1.03      (![X11, X10] : ((k2_xboole_0(X11,X10) = k2_xboole_0(X10,k4_xboole_0(k2_xboole_0(X11,X10),X10)))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1008,axiom,
% 3.86/1.03      (![X9, X8] : ((k2_xboole_0(X8,X9) = k2_xboole_0(X8,k4_xboole_0(k2_xboole_0(X8,X9),X8)))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1007,negated_conjecture,
% 3.86/1.03      ((~(u1_struct_0(sK1) = k2_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK1),sK2)))) | (u1_struct_0(sK1) = k2_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK1),sK2))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1006,negated_conjecture,
% 3.86/1.03      ((~(sK2 = k2_xboole_0(sK2,k4_xboole_0(sK2,u1_struct_0(sK1))))) | (sK2 = k2_xboole_0(sK2,k4_xboole_0(sK2,u1_struct_0(sK1)))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1005,axiom,
% 3.86/1.03      (![X1, X0] : ((k2_tarski(X0,X1) = k2_tarski(X1,X0))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1004,axiom,
% 3.86/1.03      (![X1, X0] : ((k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1003,axiom,
% 3.86/1.03      (![X1, X0] : ((k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0)))))).
% 3.86/1.03  
% 3.86/1.03  tff(u1002,negated_conjecture,
% 3.86/1.03      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),sK2,sK2))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),sK2,sK2)))).
% 3.86/1.03  
% 3.86/1.03  tff(u1001,negated_conjecture,
% 3.86/1.03      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2)))).
% 3.86/1.03  
% 3.86/1.03  tff(u1000,axiom,
% 3.86/1.03      (![X1, X0] : ((k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1))))).
% 3.86/1.03  
% 3.86/1.03  tff(u999,axiom,
% 3.86/1.03      (![X1, X0] : ((k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)))))).
% 3.86/1.03  
% 3.86/1.03  tff(u998,axiom,
% 3.86/1.03      (![X1, X0] : ((k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)))))).
% 3.86/1.03  
% 3.86/1.03  tff(u997,axiom,
% 3.86/1.03      (![X1, X0] : ((~r1_tarski(X0,X1) | (k3_xboole_0(X0,X1) = X0))))).
% 3.86/1.03  
% 3.86/1.03  tff(u996,negated_conjecture,
% 3.86/1.03      ((~r1_tarski(sK2,u1_struct_0(sK1))) | r1_tarski(sK2,u1_struct_0(sK1)))).
% 3.86/1.03  
% 3.86/1.03  tff(u995,axiom,
% 3.86/1.03      (![X0] : (r1_tarski(X0,X0)))).
% 3.86/1.03  
% 3.86/1.03  tff(u994,axiom,
% 3.86/1.03      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))).
% 3.86/1.03  
% 3.86/1.03  tff(u993,axiom,
% 3.86/1.03      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)))))).
% 3.86/1.03  
% 3.86/1.03  tff(u992,negated_conjecture,
% 3.86/1.03      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))))).
% 3.86/1.03  
% 3.86/1.03  tff(u991,axiom,
% 3.86/1.03      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 3.86/1.03  
% 3.86/1.03  tff(u990,axiom,
% 3.86/1.03      (![X1] : (~sP0(k2_struct_0(X1),X1)))).
% 3.86/1.03  
% 3.86/1.03  tff(u989,axiom,
% 3.86/1.03      (![X1, X0] : ((~sP0(X0,X1) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)))))).
% 3.86/1.03  
% 3.86/1.03  tff(u988,negated_conjecture,
% 3.86/1.03      ((~sP0(sK2,sK1)) | sP0(sK2,sK1))).
% 3.86/1.03  
% 3.86/1.03  % (32741)# SZS output end Saturation.
% 3.86/1.03  % (32741)------------------------------
% 3.86/1.03  % (32741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.86/1.03  % (32741)Termination reason: Satisfiable
% 3.86/1.03  
% 3.86/1.03  % (32741)Memory used [KB]: 6652
% 3.86/1.03  % (32741)Time elapsed: 0.320 s
% 3.86/1.03  % (32741)------------------------------
% 3.86/1.03  % (32741)------------------------------
% 3.86/1.03  % (32692)Success in time 0.677 s
%------------------------------------------------------------------------------
