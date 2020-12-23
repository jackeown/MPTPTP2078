%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:44 EST 2020

% Result     : CounterSatisfiable 1.38s
% Output     : Saturation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   51 (  51 expanded)
%              Number of leaves         :   51 (  51 expanded)
%              Depth                    :    0
%              Number of atoms          :   82 (  82 expanded)
%              Number of equality atoms :   63 (  63 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u358,negated_conjecture,
    ( ~ ( sK1 != k2_struct_0(sK0) )
    | sK1 != k2_struct_0(sK0) )).

tff(u357,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 )).

tff(u356,axiom,(
    ! [X3,X4] : k7_subset_1(X3,X3,X4) = k5_xboole_0(X3,k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) )).

tff(u355,axiom,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) )).

tff(u354,axiom,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k7_subset_1(X0,X0,k1_xboole_0)) )).

tff(u353,axiom,(
    ! [X0] : k1_xboole_0 = k7_subset_1(X0,k1_xboole_0,k1_xboole_0) )).

tff(u352,axiom,(
    ! [X0] : k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

tff(u351,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

tff(u350,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u349,axiom,(
    ! [X0] : k1_xboole_0 = k4_subset_1(X0,k1_xboole_0,k1_xboole_0) )).

tff(u348,axiom,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 )).

tff(u347,axiom,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 )).

tff(u346,axiom,(
    ! [X1,X0] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )).

tff(u345,axiom,(
    ! [X1,X0] : k3_tarski(k2_enumset1(X0,X0,X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) = k3_tarski(k2_enumset1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k1_setfam_1(k2_enumset1(X0,X0,X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))))) )).

tff(u344,axiom,(
    ! [X0] : k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 )).

tff(u343,axiom,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 )).

tff(u342,axiom,(
    ! [X1] : k3_subset_1(X1,k7_subset_1(X1,k1_xboole_0,X1)) = X1 )).

tff(u341,axiom,(
    ! [X1,X0] : k3_subset_1(X0,k7_subset_1(X1,k1_xboole_0,X0)) = X0 )).

tff(u340,axiom,(
    ! [X1] : k4_subset_1(X1,k1_xboole_0,X1) = X1 )).

tff(u339,axiom,(
    ! [X1] : k4_subset_1(X1,X1,X1) = X1 )).

tff(u338,axiom,(
    ! [X0] : k4_subset_1(X0,X0,k1_xboole_0) = X0 )).

tff(u337,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) != k3_tarski(k2_enumset1(sK1,sK1,sK1,u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,u1_struct_0(sK0))) )).

tff(u336,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) != k3_tarski(k2_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1))
    | k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1)) )).

tff(u335,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) != k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1))
    | k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)) )).

tff(u334,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) != k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1))
    | ! [X0] : k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(X0,k1_xboole_0,sK1)) )).

tff(u333,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0) != k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,k1_xboole_0))
    | k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,k1_xboole_0)) )).

tff(u332,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) != k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))) )).

tff(u331,axiom,(
    ! [X1,X0] : k7_subset_1(X0,k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))) )).

tff(u330,axiom,(
    ! [X1,X0,X2] : k7_subset_1(X1,k1_xboole_0,X0) = k7_subset_1(X2,k1_xboole_0,X0) )).

tff(u329,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X2] : k7_subset_1(u1_struct_0(sK0),sK1,X2) = k7_subset_1(sK1,sK1,X2) )).

tff(u328,axiom,(
    ! [X0] : k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 )).

tff(u327,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = k3_tarski(k2_enumset1(k7_subset_1(X2,k1_xboole_0,X1),k7_subset_1(X2,k1_xboole_0,X1),k7_subset_1(X2,k1_xboole_0,X1),k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)))))) )).

tff(u326,negated_conjecture,
    ( u1_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1)
    | u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) )).

tff(u325,negated_conjecture,
    ( sK1 != k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

tff(u324,negated_conjecture,
    ( sK1 != k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))
    | sK1 = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) )).

tff(u323,negated_conjecture,
    ( sK1 != k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)
    | sK1 = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) )).

tff(u322,negated_conjecture,
    ( sK1 != k4_subset_1(u1_struct_0(sK0),sK1,sK1)
    | sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1) )).

tff(u321,negated_conjecture,
    ( sK1 != k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)
    | sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

tff(u320,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) )).

tff(u319,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) )).

tff(u318,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2)) ) )).

tff(u317,axiom,(
    ! [X3,X4] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
      | k4_subset_1(X4,X4,X3) = k3_tarski(k2_enumset1(X4,X4,X4,X3)) ) )).

tff(u316,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k4_subset_1(X1,X1,X0) = k3_subset_1(X1,k7_subset_1(X1,k1_xboole_0,X0)) ) )).

tff(u315,axiom,(
    ! [X3,X4] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
      | k3_subset_1(X4,k7_subset_1(X4,X4,X3)) = k4_subset_1(X4,k1_xboole_0,X3) ) )).

tff(u314,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) ) )).

tff(u313,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k4_subset_1(X1,k1_xboole_0,X0) = X0 ) )).

tff(u312,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X2) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,X2)) ) )).

tff(u311,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X2) = k3_tarski(k2_enumset1(sK1,sK1,sK1,X2)) ) )).

tff(u310,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

tff(u309,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u308,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:02:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (23524)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (23515)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (23514)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (23513)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (23540)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (23523)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (23511)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (23511)Refutation not found, incomplete strategy% (23511)------------------------------
% 0.21/0.53  % (23511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (23511)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (23511)Memory used [KB]: 1663
% 0.21/0.53  % (23511)Time elapsed: 0.115 s
% 0.21/0.53  % (23511)------------------------------
% 0.21/0.53  % (23511)------------------------------
% 0.21/0.53  % (23528)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (23519)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (23512)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (23520)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (23539)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (23521)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (23513)Refutation not found, incomplete strategy% (23513)------------------------------
% 0.21/0.54  % (23513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23513)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (23513)Memory used [KB]: 10746
% 0.21/0.54  % (23513)Time elapsed: 0.120 s
% 0.21/0.54  % (23513)------------------------------
% 0.21/0.54  % (23513)------------------------------
% 0.21/0.54  % (23535)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (23515)Refutation not found, incomplete strategy% (23515)------------------------------
% 0.21/0.54  % (23515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23515)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (23515)Memory used [KB]: 6268
% 0.21/0.54  % (23515)Time elapsed: 0.128 s
% 0.21/0.54  % (23515)------------------------------
% 0.21/0.54  % (23515)------------------------------
% 0.21/0.54  % (23516)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (23537)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (23528)Refutation not found, incomplete strategy% (23528)------------------------------
% 0.21/0.54  % (23528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23532)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (23530)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (23525)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (23534)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (23532)Refutation not found, incomplete strategy% (23532)------------------------------
% 0.21/0.54  % (23532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23532)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (23532)Memory used [KB]: 1791
% 0.21/0.54  % (23532)Time elapsed: 0.127 s
% 0.21/0.54  % (23532)------------------------------
% 0.21/0.54  % (23532)------------------------------
% 0.21/0.54  % (23536)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.38/0.54  % (23527)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.38/0.54  % (23537)Refutation not found, incomplete strategy% (23537)------------------------------
% 1.38/0.54  % (23537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (23528)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (23528)Memory used [KB]: 10618
% 1.38/0.54  % (23528)Time elapsed: 0.133 s
% 1.38/0.54  % (23528)------------------------------
% 1.38/0.54  % (23528)------------------------------
% 1.38/0.54  % (23533)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.38/0.55  % (23520)Refutation not found, incomplete strategy% (23520)------------------------------
% 1.38/0.55  % (23520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (23520)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (23520)Memory used [KB]: 10618
% 1.38/0.55  % (23520)Time elapsed: 0.132 s
% 1.38/0.55  % (23520)------------------------------
% 1.38/0.55  % (23520)------------------------------
% 1.38/0.55  % (23533)Refutation not found, incomplete strategy% (23533)------------------------------
% 1.38/0.55  % (23533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (23537)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (23537)Memory used [KB]: 10746
% 1.38/0.55  % (23537)Time elapsed: 0.134 s
% 1.38/0.55  % (23537)------------------------------
% 1.38/0.55  % (23537)------------------------------
% 1.38/0.55  % (23538)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.38/0.55  % (23529)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.38/0.55  % SZS status CounterSatisfiable for theBenchmark
% 1.38/0.55  % (23522)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.38/0.55  % (23518)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.38/0.55  % (23526)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.38/0.55  % (23522)Refutation not found, incomplete strategy% (23522)------------------------------
% 1.38/0.55  % (23522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (23522)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (23522)Memory used [KB]: 10618
% 1.38/0.55  % (23522)Time elapsed: 0.139 s
% 1.38/0.55  % (23522)------------------------------
% 1.38/0.55  % (23522)------------------------------
% 1.38/0.55  % (23526)Refutation not found, incomplete strategy% (23526)------------------------------
% 1.38/0.55  % (23526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (23517)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.38/0.55  % (23516)Refutation not found, incomplete strategy% (23516)------------------------------
% 1.38/0.55  % (23516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (23516)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (23518)Refutation not found, incomplete strategy% (23518)------------------------------
% 1.38/0.55  % (23518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (23518)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (23518)Memory used [KB]: 6268
% 1.38/0.55  % (23518)Time elapsed: 0.137 s
% 1.38/0.55  % (23518)------------------------------
% 1.38/0.55  % (23518)------------------------------
% 1.38/0.55  % (23516)Memory used [KB]: 6396
% 1.38/0.55  % (23516)Time elapsed: 0.134 s
% 1.38/0.55  % (23516)------------------------------
% 1.38/0.55  % (23516)------------------------------
% 1.38/0.55  % (23531)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.38/0.55  % (23526)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (23526)Memory used [KB]: 6140
% 1.38/0.55  % (23526)Time elapsed: 0.003 s
% 1.38/0.55  % (23526)------------------------------
% 1.38/0.55  % (23526)------------------------------
% 1.38/0.56  % (23521)Refutation not found, incomplete strategy% (23521)------------------------------
% 1.38/0.56  % (23521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (23521)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (23521)Memory used [KB]: 10618
% 1.38/0.56  % (23521)Time elapsed: 0.139 s
% 1.38/0.56  % (23521)------------------------------
% 1.38/0.56  % (23521)------------------------------
% 1.38/0.56  % (23519)Refutation not found, incomplete strategy% (23519)------------------------------
% 1.38/0.56  % (23519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (23534)Refutation not found, incomplete strategy% (23534)------------------------------
% 1.38/0.56  % (23534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (23534)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (23534)Memory used [KB]: 1791
% 1.38/0.56  % (23534)Time elapsed: 0.107 s
% 1.38/0.56  % (23534)------------------------------
% 1.38/0.56  % (23534)------------------------------
% 1.38/0.56  % (23533)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (23533)Memory used [KB]: 10746
% 1.38/0.56  % (23533)Time elapsed: 0.095 s
% 1.38/0.56  % (23533)------------------------------
% 1.38/0.56  % (23533)------------------------------
% 1.38/0.56  % (23531)Refutation not found, incomplete strategy% (23531)------------------------------
% 1.38/0.56  % (23531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (23531)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (23531)Memory used [KB]: 10746
% 1.38/0.56  % (23531)Time elapsed: 0.152 s
% 1.38/0.56  % (23531)------------------------------
% 1.38/0.56  % (23531)------------------------------
% 1.38/0.56  % (23536)Refutation not found, incomplete strategy% (23536)------------------------------
% 1.38/0.56  % (23536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (23536)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (23536)Memory used [KB]: 6396
% 1.38/0.56  % (23536)Time elapsed: 0.141 s
% 1.38/0.56  % (23536)------------------------------
% 1.38/0.56  % (23536)------------------------------
% 1.58/0.56  % (23519)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.56  
% 1.58/0.56  % (23519)Memory used [KB]: 10746
% 1.58/0.56  % (23519)Time elapsed: 0.142 s
% 1.58/0.56  % (23519)------------------------------
% 1.58/0.56  % (23519)------------------------------
% 1.58/0.56  % (23527)# SZS output start Saturation.
% 1.58/0.56  tff(u358,negated_conjecture,
% 1.58/0.56      ((~(sK1 != k2_struct_0(sK0))) | (sK1 != k2_struct_0(sK0)))).
% 1.58/0.56  
% 1.58/0.56  tff(u357,axiom,
% 1.58/0.56      (![X0] : ((k5_xboole_0(X0,X0) = k1_xboole_0)))).
% 1.58/0.56  
% 1.58/0.56  tff(u356,axiom,
% 1.58/0.56      (![X3, X4] : ((k7_subset_1(X3,X3,X4) = k5_xboole_0(X3,k1_setfam_1(k2_enumset1(X3,X3,X3,X4))))))).
% 1.58/0.56  
% 1.58/0.56  tff(u355,axiom,
% 1.58/0.56      (![X0] : ((k1_xboole_0 = k3_subset_1(X0,X0))))).
% 1.58/0.56  
% 1.58/0.56  tff(u354,axiom,
% 1.58/0.56      (![X0] : ((k1_xboole_0 = k3_subset_1(X0,k7_subset_1(X0,X0,k1_xboole_0)))))).
% 1.58/0.56  
% 1.58/0.56  tff(u353,axiom,
% 1.58/0.56      (![X0] : ((k1_xboole_0 = k7_subset_1(X0,k1_xboole_0,k1_xboole_0))))).
% 1.58/0.56  
% 1.58/0.56  tff(u352,axiom,
% 1.58/0.56      (![X0] : ((k1_xboole_0 = k7_subset_1(X0,X0,X0))))).
% 1.58/0.56  
% 1.58/0.56  tff(u351,negated_conjecture,
% 1.58/0.56      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)))).
% 1.58/0.56  
% 1.58/0.56  tff(u350,negated_conjecture,
% 1.58/0.56      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 1.58/0.56  
% 1.58/0.56  tff(u349,axiom,
% 1.58/0.56      (![X0] : ((k1_xboole_0 = k4_subset_1(X0,k1_xboole_0,k1_xboole_0))))).
% 1.58/0.56  
% 1.58/0.56  tff(u348,axiom,
% 1.58/0.56      (![X0] : ((k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0)))).
% 1.58/0.56  
% 1.58/0.56  tff(u347,axiom,
% 1.58/0.56      (![X0] : ((k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0)))).
% 1.58/0.56  
% 1.58/0.56  tff(u346,axiom,
% 1.58/0.56      (![X1, X0] : ((k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))))))).
% 1.58/0.56  
% 1.58/0.56  tff(u345,axiom,
% 1.58/0.56      (![X1, X0] : ((k3_tarski(k2_enumset1(X0,X0,X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) = k3_tarski(k2_enumset1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k1_setfam_1(k2_enumset1(X0,X0,X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))))))))).
% 1.58/0.56  
% 1.58/0.56  tff(u344,axiom,
% 1.58/0.56      (![X0] : ((k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0)))).
% 1.58/0.56  
% 1.58/0.56  tff(u343,axiom,
% 1.58/0.56      (![X0] : ((k3_subset_1(X0,k1_xboole_0) = X0)))).
% 1.58/0.56  
% 1.58/0.56  tff(u342,axiom,
% 1.58/0.56      (![X1] : ((k3_subset_1(X1,k7_subset_1(X1,k1_xboole_0,X1)) = X1)))).
% 1.58/0.56  
% 1.58/0.56  tff(u341,axiom,
% 1.58/0.56      (![X1, X0] : ((k3_subset_1(X0,k7_subset_1(X1,k1_xboole_0,X0)) = X0)))).
% 1.58/0.56  
% 1.58/0.56  tff(u340,axiom,
% 1.58/0.56      (![X1] : ((k4_subset_1(X1,k1_xboole_0,X1) = X1)))).
% 1.58/0.56  
% 1.58/0.56  tff(u339,axiom,
% 1.58/0.56      (![X1] : ((k4_subset_1(X1,X1,X1) = X1)))).
% 1.58/0.56  
% 1.58/0.56  tff(u338,axiom,
% 1.58/0.56      (![X0] : ((k4_subset_1(X0,X0,k1_xboole_0) = X0)))).
% 1.58/0.56  
% 1.58/0.56  tff(u337,negated_conjecture,
% 1.58/0.56      ((~(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,u1_struct_0(sK0))))) | (k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,u1_struct_0(sK0)))))).
% 1.58/0.56  
% 1.58/0.56  tff(u336,negated_conjecture,
% 1.58/0.56      ((~(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1)))) | (k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1))))).
% 1.58/0.56  
% 1.58/0.56  tff(u335,negated_conjecture,
% 1.58/0.56      ((~(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)))) | (k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1))))).
% 1.58/0.56  
% 1.58/0.56  tff(u334,negated_conjecture,
% 1.58/0.56      ((~(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)))) | (![X0] : ((k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(X0,k1_xboole_0,sK1))))))).
% 1.58/0.56  
% 1.58/0.56  tff(u333,negated_conjecture,
% 1.58/0.56      ((~(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,k1_xboole_0)))) | (k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,k1_xboole_0))))).
% 1.58/0.56  
% 1.58/0.56  tff(u332,negated_conjecture,
% 1.58/0.56      ((~(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))))) | (k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0)))))).
% 1.58/0.56  
% 1.58/0.56  tff(u331,axiom,
% 1.58/0.56      (![X1, X0] : ((k7_subset_1(X0,k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))))))).
% 1.58/0.56  
% 1.58/0.56  tff(u330,axiom,
% 1.58/0.56      (![X1, X0, X2] : ((k7_subset_1(X1,k1_xboole_0,X0) = k7_subset_1(X2,k1_xboole_0,X0))))).
% 1.58/0.56  
% 1.58/0.56  tff(u329,negated_conjecture,
% 1.58/0.56      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X2] : ((k7_subset_1(u1_struct_0(sK0),sK1,X2) = k7_subset_1(sK1,sK1,X2)))))).
% 1.58/0.56  
% 1.58/0.56  tff(u328,axiom,
% 1.58/0.56      (![X0] : ((k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0)))).
% 1.58/0.56  
% 1.58/0.56  tff(u327,axiom,
% 1.58/0.56      (![X1, X2] : ((k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = k3_tarski(k2_enumset1(k7_subset_1(X2,k1_xboole_0,X1),k7_subset_1(X2,k1_xboole_0,X1),k7_subset_1(X2,k1_xboole_0,X1),k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)))))))))).
% 1.58/0.56  
% 1.58/0.56  tff(u326,negated_conjecture,
% 1.58/0.56      ((~(u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1))) | (u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1)))).
% 1.58/0.56  
% 1.58/0.56  tff(u325,negated_conjecture,
% 1.58/0.56      ((~(sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) | (sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))).
% 1.58/0.56  
% 1.58/0.56  tff(u324,negated_conjecture,
% 1.58/0.56      ((~(sK1 = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)))) | (sK1 = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))))).
% 1.58/0.56  
% 1.58/0.56  tff(u323,negated_conjecture,
% 1.58/0.56      ((~(sK1 = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1))) | (sK1 = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)))).
% 1.58/0.56  
% 1.58/0.56  tff(u322,negated_conjecture,
% 1.58/0.56      ((~(sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1))) | (sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1)))).
% 1.58/0.56  
% 1.58/0.56  tff(u321,negated_conjecture,
% 1.58/0.56      ((~(sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0))) | (sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)))).
% 1.58/0.56  
% 1.58/0.56  tff(u320,axiom,
% 1.58/0.56      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1))))).
% 1.58/0.56  
% 1.58/0.56  tff(u319,axiom,
% 1.58/0.56      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))))).
% 1.58/0.56  
% 1.58/0.56  tff(u318,axiom,
% 1.58/0.56      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | (k4_subset_1(X0,X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2))))))).
% 1.58/0.56  
% 1.58/0.56  tff(u317,axiom,
% 1.58/0.56      (![X3, X4] : ((~m1_subset_1(X3,k1_zfmisc_1(X4)) | (k4_subset_1(X4,X4,X3) = k3_tarski(k2_enumset1(X4,X4,X4,X3))))))).
% 1.58/0.56  
% 1.58/0.56  tff(u316,axiom,
% 1.58/0.56      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | (k4_subset_1(X1,X1,X0) = k3_subset_1(X1,k7_subset_1(X1,k1_xboole_0,X0))))))).
% 1.58/0.56  
% 1.58/0.56  tff(u315,axiom,
% 1.58/0.56      (![X3, X4] : ((~m1_subset_1(X3,k1_zfmisc_1(X4)) | (k3_subset_1(X4,k7_subset_1(X4,X4,X3)) = k4_subset_1(X4,k1_xboole_0,X3)))))).
% 1.58/0.56  
% 1.58/0.56  tff(u314,axiom,
% 1.58/0.56      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)))))).
% 1.58/0.56  
% 1.58/0.56  tff(u313,axiom,
% 1.58/0.56      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | (k4_subset_1(X1,k1_xboole_0,X0) = X0))))).
% 1.58/0.56  
% 1.58/0.56  tff(u312,negated_conjecture,
% 1.58/0.56      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X2] : ((~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | (k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X2) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,X2)))))))).
% 1.58/0.56  
% 1.58/0.56  tff(u311,negated_conjecture,
% 1.58/0.56      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X2] : ((~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | (k4_subset_1(u1_struct_0(sK0),sK1,X2) = k3_tarski(k2_enumset1(sK1,sK1,sK1,X2)))))))).
% 1.58/0.56  
% 1.58/0.56  tff(u310,axiom,
% 1.58/0.56      (![X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))))).
% 1.58/0.56  
% 1.58/0.56  tff(u309,negated_conjecture,
% 1.58/0.56      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 1.58/0.56  
% 1.58/0.56  tff(u308,axiom,
% 1.58/0.56      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 1.58/0.56  
% 1.58/0.56  % (23527)# SZS output end Saturation.
% 1.58/0.56  % (23527)------------------------------
% 1.58/0.56  % (23527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.56  % (23527)Termination reason: Satisfiable
% 1.58/0.56  
% 1.58/0.56  % (23527)Memory used [KB]: 11001
% 1.58/0.56  % (23527)Time elapsed: 0.136 s
% 1.58/0.56  % (23527)------------------------------
% 1.58/0.56  % (23527)------------------------------
% 1.58/0.56  % (23523)Refutation not found, incomplete strategy% (23523)------------------------------
% 1.58/0.56  % (23523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.56  % (23523)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.56  
% 1.58/0.56  % (23523)Memory used [KB]: 6524
% 1.58/0.56  % (23523)Time elapsed: 0.137 s
% 1.58/0.56  % (23523)------------------------------
% 1.58/0.56  % (23523)------------------------------
% 1.58/0.56  % (23510)Success in time 0.186 s
%------------------------------------------------------------------------------
