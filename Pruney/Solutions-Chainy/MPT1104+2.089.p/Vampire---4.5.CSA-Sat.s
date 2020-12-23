%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:01 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   41 (  41 expanded)
%              Number of leaves         :   41 (  41 expanded)
%              Depth                    :    0
%              Number of atoms          :   76 (  76 expanded)
%              Number of equality atoms :   53 (  53 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u235,negated_conjecture,
    ( ~ ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )
    | sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u234,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

tff(u233,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK1,sK2)
    | k1_xboole_0 = k3_xboole_0(sK1,sK2) )).

tff(u232,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u231,axiom,(
    ! [X3,X2] : k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k3_xboole_0(X2,X3)) )).

tff(u230,axiom,(
    ! [X1,X0] : k5_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X0,X1),X1)) = k7_subset_1(X0,X0,X1) )).

tff(u229,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u228,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u227,axiom,(
    ! [X0] : k4_subset_1(X0,X0,X0) = k2_xboole_0(X0,X0) )).

tff(u226,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) != k2_xboole_0(u1_struct_0(sK0),sK1)
    | k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(u1_struct_0(sK0),sK1) )).

tff(u225,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) != k2_xboole_0(u1_struct_0(sK0),sK2)
    | k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(u1_struct_0(sK0),sK2) )).

tff(u224,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) != k2_xboole_0(sK1,sK1)
    | k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) )).

tff(u223,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) != k2_xboole_0(sK1,u1_struct_0(sK0))
    | k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k2_xboole_0(sK1,u1_struct_0(sK0)) )).

tff(u222,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) != k2_xboole_0(sK2,sK1)
    | k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1) )).

tff(u221,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) != k2_xboole_0(sK2,sK2)
    | k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2) )).

tff(u220,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) != k2_xboole_0(sK2,u1_struct_0(sK0))
    | k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k2_xboole_0(sK2,u1_struct_0(sK0)) )).

tff(u219,axiom,(
    ! [X0] : k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

tff(u218,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

tff(u217,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X1] : k7_subset_1(u1_struct_0(sK0),sK2,X1) = k7_subset_1(sK2,sK2,X1) )).

tff(u216,axiom,(
    ! [X3,X2] : k7_subset_1(X2,X2,X3) = k7_subset_1(k2_xboole_0(X2,X3),k2_xboole_0(X2,X3),X3) )).

tff(u215,negated_conjecture,
    ( u1_struct_0(sK0) != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

tff(u214,negated_conjecture,
    ( k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK1,sK2)
    | k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

tff(u213,negated_conjecture,
    ( k2_struct_0(sK0) != k2_xboole_0(sK1,sK2)
    | k2_struct_0(sK0) = k2_xboole_0(sK1,sK2) )).

tff(u212,negated_conjecture,
    ( sK1 != k7_subset_1(sK1,sK1,sK2)
    | sK1 = k7_subset_1(sK1,sK1,sK2) )).

tff(u211,negated_conjecture,
    ( sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
    | sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

tff(u210,negated_conjecture,
    ( sK1 != k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2)
    | sK1 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2) )).

tff(u209,negated_conjecture,
    ( sK1 != k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(k2_struct_0(sK0),sK2))
    | sK1 = k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(k2_struct_0(sK0),sK2)) )).

tff(u208,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK2))
    | sK2 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK2)) )).

tff(u207,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) )).

tff(u206,negated_conjecture,
    ( ~ r1_xboole_0(sK1,sK2)
    | r1_xboole_0(sK1,sK2) )).

tff(u205,axiom,(
    ! [X3,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | k4_subset_1(X3,X3,X2) = k2_xboole_0(X3,X2) ) )).

tff(u204,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) )).

tff(u203,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) ) )).

tff(u202,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) )).

tff(u201,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK2,X1) = k2_xboole_0(sK2,X1) ) )).

tff(u200,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0) ) )).

tff(u199,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u198,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u197,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u196,axiom,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0))) ) )).

tff(u195,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (8516)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.48  % (8516)Refutation not found, incomplete strategy% (8516)------------------------------
% 0.20/0.48  % (8516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (8524)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.49  % (8516)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (8516)Memory used [KB]: 10746
% 0.20/0.49  % (8516)Time elapsed: 0.075 s
% 0.20/0.49  % (8516)------------------------------
% 0.20/0.49  % (8516)------------------------------
% 0.20/0.49  % (8524)Refutation not found, incomplete strategy% (8524)------------------------------
% 0.20/0.49  % (8524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (8524)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (8524)Memory used [KB]: 10746
% 0.20/0.49  % (8524)Time elapsed: 0.085 s
% 0.20/0.49  % (8524)------------------------------
% 0.20/0.49  % (8524)------------------------------
% 0.20/0.51  % (8509)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (8507)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (8509)Refutation not found, incomplete strategy% (8509)------------------------------
% 0.20/0.51  % (8509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (8509)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (8509)Memory used [KB]: 6268
% 0.20/0.51  % (8509)Time elapsed: 0.108 s
% 0.20/0.51  % (8509)------------------------------
% 0.20/0.51  % (8509)------------------------------
% 0.20/0.52  % (8510)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (8527)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (8527)Refutation not found, incomplete strategy% (8527)------------------------------
% 0.20/0.52  % (8527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (8527)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (8527)Memory used [KB]: 10746
% 0.20/0.52  % (8527)Time elapsed: 0.089 s
% 0.20/0.52  % (8527)------------------------------
% 0.20/0.52  % (8527)------------------------------
% 0.20/0.52  % (8532)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.52  % (8522)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (8525)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (8523)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (8528)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (8508)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (8511)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (8517)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (8508)Refutation not found, incomplete strategy% (8508)------------------------------
% 0.20/0.53  % (8508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (8508)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (8508)Memory used [KB]: 10746
% 0.20/0.53  % (8508)Time elapsed: 0.124 s
% 0.20/0.53  % (8508)------------------------------
% 0.20/0.53  % (8508)------------------------------
% 0.20/0.53  % (8505)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (8517)Refutation not found, incomplete strategy% (8517)------------------------------
% 0.20/0.53  % (8517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (8517)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (8517)Memory used [KB]: 6268
% 0.20/0.53  % (8517)Time elapsed: 0.134 s
% 0.20/0.53  % (8517)------------------------------
% 0.20/0.53  % (8517)------------------------------
% 0.20/0.53  % (8505)Refutation not found, incomplete strategy% (8505)------------------------------
% 0.20/0.53  % (8505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (8505)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (8505)Memory used [KB]: 1791
% 0.20/0.53  % (8505)Time elapsed: 0.125 s
% 0.20/0.53  % (8505)------------------------------
% 0.20/0.53  % (8505)------------------------------
% 0.20/0.53  % (8534)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (8533)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (8507)Refutation not found, incomplete strategy% (8507)------------------------------
% 0.20/0.54  % (8507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (8507)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (8507)Memory used [KB]: 10746
% 0.20/0.54  % (8507)Time elapsed: 0.127 s
% 0.20/0.54  % (8507)------------------------------
% 0.20/0.54  % (8507)------------------------------
% 0.20/0.54  % (8530)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (8519)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (8531)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (8506)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (8520)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (8530)Refutation not found, incomplete strategy% (8530)------------------------------
% 0.20/0.54  % (8530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (8530)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (8530)Memory used [KB]: 6396
% 0.20/0.54  % (8530)Time elapsed: 0.139 s
% 0.20/0.54  % (8530)------------------------------
% 0.20/0.54  % (8530)------------------------------
% 0.20/0.54  % (8520)Refutation not found, incomplete strategy% (8520)------------------------------
% 0.20/0.54  % (8520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (8520)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (8520)Memory used [KB]: 6140
% 0.20/0.54  % (8520)Time elapsed: 0.001 s
% 0.20/0.54  % (8520)------------------------------
% 0.20/0.54  % (8520)------------------------------
% 0.20/0.54  % (8510)Refutation not found, incomplete strategy% (8510)------------------------------
% 0.20/0.54  % (8510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (8510)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (8510)Memory used [KB]: 6268
% 0.20/0.54  % (8510)Time elapsed: 0.120 s
% 0.20/0.54  % (8510)------------------------------
% 0.20/0.54  % (8510)------------------------------
% 0.20/0.54  % (8531)Refutation not found, incomplete strategy% (8531)------------------------------
% 0.20/0.54  % (8531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (8531)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (8531)Memory used [KB]: 10746
% 0.20/0.54  % (8531)Time elapsed: 0.138 s
% 0.20/0.54  % (8531)------------------------------
% 0.20/0.54  % (8531)------------------------------
% 0.20/0.54  % (8514)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (8526)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (8512)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (8514)Refutation not found, incomplete strategy% (8514)------------------------------
% 0.20/0.54  % (8514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (8514)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (8514)Memory used [KB]: 10746
% 0.20/0.54  % (8514)Time elapsed: 0.139 s
% 0.20/0.54  % (8514)------------------------------
% 0.20/0.54  % (8514)------------------------------
% 0.20/0.54  % (8526)Refutation not found, incomplete strategy% (8526)------------------------------
% 0.20/0.54  % (8526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (8526)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (8526)Memory used [KB]: 1663
% 0.20/0.54  % (8526)Time elapsed: 0.139 s
% 0.20/0.54  % (8526)------------------------------
% 0.20/0.54  % (8526)------------------------------
% 0.20/0.54  % (8525)Refutation not found, incomplete strategy% (8525)------------------------------
% 0.20/0.54  % (8525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (8525)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (8525)Memory used [KB]: 10746
% 0.20/0.54  % (8525)Time elapsed: 0.143 s
% 0.20/0.54  % (8525)------------------------------
% 0.20/0.54  % (8525)------------------------------
% 0.20/0.54  % (8512)Refutation not found, incomplete strategy% (8512)------------------------------
% 0.20/0.54  % (8512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (8512)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (8512)Memory used [KB]: 6268
% 0.20/0.54  % (8512)Time elapsed: 0.141 s
% 0.20/0.54  % (8512)------------------------------
% 0.20/0.54  % (8512)------------------------------
% 0.20/0.54  % (8522)Refutation not found, incomplete strategy% (8522)------------------------------
% 0.20/0.54  % (8522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (8522)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (8522)Memory used [KB]: 10618
% 0.20/0.54  % (8522)Time elapsed: 0.138 s
% 0.20/0.54  % (8522)------------------------------
% 0.20/0.54  % (8522)------------------------------
% 0.20/0.55  % (8518)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (8513)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.55  % (8528)Refutation not found, incomplete strategy% (8528)------------------------------
% 0.20/0.55  % (8528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (8528)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (8528)Memory used [KB]: 1791
% 0.20/0.55  % (8528)Time elapsed: 0.141 s
% 0.20/0.55  % (8528)------------------------------
% 0.20/0.55  % (8528)------------------------------
% 0.20/0.55  % (8515)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (8513)Refutation not found, incomplete strategy% (8513)------------------------------
% 0.20/0.55  % (8513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (8513)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (8513)Memory used [KB]: 10746
% 0.20/0.55  % (8513)Time elapsed: 0.149 s
% 0.20/0.55  % (8513)------------------------------
% 0.20/0.55  % (8513)------------------------------
% 0.20/0.55  % (8529)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (8521)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (8515)Refutation not found, incomplete strategy% (8515)------------------------------
% 0.20/0.55  % (8515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (8515)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (8515)Memory used [KB]: 10746
% 0.20/0.55  % (8515)Time elapsed: 0.151 s
% 0.20/0.55  % (8515)------------------------------
% 0.20/0.55  % (8515)------------------------------
% 0.20/0.55  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.55  % (8521)# SZS output start Saturation.
% 0.20/0.55  tff(u235,negated_conjecture,
% 0.20/0.55      ((~(sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 0.20/0.55  
% 0.20/0.55  tff(u234,axiom,
% 0.20/0.55      (![X0] : ((k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0))))).
% 0.20/0.55  
% 0.20/0.55  tff(u233,negated_conjecture,
% 0.20/0.55      ((~(k1_xboole_0 = k3_xboole_0(sK1,sK2))) | (k1_xboole_0 = k3_xboole_0(sK1,sK2)))).
% 0.20/0.55  
% 0.20/0.55  tff(u232,axiom,
% 0.20/0.55      (![X0] : ((k5_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.20/0.55  
% 0.20/0.55  tff(u231,axiom,
% 0.20/0.55      (![X3, X2] : ((k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k3_xboole_0(X2,X3)))))).
% 0.20/0.55  
% 0.20/0.55  tff(u230,axiom,
% 0.20/0.55      (![X1, X0] : ((k5_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X0,X1),X1)) = k7_subset_1(X0,X0,X1))))).
% 0.20/0.55  
% 0.20/0.55  tff(u229,axiom,
% 0.20/0.55      (![X0] : ((k2_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.20/0.55  
% 0.20/0.55  tff(u228,axiom,
% 0.20/0.55      (![X0] : ((k2_subset_1(X0) = X0)))).
% 0.20/0.55  
% 0.20/0.55  tff(u227,axiom,
% 0.20/0.55      (![X0] : ((k4_subset_1(X0,X0,X0) = k2_xboole_0(X0,X0))))).
% 0.20/0.55  
% 0.20/0.55  tff(u226,negated_conjecture,
% 0.20/0.55      ((~(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(u1_struct_0(sK0),sK1))) | (k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(u1_struct_0(sK0),sK1)))).
% 0.20/0.55  
% 0.20/0.55  tff(u225,negated_conjecture,
% 0.20/0.55      ((~(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(u1_struct_0(sK0),sK2))) | (k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(u1_struct_0(sK0),sK2)))).
% 0.20/0.55  
% 0.20/0.55  tff(u224,negated_conjecture,
% 0.20/0.55      ((~(k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1))) | (k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1)))).
% 0.20/0.55  
% 0.20/0.55  tff(u223,negated_conjecture,
% 0.20/0.55      ((~(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k2_xboole_0(sK1,u1_struct_0(sK0)))) | (k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k2_xboole_0(sK1,u1_struct_0(sK0))))).
% 0.20/0.55  
% 0.20/0.55  tff(u222,negated_conjecture,
% 0.20/0.55      ((~(k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1))) | (k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1)))).
% 0.20/0.55  
% 0.20/0.55  tff(u221,negated_conjecture,
% 0.20/0.55      ((~(k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2))) | (k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2)))).
% 0.20/0.55  
% 0.20/0.55  tff(u220,negated_conjecture,
% 0.20/0.55      ((~(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k2_xboole_0(sK2,u1_struct_0(sK0)))) | (k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k2_xboole_0(sK2,u1_struct_0(sK0))))).
% 0.20/0.55  
% 0.20/0.55  tff(u219,axiom,
% 0.20/0.55      (![X0] : ((k7_subset_1(X0,X0,k1_xboole_0) = X0)))).
% 0.20/0.55  
% 0.20/0.55  tff(u218,negated_conjecture,
% 0.20/0.55      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)))))).
% 0.20/0.55  
% 0.20/0.55  tff(u217,negated_conjecture,
% 0.20/0.55      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X1] : ((k7_subset_1(u1_struct_0(sK0),sK2,X1) = k7_subset_1(sK2,sK2,X1)))))).
% 0.20/0.55  
% 0.20/0.55  tff(u216,axiom,
% 0.20/0.55      (![X3, X2] : ((k7_subset_1(X2,X2,X3) = k7_subset_1(k2_xboole_0(X2,X3),k2_xboole_0(X2,X3),X3))))).
% 0.20/0.55  
% 0.20/0.55  tff(u215,negated_conjecture,
% 0.20/0.55      ((~(u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))))) | (u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))))).
% 0.20/0.55  
% 0.20/0.55  tff(u214,negated_conjecture,
% 0.20/0.55      ((~(k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | (k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)))).
% 0.20/0.55  
% 0.20/0.55  tff(u213,negated_conjecture,
% 0.20/0.55      ((~(k2_struct_0(sK0) = k2_xboole_0(sK1,sK2))) | (k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)))).
% 0.20/0.55  
% 0.20/0.55  tff(u212,negated_conjecture,
% 0.20/0.55      ((~(sK1 = k7_subset_1(sK1,sK1,sK2))) | (sK1 = k7_subset_1(sK1,sK1,sK2)))).
% 0.20/0.55  
% 0.20/0.55  tff(u211,negated_conjecture,
% 0.20/0.55      ((~(sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))) | (sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))))).
% 0.20/0.55  
% 0.20/0.55  tff(u210,negated_conjecture,
% 0.20/0.55      ((~(sK1 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2))) | (sK1 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2)))).
% 0.20/0.55  
% 0.20/0.55  tff(u209,negated_conjecture,
% 0.20/0.55      ((~(sK1 = k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(k2_struct_0(sK0),sK2)))) | (sK1 = k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(k2_struct_0(sK0),sK2))))).
% 0.20/0.55  
% 0.20/0.55  tff(u208,negated_conjecture,
% 0.20/0.55      ((~(sK2 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK2)))) | (sK2 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK2))))).
% 0.20/0.55  
% 0.20/0.55  tff(u207,axiom,
% 0.20/0.55      (![X1, X0] : ((~r1_xboole_0(X0,X1) | (k3_xboole_0(X0,X1) = k1_xboole_0))))).
% 0.20/0.55  
% 0.20/0.55  tff(u206,negated_conjecture,
% 0.20/0.55      ((~r1_xboole_0(sK1,sK2)) | r1_xboole_0(sK1,sK2))).
% 0.20/0.55  
% 0.20/0.55  tff(u205,axiom,
% 0.20/0.55      (![X3, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(X3)) | (k4_subset_1(X3,X3,X2) = k2_xboole_0(X3,X2)))))).
% 0.20/0.55  
% 0.20/0.55  tff(u204,axiom,
% 0.20/0.55      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)))))).
% 0.20/0.55  
% 0.20/0.55  tff(u203,axiom,
% 0.20/0.55      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)))))).
% 0.20/0.55  
% 0.20/0.55  tff(u202,axiom,
% 0.20/0.55      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))))).
% 0.20/0.55  
% 0.20/0.55  tff(u201,negated_conjecture,
% 0.20/0.55      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | (k4_subset_1(u1_struct_0(sK0),sK2,X1) = k2_xboole_0(sK2,X1))))))).
% 0.20/0.55  
% 0.20/0.55  tff(u200,negated_conjecture,
% 0.20/0.55      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | (k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0))))))).
% 0.20/0.55  
% 0.20/0.55  tff(u199,negated_conjecture,
% 0.20/0.55      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.20/0.55  
% 0.20/0.55  tff(u198,negated_conjecture,
% 0.20/0.55      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.20/0.55  
% 0.20/0.55  tff(u197,axiom,
% 0.20/0.55      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 0.20/0.55  
% 0.20/0.55  tff(u196,axiom,
% 0.20/0.55      (![X0] : ((~l1_struct_0(X0) | (u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0)))))))).
% 0.20/0.55  
% 0.20/0.55  tff(u195,negated_conjecture,
% 0.20/0.55      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 0.20/0.55  
% 0.20/0.55  % (8521)# SZS output end Saturation.
% 0.20/0.55  % (8521)------------------------------
% 0.20/0.55  % (8521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (8521)Termination reason: Satisfiable
% 0.20/0.55  
% 0.20/0.55  % (8521)Memory used [KB]: 10874
% 0.20/0.55  % (8521)Time elapsed: 0.151 s
% 0.20/0.55  % (8521)------------------------------
% 0.20/0.55  % (8521)------------------------------
% 0.20/0.55  % (8504)Success in time 0.186 s
%------------------------------------------------------------------------------
