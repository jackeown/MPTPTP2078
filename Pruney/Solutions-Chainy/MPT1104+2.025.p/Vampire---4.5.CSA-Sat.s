%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:53 EST 2020

% Result     : CounterSatisfiable 1.40s
% Output     : Saturation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   62 (  62 expanded)
%              Number of leaves         :   62 (  62 expanded)
%              Depth                    :    0
%              Number of atoms          :  113 ( 113 expanded)
%              Number of equality atoms :   79 (  79 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u376,negated_conjecture,
    ( ~ ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )
    | sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u375,axiom,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) )).

tff(u374,axiom,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) )).

tff(u373,negated_conjecture,
    ( k1_xboole_0 != k1_setfam_1(k2_tarski(sK1,sK2))
    | k1_xboole_0 = k1_setfam_1(k2_tarski(sK1,sK2)) )).

tff(u372,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) )).

tff(u371,axiom,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) )).

tff(u370,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u369,axiom,(
    ! [X1,X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X1,k3_tarski(k2_tarski(X0,X1))))) )).

tff(u368,axiom,(
    ! [X1,X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),k1_setfam_1(k2_tarski(X1,k3_tarski(k2_tarski(X1,X0))))) )).

tff(u367,axiom,(
    ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

tff(u366,axiom,(
    ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 )).

tff(u365,axiom,(
    ! [X0] : k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 )).

tff(u364,negated_conjecture,
    ( k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) != k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))
    | k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

tff(u363,negated_conjecture,
    ( k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) != k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))
    | k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

tff(u362,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u361,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),sK1)
    | k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) )).

tff(u360,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK2) != k5_xboole_0(u1_struct_0(sK0),sK2)
    | k3_subset_1(u1_struct_0(sK0),sK2) = k5_xboole_0(u1_struct_0(sK0),sK2) )).

tff(u359,axiom,(
    ! [X0] : k4_subset_1(X0,X0,X0) = k3_tarski(k2_tarski(X0,X0)) )).

tff(u358,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) != k3_tarski(k2_tarski(sK1,sK1))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1)) )).

tff(u357,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) != k3_tarski(k2_tarski(sK2,sK2))
    | k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k3_tarski(k2_tarski(sK2,sK2)) )).

tff(u356,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) != k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) )).

tff(u355,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) != k3_tarski(k2_tarski(sK2,u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) )).

tff(u354,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k1_setfam_1(k2_tarski(X0,sK1)) )).

tff(u353,axiom,(
    ! [X0] : k7_subset_1(X0,X0,X0) = k9_subset_1(X0,X0,k1_xboole_0) )).

tff(u352,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) != k9_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)
    | k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k9_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

tff(u351,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) != k9_subset_1(u1_struct_0(sK0),sK2,k1_xboole_0)
    | k7_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k9_subset_1(u1_struct_0(sK0),sK2,k1_xboole_0) )).

tff(u350,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK1) != k9_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(u1_struct_0(sK0),sK1))
    | k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(u1_struct_0(sK0),sK1)) )).

tff(u349,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(u1_struct_0(sK0),sK2))
    | k7_subset_1(u1_struct_0(sK0),sK1,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(u1_struct_0(sK0),sK2)) )).

tff(u348,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,sK1) != k9_subset_1(u1_struct_0(sK0),sK2,k5_xboole_0(u1_struct_0(sK0),sK1))
    | k7_subset_1(u1_struct_0(sK0),sK2,sK1) = k9_subset_1(u1_struct_0(sK0),sK2,k5_xboole_0(u1_struct_0(sK0),sK1)) )).

tff(u347,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,sK2) != k9_subset_1(u1_struct_0(sK0),sK2,k5_xboole_0(u1_struct_0(sK0),sK2))
    | k7_subset_1(u1_struct_0(sK0),sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,k5_xboole_0(u1_struct_0(sK0),sK2)) )).

tff(u346,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) != k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))
    | k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) )).

tff(u345,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK2))
    | k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK2)) )).

tff(u344,axiom,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 )).

tff(u343,axiom,(
    ! [X3,X2] : k9_subset_1(X2,X3,X2) = k1_setfam_1(k2_tarski(X3,X2)) )).

tff(u342,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK2) = k1_setfam_1(k2_tarski(X1,sK2)) )).

tff(u341,negated_conjecture,
    ( k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK1,sK2)
    | k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

tff(u340,negated_conjecture,
    ( k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK2,sK1)
    | k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

tff(u339,negated_conjecture,
    ( k2_struct_0(sK0) != k3_tarski(k2_tarski(sK1,sK2))
    | k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2)) )).

tff(u338,negated_conjecture,
    ( sK1 != k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))
    | sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) )).

tff(u337,negated_conjecture,
    ( sK1 != k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))))
    | sK1 = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))) )).

tff(u336,negated_conjecture,
    ( sK2 != k1_setfam_1(k2_tarski(sK2,u1_struct_0(sK0)))
    | sK2 = k1_setfam_1(k2_tarski(sK2,u1_struct_0(sK0))) )).

tff(u335,negated_conjecture,
    ( sK2 != k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0))))
    | sK2 = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))) )).

tff(u334,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) ) )).

tff(u333,negated_conjecture,
    ( ~ r1_xboole_0(sK1,sK2)
    | r1_xboole_0(sK1,sK2) )).

tff(u332,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) )).

tff(u331,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u330,negated_conjecture,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | r1_tarski(sK1,u1_struct_0(sK0)) )).

tff(u329,negated_conjecture,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | r1_tarski(sK2,u1_struct_0(sK0)) )).

tff(u328,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) )).

tff(u327,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) )).

tff(u326,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) )).

tff(u325,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) )).

tff(u324,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) ) )).

tff(u323,axiom,(
    ! [X3,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | k4_subset_1(X3,X3,X2) = k3_tarski(k2_tarski(X3,X2)) ) )).

tff(u322,axiom,(
    ! [X3,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | k7_subset_1(X3,X3,X2) = k9_subset_1(X3,X3,k3_subset_1(X3,X2)) ) )).

tff(u321,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_subset_1(u1_struct_0(sK0),sK2,X1) = k9_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),X1)) ) )).

tff(u320,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_subset_1(u1_struct_0(sK0),sK1,X0) = k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),X0)) ) )).

tff(u319,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK2,X1) = k3_tarski(k2_tarski(sK2,X1)) ) )).

tff(u318,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0)) ) )).

tff(u317,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u316,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u315,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:34:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.40/0.55  % (7828)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.40/0.55  % (7829)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.40/0.56  % (7836)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.40/0.56  % (7836)Refutation not found, incomplete strategy% (7836)------------------------------
% 1.40/0.56  % (7836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (7836)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (7836)Memory used [KB]: 6140
% 1.40/0.56  % (7836)Time elapsed: 0.002 s
% 1.40/0.56  % (7836)------------------------------
% 1.40/0.56  % (7836)------------------------------
% 1.40/0.56  % (7845)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.40/0.56  % (7837)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.40/0.57  % SZS status CounterSatisfiable for theBenchmark
% 1.40/0.57  % (7828)Refutation not found, incomplete strategy% (7828)------------------------------
% 1.40/0.57  % (7828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.57  % (7829)Refutation not found, incomplete strategy% (7829)------------------------------
% 1.40/0.57  % (7829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.57  % (7829)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.57  
% 1.40/0.57  % (7829)Memory used [KB]: 10746
% 1.40/0.57  % (7829)Time elapsed: 0.112 s
% 1.40/0.57  % (7829)------------------------------
% 1.40/0.57  % (7829)------------------------------
% 1.40/0.57  % (7831)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.40/0.57  % (7839)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.40/0.57  % (7827)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.40/0.57  % (7844)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.40/0.58  % (7831)Refutation not found, incomplete strategy% (7831)------------------------------
% 1.40/0.58  % (7831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.58  % (7831)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.58  
% 1.40/0.58  % (7831)Memory used [KB]: 10746
% 1.40/0.58  % (7831)Time elapsed: 0.097 s
% 1.40/0.58  % (7831)------------------------------
% 1.40/0.58  % (7831)------------------------------
% 1.40/0.58  % (7844)Refutation not found, incomplete strategy% (7844)------------------------------
% 1.40/0.58  % (7844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.58  % (7844)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.58  
% 1.40/0.58  % (7844)Memory used [KB]: 1791
% 1.40/0.58  % (7844)Time elapsed: 0.137 s
% 1.40/0.58  % (7844)------------------------------
% 1.40/0.58  % (7844)------------------------------
% 1.40/0.58  % (7822)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.40/0.58  % (7824)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.40/0.58  % (7847)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.40/0.58  % (7823)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.40/0.58  % (7825)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.40/0.58  % (7828)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.58  
% 1.40/0.58  % (7828)Memory used [KB]: 6396
% 1.40/0.58  % (7828)Time elapsed: 0.127 s
% 1.40/0.58  % (7828)------------------------------
% 1.40/0.58  % (7828)------------------------------
% 1.40/0.58  % (7843)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.40/0.59  % (7846)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.40/0.59  % (7835)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.40/0.59  % (7825)Refutation not found, incomplete strategy% (7825)------------------------------
% 1.40/0.59  % (7825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.59  % (7825)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.59  
% 1.40/0.59  % (7825)Memory used [KB]: 6268
% 1.40/0.59  % (7825)Time elapsed: 0.152 s
% 1.40/0.59  % (7825)------------------------------
% 1.40/0.59  % (7825)------------------------------
% 1.40/0.59  % (7840)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.40/0.59  % (7837)# SZS output start Saturation.
% 1.40/0.59  tff(u376,negated_conjecture,
% 1.40/0.59      ((~(sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 1.40/0.59  
% 1.40/0.59  tff(u375,axiom,
% 1.40/0.59      (![X0] : ((k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)))))).
% 1.40/0.59  
% 1.40/0.59  tff(u374,axiom,
% 1.40/0.59      (![X0] : ((k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)))))).
% 1.40/0.59  
% 1.40/0.59  tff(u373,negated_conjecture,
% 1.40/0.59      ((~(k1_xboole_0 = k1_setfam_1(k2_tarski(sK1,sK2)))) | (k1_xboole_0 = k1_setfam_1(k2_tarski(sK1,sK2))))).
% 1.40/0.59  
% 1.40/0.59  tff(u372,axiom,
% 1.40/0.59      (![X0] : ((k1_xboole_0 = k5_xboole_0(X0,X0))))).
% 1.40/0.59  
% 1.40/0.59  tff(u371,axiom,
% 1.40/0.59      (![X0] : ((k1_xboole_0 = k3_subset_1(X0,X0))))).
% 1.40/0.59  
% 1.40/0.59  tff(u370,axiom,
% 1.40/0.59      (![X0] : ((k5_xboole_0(X0,k1_xboole_0) = X0)))).
% 1.40/0.59  
% 1.40/0.59  tff(u369,axiom,
% 1.40/0.59      (![X1, X0] : ((k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X1,k3_tarski(k2_tarski(X0,X1))))))))).
% 1.40/0.59  
% 1.40/0.59  tff(u368,axiom,
% 1.40/0.59      (![X1, X0] : ((k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),k1_setfam_1(k2_tarski(X1,k3_tarski(k2_tarski(X1,X0))))))))).
% 1.40/0.59  
% 1.40/0.59  tff(u367,axiom,
% 1.40/0.59      (![X1, X0] : ((k2_tarski(X0,X1) = k2_tarski(X1,X0))))).
% 1.40/0.59  
% 1.40/0.59  tff(u366,axiom,
% 1.40/0.59      (![X0] : ((k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0)))).
% 1.40/0.59  
% 1.40/0.59  tff(u365,axiom,
% 1.40/0.59      (![X0] : ((k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0)))).
% 1.40/0.59  
% 1.40/0.59  tff(u364,negated_conjecture,
% 1.40/0.59      ((~(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)))) | (k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))))).
% 1.40/0.59  
% 1.40/0.59  tff(u363,negated_conjecture,
% 1.40/0.59      ((~(k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)))) | (k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))))).
% 1.40/0.59  
% 1.40/0.59  tff(u362,axiom,
% 1.40/0.59      (![X0] : ((k2_subset_1(X0) = X0)))).
% 1.40/0.59  
% 1.40/0.59  tff(u361,negated_conjecture,
% 1.40/0.59      ((~(k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1))) | (k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1)))).
% 1.40/0.59  
% 1.40/0.59  tff(u360,negated_conjecture,
% 1.40/0.59      ((~(k3_subset_1(u1_struct_0(sK0),sK2) = k5_xboole_0(u1_struct_0(sK0),sK2))) | (k3_subset_1(u1_struct_0(sK0),sK2) = k5_xboole_0(u1_struct_0(sK0),sK2)))).
% 1.40/0.59  
% 1.40/0.59  tff(u359,axiom,
% 1.40/0.59      (![X0] : ((k4_subset_1(X0,X0,X0) = k3_tarski(k2_tarski(X0,X0)))))).
% 1.40/0.59  
% 1.40/0.59  tff(u358,negated_conjecture,
% 1.40/0.59      ((~(k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1)))) | (k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1))))).
% 1.40/0.59  
% 1.40/0.59  tff(u357,negated_conjecture,
% 1.40/0.59      ((~(k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k3_tarski(k2_tarski(sK2,sK2)))) | (k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k3_tarski(k2_tarski(sK2,sK2))))).
% 1.40/0.59  
% 1.40/0.59  tff(u356,negated_conjecture,
% 1.40/0.59      ((~(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))))) | (k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))))).
% 1.40/0.59  
% 1.40/0.59  tff(u355,negated_conjecture,
% 1.40/0.59      ((~(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))))) | (k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0)))))).
% 1.40/0.59  
% 1.40/0.59  tff(u354,negated_conjecture,
% 1.40/0.59      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((k9_subset_1(u1_struct_0(sK0),X0,sK1) = k1_setfam_1(k2_tarski(X0,sK1))))))).
% 1.40/0.59  
% 1.40/0.59  tff(u353,axiom,
% 1.40/0.59      (![X0] : ((k7_subset_1(X0,X0,X0) = k9_subset_1(X0,X0,k1_xboole_0))))).
% 1.40/0.59  
% 1.40/0.59  tff(u352,negated_conjecture,
% 1.40/0.59      ((~(k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k9_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0))) | (k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k9_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)))).
% 1.40/0.59  
% 1.40/0.59  tff(u351,negated_conjecture,
% 1.40/0.59      ((~(k7_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k9_subset_1(u1_struct_0(sK0),sK2,k1_xboole_0))) | (k7_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k9_subset_1(u1_struct_0(sK0),sK2,k1_xboole_0)))).
% 1.40/0.59  
% 1.40/0.59  tff(u350,negated_conjecture,
% 1.40/0.59      ((~(k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(u1_struct_0(sK0),sK1)))) | (k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(u1_struct_0(sK0),sK1))))).
% 1.40/0.59  
% 1.40/0.59  tff(u349,negated_conjecture,
% 1.40/0.59      ((~(k7_subset_1(u1_struct_0(sK0),sK1,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(u1_struct_0(sK0),sK2)))) | (k7_subset_1(u1_struct_0(sK0),sK1,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(u1_struct_0(sK0),sK2))))).
% 1.40/0.59  
% 1.40/0.59  tff(u348,negated_conjecture,
% 1.40/0.59      ((~(k7_subset_1(u1_struct_0(sK0),sK2,sK1) = k9_subset_1(u1_struct_0(sK0),sK2,k5_xboole_0(u1_struct_0(sK0),sK1)))) | (k7_subset_1(u1_struct_0(sK0),sK2,sK1) = k9_subset_1(u1_struct_0(sK0),sK2,k5_xboole_0(u1_struct_0(sK0),sK1))))).
% 1.40/0.59  
% 1.40/0.59  tff(u347,negated_conjecture,
% 1.40/0.59      ((~(k7_subset_1(u1_struct_0(sK0),sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,k5_xboole_0(u1_struct_0(sK0),sK2)))) | (k7_subset_1(u1_struct_0(sK0),sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,k5_xboole_0(u1_struct_0(sK0),sK2))))).
% 1.40/0.59  
% 1.40/0.59  tff(u346,negated_conjecture,
% 1.40/0.59      ((~(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)))) | (k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))))).
% 1.40/0.59  
% 1.40/0.59  tff(u345,negated_conjecture,
% 1.40/0.59      ((~(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK2)))) | (k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK2))))).
% 1.40/0.59  
% 1.40/0.59  tff(u344,axiom,
% 1.40/0.59      (![X0] : ((k1_setfam_1(k2_tarski(X0,X0)) = X0)))).
% 1.40/0.59  
% 1.40/0.59  tff(u343,axiom,
% 1.40/0.59      (![X3, X2] : ((k9_subset_1(X2,X3,X2) = k1_setfam_1(k2_tarski(X3,X2)))))).
% 1.40/0.59  
% 1.40/0.59  tff(u342,negated_conjecture,
% 1.40/0.59      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X1] : ((k9_subset_1(u1_struct_0(sK0),X1,sK2) = k1_setfam_1(k2_tarski(X1,sK2))))))).
% 1.40/0.59  
% 1.40/0.59  tff(u341,negated_conjecture,
% 1.40/0.59      ((~(k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | (k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)))).
% 1.40/0.59  
% 1.40/0.59  tff(u340,negated_conjecture,
% 1.40/0.59      ((~(k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1))) | (k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)))).
% 1.40/0.59  
% 1.40/0.59  tff(u339,negated_conjecture,
% 1.40/0.59      ((~(k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2)))) | (k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2))))).
% 1.40/0.59  
% 1.40/0.59  tff(u338,negated_conjecture,
% 1.40/0.59      ((~(sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))))) | (sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))))).
% 1.40/0.59  
% 1.40/0.59  tff(u337,negated_conjecture,
% 1.40/0.59      ((~(sK1 = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))))) | (sK1 = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))))))).
% 1.40/0.59  
% 1.40/0.59  tff(u336,negated_conjecture,
% 1.40/0.59      ((~(sK2 = k1_setfam_1(k2_tarski(sK2,u1_struct_0(sK0))))) | (sK2 = k1_setfam_1(k2_tarski(sK2,u1_struct_0(sK0)))))).
% 1.40/0.59  
% 1.40/0.59  tff(u335,negated_conjecture,
% 1.40/0.59      ((~(sK2 = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))))) | (sK2 = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0))))))).
% 1.40/0.59  
% 1.40/0.59  tff(u334,axiom,
% 1.40/0.59      (![X1, X0] : ((~r1_xboole_0(X0,X1) | (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))))))).
% 1.40/0.59  
% 1.40/0.59  tff(u333,negated_conjecture,
% 1.40/0.59      ((~r1_xboole_0(sK1,sK2)) | r1_xboole_0(sK1,sK2))).
% 1.40/0.59  
% 1.40/0.59  tff(u332,axiom,
% 1.40/0.59      (![X1, X0] : ((~r1_tarski(X0,X1) | (k1_setfam_1(k2_tarski(X0,X1)) = X0))))).
% 1.40/0.59  
% 1.40/0.59  tff(u331,axiom,
% 1.40/0.59      (![X0] : (r1_tarski(X0,X0)))).
% 1.40/0.59  
% 1.40/0.59  tff(u330,negated_conjecture,
% 1.40/0.59      ((~r1_tarski(sK1,u1_struct_0(sK0))) | r1_tarski(sK1,u1_struct_0(sK0)))).
% 1.40/0.59  
% 1.40/0.59  tff(u329,negated_conjecture,
% 1.40/0.59      ((~r1_tarski(sK2,u1_struct_0(sK0))) | r1_tarski(sK2,u1_struct_0(sK0)))).
% 1.40/0.59  
% 1.40/0.59  tff(u328,axiom,
% 1.40/0.59      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))))).
% 1.40/0.59  
% 1.40/0.59  tff(u327,axiom,
% 1.40/0.59      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))).
% 1.40/0.59  
% 1.40/0.59  tff(u326,axiom,
% 1.40/0.59      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))))).
% 1.40/0.59  
% 1.40/0.59  tff(u325,axiom,
% 1.40/0.59      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(X0)) | (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))))))).
% 1.40/0.59  
% 1.40/0.59  tff(u324,axiom,
% 1.40/0.59      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | (k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))))))).
% 1.40/0.59  
% 1.40/0.59  tff(u323,axiom,
% 1.40/0.59      (![X3, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(X3)) | (k4_subset_1(X3,X3,X2) = k3_tarski(k2_tarski(X3,X2))))))).
% 1.40/0.59  
% 1.40/0.59  tff(u322,axiom,
% 1.40/0.59      (![X3, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(X3)) | (k7_subset_1(X3,X3,X2) = k9_subset_1(X3,X3,k3_subset_1(X3,X2))))))).
% 1.40/0.59  
% 1.40/0.59  tff(u321,negated_conjecture,
% 1.40/0.59      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | (k7_subset_1(u1_struct_0(sK0),sK2,X1) = k9_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),X1)))))))).
% 1.40/0.59  
% 1.40/0.59  tff(u320,negated_conjecture,
% 1.40/0.59      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),X0)))))))).
% 1.40/0.59  
% 1.40/0.59  tff(u319,negated_conjecture,
% 1.40/0.59      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | (k4_subset_1(u1_struct_0(sK0),sK2,X1) = k3_tarski(k2_tarski(sK2,X1)))))))).
% 1.40/0.59  
% 1.40/0.59  tff(u318,negated_conjecture,
% 1.40/0.59      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | (k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0)))))))).
% 1.40/0.59  
% 1.40/0.59  tff(u317,negated_conjecture,
% 1.40/0.59      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 1.40/0.59  
% 1.40/0.59  tff(u316,negated_conjecture,
% 1.40/0.59      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))).
% 1.40/0.59  
% 1.40/0.59  tff(u315,axiom,
% 1.40/0.59      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 1.40/0.59  
% 1.40/0.59  % (7837)# SZS output end Saturation.
% 1.40/0.59  % (7837)------------------------------
% 1.40/0.59  % (7837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.59  % (7837)Termination reason: Satisfiable
% 1.40/0.59  
% 1.40/0.59  % (7837)Memory used [KB]: 11001
% 1.40/0.59  % (7837)Time elapsed: 0.130 s
% 1.40/0.59  % (7837)------------------------------
% 1.40/0.59  % (7837)------------------------------
% 1.40/0.59  % (7820)Success in time 0.218 s
%------------------------------------------------------------------------------
