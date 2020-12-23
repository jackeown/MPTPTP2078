%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:29 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    0
%              Number of atoms          :   40 (  40 expanded)
%              Number of equality atoms :   25 (  25 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u139,negated_conjecture,
    ( ~ ( sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )
    | sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

tff(u138,negated_conjecture,
    ( ~ ( k1_xboole_0 != k4_xboole_0(k2_struct_0(sK0),u1_struct_0(sK0)) )
    | k1_xboole_0 != k4_xboole_0(k2_struct_0(sK0),u1_struct_0(sK0)) )).

tff(u137,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u136,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u135,axiom,(
    ! [X1] : k1_setfam_1(k2_tarski(X1,X1)) = X1 )).

tff(u134,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK1,u1_struct_0(sK0))
    | k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)) )).

tff(u133,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) )).

% (11156)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
tff(u132,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

tff(u131,axiom,(
    ! [X3,X5,X4] :
      ( k7_subset_1(X3,X4,X5) = k4_xboole_0(X4,X5)
      | k1_xboole_0 != k4_xboole_0(X4,X3) ) )).

tff(u130,axiom,(
    ! [X3,X2] : k1_setfam_1(k2_tarski(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))) )).

tff(u129,axiom,(
    ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

tff(u128,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2) )).

tff(u127,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) )).

tff(u126,negated_conjecture,
    ( sK1 != k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))
    | sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) )).

tff(u125,axiom,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) )).

tff(u124,axiom,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) )).

tff(u123,axiom,(
    ! [X3,X5,X4] :
      ( ~ r1_tarski(X4,X3)
      | k7_subset_1(X3,X4,X5) = k4_xboole_0(X4,X5) ) )).

tff(u122,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) )).

tff(u121,negated_conjecture,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | r1_tarski(sK1,u1_struct_0(sK0)) )).

tff(u120,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u119,axiom,(
    ! [X1,X0] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) )).

tff(u118,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) )).

tff(u117,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) )).

tff(u116,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u115,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u114,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:03:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (11149)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.45  % (11143)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (11139)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (11144)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.46  % (11149)# SZS output start Saturation.
% 0.20/0.46  tff(u139,negated_conjecture,
% 0.20/0.46      ((~(sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))) | (sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))))).
% 0.20/0.46  
% 0.20/0.46  tff(u138,negated_conjecture,
% 0.20/0.46      ((~(k1_xboole_0 != k4_xboole_0(k2_struct_0(sK0),u1_struct_0(sK0)))) | (k1_xboole_0 != k4_xboole_0(k2_struct_0(sK0),u1_struct_0(sK0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u137,axiom,
% 0.20/0.46      (![X0] : ((k2_subset_1(X0) = X0)))).
% 0.20/0.46  
% 0.20/0.46  tff(u136,axiom,
% 0.20/0.46      (![X0] : ((k4_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.20/0.46  
% 0.20/0.46  tff(u135,axiom,
% 0.20/0.46      (![X1] : ((k1_setfam_1(k2_tarski(X1,X1)) = X1)))).
% 0.20/0.46  
% 0.20/0.46  tff(u134,negated_conjecture,
% 0.20/0.46      ((~(k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)))) | (k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u133,axiom,
% 0.20/0.46      (![X0] : ((k1_xboole_0 = k4_xboole_0(X0,X0))))).
% 0.20/0.46  
% 0.20/0.46  % (11156)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.47  tff(u132,negated_conjecture,
% 0.20/0.47      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u131,axiom,
% 0.20/0.47      (![X3, X5, X4] : (((k7_subset_1(X3,X4,X5) = k4_xboole_0(X4,X5)) | (k1_xboole_0 != k4_xboole_0(X4,X3)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u130,axiom,
% 0.20/0.47      (![X3, X2] : ((k1_setfam_1(k2_tarski(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))))).
% 0.20/0.47  
% 0.20/0.47  tff(u129,axiom,
% 0.20/0.47      (![X1, X0] : ((k2_tarski(X0,X1) = k2_tarski(X1,X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u128,axiom,
% 0.20/0.47      (![X1, X2] : ((k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2))))).
% 0.20/0.47  
% 0.20/0.47  tff(u127,axiom,
% 0.20/0.47      (![X1, X0] : ((k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u126,negated_conjecture,
% 0.20/0.47      ((~(sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))))) | (sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u125,axiom,
% 0.20/0.47      (![X0] : ((k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u124,axiom,
% 0.20/0.47      (![X0] : ((k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u123,axiom,
% 0.20/0.47      (![X3, X5, X4] : ((~r1_tarski(X4,X3) | (k7_subset_1(X3,X4,X5) = k4_xboole_0(X4,X5)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u122,axiom,
% 0.20/0.47      (![X1, X0] : ((~r1_tarski(X0,X1) | (k4_xboole_0(X0,X1) = k1_xboole_0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u121,negated_conjecture,
% 0.20/0.47      ((~r1_tarski(sK1,u1_struct_0(sK0))) | r1_tarski(sK1,u1_struct_0(sK0)))).
% 0.20/0.47  
% 0.20/0.47  tff(u120,axiom,
% 0.20/0.47      (![X0] : (r1_tarski(X0,X0)))).
% 0.20/0.47  
% 0.20/0.47  tff(u119,axiom,
% 0.20/0.47      (![X1, X0] : ((r1_tarski(X0,X1) | (k4_xboole_0(X0,X1) != k1_xboole_0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u118,axiom,
% 0.20/0.47      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u117,axiom,
% 0.20/0.47      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u116,negated_conjecture,
% 0.20/0.47      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u115,axiom,
% 0.20/0.47      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u114,axiom,
% 0.20/0.47      (![X1, X0] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))))).
% 0.20/0.47  
% 0.20/0.47  % (11149)# SZS output end Saturation.
% 0.20/0.47  % (11149)------------------------------
% 0.20/0.47  % (11149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (11149)Termination reason: Satisfiable
% 0.20/0.47  
% 0.20/0.47  % (11149)Memory used [KB]: 6140
% 0.20/0.47  % (11149)Time elapsed: 0.061 s
% 0.20/0.47  % (11149)------------------------------
% 0.20/0.47  % (11149)------------------------------
% 0.20/0.47  % (11142)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (11138)Success in time 0.115 s
%------------------------------------------------------------------------------
