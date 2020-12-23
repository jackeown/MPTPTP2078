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
% DateTime   : Thu Dec  3 13:08:42 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   30 (  30 expanded)
%              Number of leaves         :   30 (  30 expanded)
%              Depth                    :    0
%              Number of atoms          :   55 (  55 expanded)
%              Number of equality atoms :   28 (  28 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u259,negated_conjecture,
    ( ~ ( u1_struct_0(sK0) != sK1 )
    | u1_struct_0(sK0) != sK1 )).

tff(u258,negated_conjecture,
    ( ~ ( k2_struct_0(sK0) != sK1 )
    | k2_struct_0(sK0) != sK1 )).

tff(u257,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u256,axiom,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) )).

tff(u255,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u254,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

tff(u253,axiom,(
    ! [X0] : k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

tff(u252,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) )).

tff(u251,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

tff(u250,axiom,(
    ! [X1,X0] : k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k7_subset_1(X0,X0,k7_subset_1(X0,X0,X1))) )).

tff(u249,axiom,(
    ! [X0] : k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

tff(u248,axiom,(
    ! [X1,X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k7_subset_1(X0,X0,k7_subset_1(X0,X0,X1)) )).

tff(u247,negated_conjecture,
    ( u1_struct_0(sK0) != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

tff(u246,negated_conjecture,
    ( sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) )).

tff(u245,negated_conjecture,
    ( sK1 != k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)
    | sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

tff(u244,axiom,(
    ! [X1,X3,X2] :
      ( ~ r1_tarski(X2,X1)
      | k7_subset_1(X1,X2,X3) = k7_subset_1(X2,X2,X3) ) )).

tff(u243,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) )).

tff(u242,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 ) )).

tff(u241,negated_conjecture,
    ( ~ ~ r1_tarski(u1_struct_0(sK0),sK1)
    | ~ r1_tarski(u1_struct_0(sK0),sK1) )).

tff(u240,axiom,(
    ! [X1] : r1_tarski(X1,X1) )).

tff(u239,negated_conjecture,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | r1_tarski(sK1,u1_struct_0(sK0)) )).

tff(u238,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) ) )).

tff(u237,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) )).

tff(u236,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 ) )).

tff(u235,negated_conjecture,
    ( ~ ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(sK1)) )).

tff(u234,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u233,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) )).

tff(u232,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u231,axiom,(
    ! [X1,X0] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) )).

tff(u230,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:23:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (15740)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.51  % (15732)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (15748)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (15756)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.52  % (15740)Refutation not found, incomplete strategy% (15740)------------------------------
% 0.21/0.52  % (15740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15740)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15740)Memory used [KB]: 10618
% 0.21/0.52  % (15740)Time elapsed: 0.101 s
% 0.21/0.52  % (15740)------------------------------
% 0.21/0.52  % (15740)------------------------------
% 0.21/0.52  % (15742)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (15741)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (15744)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.52  % (15742)Refutation not found, incomplete strategy% (15742)------------------------------
% 0.21/0.52  % (15742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15742)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15742)Memory used [KB]: 1663
% 0.21/0.52  % (15742)Time elapsed: 0.076 s
% 0.21/0.52  % (15742)------------------------------
% 0.21/0.52  % (15742)------------------------------
% 0.21/0.52  % (15750)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (15756)Refutation not found, incomplete strategy% (15756)------------------------------
% 0.21/0.53  % (15756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15739)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (15756)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (15756)Memory used [KB]: 10746
% 0.21/0.53  % (15756)Time elapsed: 0.114 s
% 0.21/0.53  % (15756)------------------------------
% 0.21/0.53  % (15756)------------------------------
% 0.21/0.53  % (15728)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (15750)Refutation not found, incomplete strategy% (15750)------------------------------
% 0.21/0.53  % (15750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15750)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (15750)Memory used [KB]: 6268
% 0.21/0.53  % (15750)Time elapsed: 0.079 s
% 0.21/0.53  % (15750)------------------------------
% 0.21/0.53  % (15750)------------------------------
% 0.21/0.53  % (15730)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.53  % (15748)# SZS output start Saturation.
% 0.21/0.53  tff(u259,negated_conjecture,
% 0.21/0.53      ((~(u1_struct_0(sK0) != sK1)) | (u1_struct_0(sK0) != sK1))).
% 0.21/0.53  
% 0.21/0.53  tff(u258,negated_conjecture,
% 0.21/0.53      ((~(k2_struct_0(sK0) != sK1)) | (k2_struct_0(sK0) != sK1))).
% 0.21/0.53  
% 0.21/0.53  tff(u257,axiom,
% 0.21/0.53      (![X0] : ((k5_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.21/0.53  
% 0.21/0.53  tff(u256,axiom,
% 0.21/0.53      (![X0] : ((k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)))))).
% 0.21/0.53  
% 0.21/0.53  tff(u255,negated_conjecture,
% 0.21/0.53      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 0.21/0.53  
% 0.21/0.53  tff(u254,negated_conjecture,
% 0.21/0.53      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)))).
% 0.21/0.53  
% 0.21/0.53  tff(u253,axiom,
% 0.21/0.53      (![X0] : ((k1_xboole_0 = k7_subset_1(X0,X0,X0))))).
% 0.21/0.53  
% 0.21/0.53  tff(u252,axiom,
% 0.21/0.53      (![X0] : ((k1_xboole_0 = k5_xboole_0(X0,X0))))).
% 0.21/0.53  
% 0.21/0.53  tff(u251,negated_conjecture,
% 0.21/0.53      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)))))).
% 0.21/0.53  
% 0.21/0.53  tff(u250,axiom,
% 0.21/0.53      (![X1, X0] : ((k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k7_subset_1(X0,X0,k7_subset_1(X0,X0,X1))))))).
% 0.21/0.53  
% 0.21/0.53  tff(u249,axiom,
% 0.21/0.53      (![X0] : ((k7_subset_1(X0,X0,k1_xboole_0) = X0)))).
% 0.21/0.53  
% 0.21/0.53  tff(u248,axiom,
% 0.21/0.53      (![X1, X0] : ((k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k7_subset_1(X0,X0,k7_subset_1(X0,X0,X1)))))).
% 0.21/0.53  
% 0.21/0.53  tff(u247,negated_conjecture,
% 0.21/0.53      ((~(u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))))) | (u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))))).
% 0.21/0.53  
% 0.21/0.53  tff(u246,negated_conjecture,
% 0.21/0.53      ((~(sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0))) | (sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)))).
% 0.21/0.53  
% 0.21/0.53  tff(u245,negated_conjecture,
% 0.21/0.53      ((~(sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0))) | (sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)))).
% 0.21/0.53  
% 0.21/0.53  tff(u244,axiom,
% 0.21/0.53      (![X1, X3, X2] : ((~r1_tarski(X2,X1) | (k7_subset_1(X1,X2,X3) = k7_subset_1(X2,X2,X3)))))).
% 0.21/0.53  
% 0.21/0.53  tff(u243,axiom,
% 0.21/0.53      (![X1, X0] : ((~r1_tarski(X1,X0) | (X0 = X1) | ~r1_tarski(X0,X1))))).
% 0.21/0.53  
% 0.21/0.53  tff(u242,negated_conjecture,
% 0.21/0.53      ((~l1_struct_0(sK0)) | (![X0] : ((~r1_tarski(X0,u1_struct_0(sK0)) | (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0)))))).
% 0.21/0.53  
% 0.21/0.53  tff(u241,negated_conjecture,
% 0.21/0.53      ((~~r1_tarski(u1_struct_0(sK0),sK1)) | ~r1_tarski(u1_struct_0(sK0),sK1))).
% 0.21/0.53  
% 0.21/0.53  tff(u240,axiom,
% 0.21/0.53      (![X1] : (r1_tarski(X1,X1)))).
% 0.21/0.53  
% 0.21/0.53  tff(u239,negated_conjecture,
% 0.21/0.53      ((~r1_tarski(sK1,u1_struct_0(sK0))) | r1_tarski(sK1,u1_struct_0(sK0)))).
% 0.21/0.53  
% 0.21/0.53  tff(u238,axiom,
% 0.21/0.53      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)))))).
% 0.21/0.53  
% 0.21/0.53  tff(u237,axiom,
% 0.21/0.53      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))).
% 0.21/0.53  
% 0.21/0.53  tff(u236,negated_conjecture,
% 0.21/0.53      ((~l1_struct_0(sK0)) | (![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0)))))).
% 0.21/0.53  
% 0.21/0.53  tff(u235,negated_conjecture,
% 0.21/0.53      ((~~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(sK1))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(sK1)))).
% 0.21/0.53  
% 0.21/0.53  tff(u234,negated_conjecture,
% 0.21/0.53      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.21/0.53  
% 0.21/0.53  tff(u233,axiom,
% 0.21/0.53      (![X1, X0] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))))).
% 0.21/0.53  
% 0.21/0.53  tff(u232,axiom,
% 0.21/0.53      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 0.21/0.53  
% 0.21/0.53  tff(u231,axiom,
% 0.21/0.53      (![X1, X0] : ((~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))))).
% 0.21/0.53  
% 0.21/0.53  tff(u230,negated_conjecture,
% 0.21/0.53      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 0.21/0.53  
% 0.21/0.53  % (15748)# SZS output end Saturation.
% 0.21/0.53  % (15748)------------------------------
% 0.21/0.53  % (15748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15748)Termination reason: Satisfiable
% 0.21/0.53  
% 0.21/0.53  % (15748)Memory used [KB]: 10874
% 0.21/0.53  % (15748)Time elapsed: 0.118 s
% 0.21/0.53  % (15748)------------------------------
% 0.21/0.53  % (15748)------------------------------
% 0.21/0.53  % (15731)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (15752)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (15727)Success in time 0.17 s
%------------------------------------------------------------------------------
