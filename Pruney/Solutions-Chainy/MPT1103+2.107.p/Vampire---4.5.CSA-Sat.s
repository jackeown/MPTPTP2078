%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:48 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of leaves         :   27 (  27 expanded)
%              Depth                    :    0
%              Number of atoms          :   45 (  45 expanded)
%              Number of equality atoms :   29 (  29 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u163,negated_conjecture,
    ( ~ ( sK1 != k2_struct_0(sK0) )
    | sK1 != k2_struct_0(sK0) )).

tff(u162,axiom,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 )).

tff(u161,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u160,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X1,X1,X2) )).

tff(u159,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

tff(u158,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) )).

tff(u157,axiom,(
    ! [X1] : k1_xboole_0 = k7_subset_1(X1,X1,X1) )).

tff(u156,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

tff(u155,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u154,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(sK1,sK1,u1_struct_0(sK0))
    | k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0)) )).

tff(u153,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u152,axiom,(
    ! [X0] : k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

tff(u151,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

tff(u150,negated_conjecture,
    ( u1_struct_0(sK0) != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

tff(u149,negated_conjecture,
    ( sK1 != k3_xboole_0(sK1,u1_struct_0(sK0))
    | sK1 = k3_xboole_0(sK1,u1_struct_0(sK0)) )).

tff(u148,negated_conjecture,
    ( sK1 != k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)
    | sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

tff(u147,negated_conjecture,
    ( sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) )).

tff(u146,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) )).

tff(u145,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u144,negated_conjecture,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | r1_tarski(sK1,u1_struct_0(sK0)) )).

tff(u143,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) ) )).

tff(u142,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) )).

tff(u141,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) )).

tff(u140,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u139,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u138,axiom,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0))) ) )).

tff(u137,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:21:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.48  % (21776)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.49  % (21783)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.49  % (21784)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (21776)Refutation not found, incomplete strategy% (21776)------------------------------
% 0.20/0.50  % (21776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (21776)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (21776)Memory used [KB]: 1663
% 0.20/0.50  % (21776)Time elapsed: 0.096 s
% 0.20/0.50  % (21776)------------------------------
% 0.20/0.50  % (21776)------------------------------
% 0.20/0.50  % (21792)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.50  % (21780)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (21791)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.50  % (21791)Refutation not found, incomplete strategy% (21791)------------------------------
% 0.20/0.50  % (21791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (21791)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (21791)Memory used [KB]: 6140
% 0.20/0.50  % (21791)Time elapsed: 0.002 s
% 0.20/0.50  % (21791)------------------------------
% 0.20/0.50  % (21791)------------------------------
% 0.20/0.50  % (21780)Refutation not found, incomplete strategy% (21780)------------------------------
% 0.20/0.50  % (21780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (21780)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (21780)Memory used [KB]: 6140
% 0.20/0.50  % (21780)Time elapsed: 0.102 s
% 0.20/0.50  % (21780)------------------------------
% 0.20/0.50  % (21780)------------------------------
% 0.20/0.50  % (21790)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (21784)Refutation not found, incomplete strategy% (21784)------------------------------
% 0.20/0.50  % (21784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (21784)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (21784)Memory used [KB]: 10618
% 0.20/0.50  % (21784)Time elapsed: 0.103 s
% 0.20/0.50  % (21784)------------------------------
% 0.20/0.50  % (21784)------------------------------
% 0.20/0.50  % (21781)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (21779)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.50  % (21792)# SZS output start Saturation.
% 0.20/0.50  tff(u163,negated_conjecture,
% 0.20/0.50      ((~(sK1 != k2_struct_0(sK0))) | (sK1 != k2_struct_0(sK0)))).
% 0.20/0.50  
% 0.20/0.50  tff(u162,axiom,
% 0.20/0.50      (![X0] : ((k3_xboole_0(X0,X0) = X0)))).
% 0.20/0.50  
% 0.20/0.50  tff(u161,axiom,
% 0.20/0.50      (![X0] : ((k5_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.20/0.50  
% 0.20/0.50  tff(u160,axiom,
% 0.20/0.50      (![X1, X2] : ((k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X1,X1,X2))))).
% 0.20/0.50  
% 0.20/0.50  tff(u159,axiom,
% 0.20/0.50      (![X0] : ((k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u158,axiom,
% 0.20/0.50      (![X0] : ((k1_xboole_0 = k5_xboole_0(X0,X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u157,axiom,
% 0.20/0.50      (![X1] : ((k1_xboole_0 = k7_subset_1(X1,X1,X1))))).
% 0.20/0.50  
% 0.20/0.50  tff(u156,negated_conjecture,
% 0.20/0.50      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)))).
% 0.20/0.50  
% 0.20/0.50  tff(u155,negated_conjecture,
% 0.20/0.50      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 0.20/0.50  
% 0.20/0.50  tff(u154,negated_conjecture,
% 0.20/0.50      ((~(k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0)))) | (k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u153,axiom,
% 0.20/0.50      (![X0] : ((k2_subset_1(X0) = X0)))).
% 0.20/0.50  
% 0.20/0.50  tff(u152,axiom,
% 0.20/0.50      (![X0] : ((k7_subset_1(X0,X0,k1_xboole_0) = X0)))).
% 0.20/0.50  
% 0.20/0.50  tff(u151,negated_conjecture,
% 0.20/0.50      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)))))).
% 0.20/0.50  
% 0.20/0.50  tff(u150,negated_conjecture,
% 0.20/0.50      ((~(u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))))) | (u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))))).
% 0.20/0.50  
% 0.20/0.50  tff(u149,negated_conjecture,
% 0.20/0.50      ((~(sK1 = k3_xboole_0(sK1,u1_struct_0(sK0)))) | (sK1 = k3_xboole_0(sK1,u1_struct_0(sK0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u148,negated_conjecture,
% 0.20/0.50      ((~(sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0))) | (sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)))).
% 0.20/0.50  
% 0.20/0.50  tff(u147,negated_conjecture,
% 0.20/0.50      ((~(sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0))) | (sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)))).
% 0.20/0.50  
% 0.20/0.50  tff(u146,axiom,
% 0.20/0.50      (![X1, X0] : ((~r1_tarski(X0,X1) | (k3_xboole_0(X0,X1) = X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u145,axiom,
% 0.20/0.50      (![X0] : (r1_tarski(X0,X0)))).
% 0.20/0.50  
% 0.20/0.50  tff(u144,negated_conjecture,
% 0.20/0.50      ((~r1_tarski(sK1,u1_struct_0(sK0))) | r1_tarski(sK1,u1_struct_0(sK0)))).
% 0.20/0.50  
% 0.20/0.50  tff(u143,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)))))).
% 0.20/0.50  
% 0.20/0.50  tff(u142,axiom,
% 0.20/0.50      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))).
% 0.20/0.50  
% 0.20/0.50  tff(u141,axiom,
% 0.20/0.50      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))))).
% 0.20/0.50  
% 0.20/0.50  tff(u140,negated_conjecture,
% 0.20/0.50      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u139,axiom,
% 0.20/0.50      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u138,axiom,
% 0.20/0.50      (![X0] : ((~l1_struct_0(X0) | (u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0)))))))).
% 0.20/0.50  
% 0.20/0.50  tff(u137,negated_conjecture,
% 0.20/0.50      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 0.20/0.50  
% 0.20/0.50  % (21792)# SZS output end Saturation.
% 0.20/0.50  % (21792)------------------------------
% 0.20/0.50  % (21792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (21792)Termination reason: Satisfiable
% 0.20/0.50  
% 0.20/0.50  % (21792)Memory used [KB]: 10746
% 0.20/0.50  % (21792)Time elapsed: 0.103 s
% 0.20/0.50  % (21792)------------------------------
% 0.20/0.50  % (21792)------------------------------
% 0.20/0.50  % (21781)Refutation not found, incomplete strategy% (21781)------------------------------
% 0.20/0.50  % (21781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (21781)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (21781)Memory used [KB]: 6268
% 0.20/0.50  % (21781)Time elapsed: 0.100 s
% 0.20/0.50  % (21781)------------------------------
% 0.20/0.50  % (21781)------------------------------
% 0.20/0.50  % (21777)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.50  % (21775)Success in time 0.151 s
%------------------------------------------------------------------------------
