%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:42 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  38 expanded)
%              Number of leaves         :   38 (  38 expanded)
%              Depth                    :    0
%              Number of atoms          :   65 (  65 expanded)
%              Number of equality atoms :   29 (  29 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u222,negated_conjecture,
    ( ~ ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

tff(u221,negated_conjecture,
    ( ~ ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )
    | k1_xboole_0 != k7_subset_1(sK1,sK1,sK1) )).

tff(u220,negated_conjecture,
    ( ~ ( k2_struct_0(sK0) != sK1 )
    | k2_struct_0(sK0) != sK1 )).

tff(u219,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u218,axiom,(
    ! [X1,X0] : k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X0,X0,X1) )).

tff(u217,axiom,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) )).

tff(u216,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u215,axiom,(
    ! [X0] : k1_xboole_0 = k7_subset_1(X0,k1_xboole_0,k1_xboole_0) )).

tff(u214,axiom,(
    ! [X1,X2] : k7_subset_1(X1,k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X2))) )).

tff(u213,axiom,(
    ! [X1,X0,X2] : k7_subset_1(X1,k1_xboole_0,X0) = k7_subset_1(X2,k1_xboole_0,X0) )).

tff(u212,negated_conjecture,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

tff(u211,axiom,(
    ! [X0] : k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

tff(u210,negated_conjecture,(
    u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

tff(u209,negated_conjecture,(
    sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

tff(u208,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) )).

tff(u207,axiom,(
    ! [X3,X5,X4] :
      ( ~ r1_tarski(X4,X3)
      | k7_subset_1(X3,X4,X5) = k7_subset_1(X4,X4,X5) ) )).

tff(u206,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) )).

tff(u205,axiom,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) )).

tff(u204,axiom,(
    ! [X1,X2] :
      ( ~ r1_tarski(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2 ) )).

tff(u203,negated_conjecture,
    ( ~ ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )
    | ~ r1_tarski(k7_subset_1(sK1,sK1,sK1),k1_xboole_0) )).

tff(u202,negated_conjecture,
    ( ~ ~ r1_tarski(u1_struct_0(sK0),sK1)
    | ~ r1_tarski(u1_struct_0(sK0),sK1) )).

tff(u201,negated_conjecture,
    ( ~ ~ r1_tarski(k2_struct_0(sK0),sK1)
    | ~ r1_tarski(k2_struct_0(sK0),sK1) )).

tff(u200,axiom,(
    ! [X1] : r1_tarski(X1,X1) )).

tff(u199,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) )).

tff(u198,negated_conjecture,(
    r1_tarski(sK1,u1_struct_0(sK0)) )).

tff(u197,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) ) )).

tff(u196,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) )).

tff(u195,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) )).

tff(u194,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
      | ~ l1_struct_0(X0) ) )).

tff(u193,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u192,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

tff(u191,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) )).

tff(u190,negated_conjecture,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK1) ) )).

tff(u189,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | m1_subset_1(X1,X2) ) )).

tff(u188,axiom,(
    ! [X3,X5,X4] :
      ( ~ r2_hidden(X3,X5)
      | m1_subset_1(X3,X4)
      | ~ r1_tarski(X5,X4) ) )).

tff(u187,axiom,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0))) ) )).

tff(u186,axiom,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k1_xboole_0)) ) )).

tff(u185,negated_conjecture,(
    l1_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:30:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (795)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (818)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.51  % (803)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.51  % (796)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (793)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (818)Refutation not found, incomplete strategy% (818)------------------------------
% 0.21/0.52  % (818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (803)Refutation not found, incomplete strategy% (803)------------------------------
% 0.21/0.52  % (803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (803)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (803)Memory used [KB]: 10618
% 0.21/0.52  % (803)Time elapsed: 0.100 s
% 0.21/0.52  % (803)------------------------------
% 0.21/0.52  % (803)------------------------------
% 0.21/0.52  % (818)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (818)Memory used [KB]: 6140
% 0.21/0.52  % (818)Time elapsed: 0.097 s
% 0.21/0.52  % (818)------------------------------
% 0.21/0.52  % (818)------------------------------
% 0.21/0.52  % (805)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (805)Refutation not found, incomplete strategy% (805)------------------------------
% 0.21/0.52  % (805)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (805)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (805)Memory used [KB]: 1663
% 0.21/0.52  % (805)Time elapsed: 0.109 s
% 0.21/0.52  % (805)------------------------------
% 0.21/0.52  % (805)------------------------------
% 0.21/0.52  % (811)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (792)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (792)Refutation not found, incomplete strategy% (792)------------------------------
% 0.21/0.52  % (792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (792)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (792)Memory used [KB]: 1663
% 0.21/0.52  % (792)Time elapsed: 0.108 s
% 0.21/0.52  % (792)------------------------------
% 0.21/0.52  % (792)------------------------------
% 0.21/0.53  % (804)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (797)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (791)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (819)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (817)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (816)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (796)Refutation not found, incomplete strategy% (796)------------------------------
% 0.21/0.54  % (796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (796)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (796)Memory used [KB]: 1791
% 0.21/0.54  % (796)Time elapsed: 0.128 s
% 0.21/0.54  % (796)------------------------------
% 0.21/0.54  % (796)------------------------------
% 0.21/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.54  % (797)# SZS output start Saturation.
% 0.21/0.54  tff(u222,negated_conjecture,
% 0.21/0.54      ((~(k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1))) | (k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)))).
% 0.21/0.54  
% 0.21/0.54  tff(u221,negated_conjecture,
% 0.21/0.54      ((~(k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1))) | (k1_xboole_0 != k7_subset_1(sK1,sK1,sK1)))).
% 0.21/0.54  
% 0.21/0.54  tff(u220,negated_conjecture,
% 0.21/0.54      ((~(k2_struct_0(sK0) != sK1)) | (k2_struct_0(sK0) != sK1))).
% 0.21/0.54  
% 0.21/0.54  tff(u219,axiom,
% 0.21/0.54      (![X0] : ((k5_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u218,axiom,
% 0.21/0.54      (![X1, X0] : ((k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X0,X0,X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u217,axiom,
% 0.21/0.54      (![X0] : ((k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u216,negated_conjecture,
% 0.21/0.54      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 0.21/0.54  
% 0.21/0.54  tff(u215,axiom,
% 0.21/0.54      (![X0] : ((k1_xboole_0 = k7_subset_1(X0,k1_xboole_0,k1_xboole_0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u214,axiom,
% 0.21/0.54      (![X1, X2] : ((k7_subset_1(X1,k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X2))))))).
% 0.21/0.54  
% 0.21/0.54  tff(u213,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((k7_subset_1(X1,k1_xboole_0,X0) = k7_subset_1(X2,k1_xboole_0,X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u212,negated_conjecture,
% 0.21/0.54      (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u211,axiom,
% 0.21/0.54      (![X0] : ((k7_subset_1(X0,X0,k1_xboole_0) = X0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u210,negated_conjecture,
% 0.21/0.54      (u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u209,negated_conjecture,
% 0.21/0.54      (sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0))).
% 0.21/0.54  
% 0.21/0.54  tff(u208,negated_conjecture,
% 0.21/0.54      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u207,axiom,
% 0.21/0.54      (![X3, X5, X4] : ((~r1_tarski(X4,X3) | (k7_subset_1(X3,X4,X5) = k7_subset_1(X4,X4,X5)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u206,axiom,
% 0.21/0.54      (![X1, X0] : ((~r1_tarski(X1,X0) | (X0 = X1) | ~r1_tarski(X0,X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u205,axiom,
% 0.21/0.54      (![X1] : ((~r1_tarski(X1,k1_xboole_0) | (k1_xboole_0 = X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u204,axiom,
% 0.21/0.54      (![X1, X2] : ((~r1_tarski(X2,u1_struct_0(X1)) | ~l1_struct_0(X1) | (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u203,negated_conjecture,
% 0.21/0.54      ((~(k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1))) | ~r1_tarski(k7_subset_1(sK1,sK1,sK1),k1_xboole_0))).
% 0.21/0.54  
% 0.21/0.54  tff(u202,negated_conjecture,
% 0.21/0.54      ((~~r1_tarski(u1_struct_0(sK0),sK1)) | ~r1_tarski(u1_struct_0(sK0),sK1))).
% 0.21/0.54  
% 0.21/0.54  tff(u201,negated_conjecture,
% 0.21/0.54      ((~~r1_tarski(k2_struct_0(sK0),sK1)) | ~r1_tarski(k2_struct_0(sK0),sK1))).
% 0.21/0.54  
% 0.21/0.54  tff(u200,axiom,
% 0.21/0.54      (![X1] : (r1_tarski(X1,X1)))).
% 0.21/0.54  
% 0.21/0.54  tff(u199,axiom,
% 0.21/0.54      (![X0] : (r1_tarski(k1_xboole_0,X0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u198,negated_conjecture,
% 0.21/0.54      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.21/0.54  
% 0.21/0.54  tff(u197,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u196,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u195,axiom,
% 0.21/0.54      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u194,axiom,
% 0.21/0.54      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1) | ~l1_struct_0(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u193,negated_conjecture,
% 0.21/0.54      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u192,axiom,
% 0.21/0.54      (![X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u191,axiom,
% 0.21/0.54      (![X1, X0] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u190,negated_conjecture,
% 0.21/0.54      (![X0] : ((m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u189,axiom,
% 0.21/0.54      (![X1, X2] : ((~r2_hidden(X1,k1_xboole_0) | m1_subset_1(X1,X2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u188,axiom,
% 0.21/0.54      (![X3, X5, X4] : ((~r2_hidden(X3,X5) | m1_subset_1(X3,X4) | ~r1_tarski(X5,X4))))).
% 0.21/0.54  
% 0.21/0.54  tff(u187,axiom,
% 0.21/0.54      (![X0] : ((~l1_struct_0(X0) | (u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0)))))))).
% 0.21/0.54  
% 0.21/0.54  tff(u186,axiom,
% 0.21/0.54      (![X0] : ((~l1_struct_0(X0) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k1_xboole_0))))))).
% 0.21/0.54  
% 0.21/0.54  tff(u185,negated_conjecture,
% 0.21/0.54      l1_struct_0(sK0)).
% 0.21/0.54  
% 0.21/0.54  % (797)# SZS output end Saturation.
% 0.21/0.54  % (797)------------------------------
% 0.21/0.54  % (797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (797)Termination reason: Satisfiable
% 0.21/0.54  
% 0.21/0.54  % (797)Memory used [KB]: 10746
% 0.21/0.54  % (797)Time elapsed: 0.121 s
% 0.21/0.54  % (797)------------------------------
% 0.21/0.54  % (797)------------------------------
% 0.21/0.54  % (794)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (816)Refutation not found, incomplete strategy% (816)------------------------------
% 0.21/0.54  % (816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (816)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (816)Memory used [KB]: 6140
% 0.21/0.54  % (816)Time elapsed: 0.131 s
% 0.21/0.54  % (816)------------------------------
% 0.21/0.54  % (816)------------------------------
% 0.21/0.54  % (790)Success in time 0.173 s
%------------------------------------------------------------------------------
