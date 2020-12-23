%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:57 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   39 (  39 expanded)
%              Number of leaves         :   39 (  39 expanded)
%              Depth                    :    0
%              Number of atoms          :   74 (  74 expanded)
%              Number of equality atoms :   49 (  49 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u231,axiom,(
    ! [X1,X0] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) )).

% (18484)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
tff(u230,axiom,(
    ! [X1,X0] :
      ( k4_xboole_0(X0,X1) != k3_tarski(k2_tarski(X0,X1))
      | r1_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ) )).

tff(u229,axiom,(
    ! [X1,X2] :
      ( k3_tarski(k2_tarski(X1,X2)) != k4_xboole_0(X2,X1)
      | r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1) ) )).

tff(u228,negated_conjecture,
    ( ~ ( sK1 != k2_struct_0(sK0) )
    | sK1 != k2_struct_0(sK0) )).

tff(u227,negated_conjecture,
    ( ~ ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )
    | sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u226,negated_conjecture,
    ( ~ ( sK2 != k2_struct_0(sK0) )
    | sK2 != k2_struct_0(sK0) )).

tff(u225,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) )).

tff(u224,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) )).

tff(u223,axiom,(
    ! [X3,X2] : k4_xboole_0(X2,X3) = k7_subset_1(X2,X2,X3) )).

tff(u222,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X1] : k7_subset_1(u1_struct_0(sK0),sK2,X1) = k4_xboole_0(sK2,X1) )).

tff(u221,axiom,(
    ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

tff(u220,axiom,(
    ! [X0] : k3_tarski(k2_tarski(X0,X0)) = k4_subset_1(X0,X0,X0) )).

tff(u219,negated_conjecture,
    ( k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) != k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))
    | k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

tff(u218,negated_conjecture,
    ( k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) != k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))
    | k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

tff(u217,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u216,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) != k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) )).

tff(u215,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) != k3_tarski(k2_tarski(sK2,u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) )).

tff(u214,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) != k3_tarski(k2_tarski(sK1,sK1))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1)) )).

tff(u213,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) != k3_tarski(k2_tarski(sK2,sK2))
    | k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k3_tarski(k2_tarski(sK2,sK2)) )).

tff(u212,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

tff(u211,negated_conjecture,
    ( k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK1,sK2)
    | k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

tff(u210,negated_conjecture,
    ( k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK2,sK1)
    | k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

tff(u209,negated_conjecture,
    ( k2_struct_0(sK0) != k3_tarski(k2_tarski(sK1,sK2))
    | k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2)) )).

tff(u208,negated_conjecture,
    ( sK1 != k4_xboole_0(sK1,sK2)
    | sK1 = k4_xboole_0(sK1,sK2) )).

tff(u207,negated_conjecture,
    ( sK1 != k4_xboole_0(k2_struct_0(sK0),sK2)
    | sK1 = k4_xboole_0(k2_struct_0(sK0),sK2) )).

tff(u206,negated_conjecture,
    ( sK2 != k4_xboole_0(sK2,sK1)
    | sK2 = k4_xboole_0(sK2,sK1) )).

tff(u205,negated_conjecture,
    ( sK2 != k4_xboole_0(k2_struct_0(sK0),sK1)
    | sK2 = k4_xboole_0(k2_struct_0(sK0),sK1) )).

tff(u204,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) )).

tff(u203,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) )).

tff(u202,negated_conjecture,
    ( ~ r1_xboole_0(sK1,sK2)
    | r1_xboole_0(sK1,sK2) )).

tff(u201,negated_conjecture,
    ( ~ r1_xboole_0(sK2,sK1)
    | r1_xboole_0(sK2,sK1) )).

tff(u200,axiom,(
    ! [X3,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | k3_tarski(k2_tarski(X3,X2)) = k4_subset_1(X3,X3,X2) ) )).

tff(u199,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) ) )).

tff(u198,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) )).

tff(u197,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK2,X1) = k3_tarski(k2_tarski(sK2,X1)) ) )).

tff(u196,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0)) ) )).

tff(u195,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u194,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u193,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:58:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.52  % (18470)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (18492)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (18474)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (18491)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (18485)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  % (18473)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (18474)Refutation not found, incomplete strategy% (18474)------------------------------
% 0.22/0.53  % (18474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (18471)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (18483)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (18477)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (18476)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (18473)Refutation not found, incomplete strategy% (18473)------------------------------
% 0.22/0.53  % (18473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (18473)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (18473)Memory used [KB]: 6268
% 0.22/0.53  % (18473)Time elapsed: 0.127 s
% 0.22/0.53  % (18473)------------------------------
% 0.22/0.53  % (18473)------------------------------
% 0.22/0.54  % (18469)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (18469)Refutation not found, incomplete strategy% (18469)------------------------------
% 0.22/0.54  % (18469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18477)Refutation not found, incomplete strategy% (18477)------------------------------
% 0.22/0.54  % (18477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18499)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.54  % (18485)# SZS output start Saturation.
% 0.22/0.54  tff(u231,axiom,
% 0.22/0.54      (![X1, X0] : (((k4_xboole_0(X0,X1) != X0) | r1_xboole_0(X0,X1))))).
% 0.22/0.54  
% 0.22/0.54  % (18484)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  tff(u230,axiom,
% 0.22/0.54      (![X1, X0] : (((k4_xboole_0(X0,X1) != k3_tarski(k2_tarski(X0,X1))) | r1_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))))).
% 0.22/0.54  
% 0.22/0.54  tff(u229,axiom,
% 0.22/0.54      (![X1, X2] : (((k3_tarski(k2_tarski(X1,X2)) != k4_xboole_0(X2,X1)) | r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1))))).
% 0.22/0.54  
% 0.22/0.54  tff(u228,negated_conjecture,
% 0.22/0.54      ((~(sK1 != k2_struct_0(sK0))) | (sK1 != k2_struct_0(sK0)))).
% 0.22/0.54  
% 0.22/0.54  tff(u227,negated_conjecture,
% 0.22/0.54      ((~(sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 0.22/0.54  
% 0.22/0.54  tff(u226,negated_conjecture,
% 0.22/0.54      ((~(sK2 != k2_struct_0(sK0))) | (sK2 != k2_struct_0(sK0)))).
% 0.22/0.54  
% 0.22/0.54  tff(u225,axiom,
% 0.22/0.54      (![X1, X0] : ((k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))))).
% 0.22/0.54  
% 0.22/0.54  tff(u224,axiom,
% 0.22/0.54      (![X1, X0] : ((k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))))).
% 0.22/0.54  
% 0.22/0.54  tff(u223,axiom,
% 0.22/0.54      (![X3, X2] : ((k4_xboole_0(X2,X3) = k7_subset_1(X2,X2,X3))))).
% 0.22/0.54  
% 0.22/0.54  tff(u222,negated_conjecture,
% 0.22/0.54      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X1] : ((k7_subset_1(u1_struct_0(sK0),sK2,X1) = k4_xboole_0(sK2,X1)))))).
% 0.22/0.54  
% 0.22/0.54  tff(u221,axiom,
% 0.22/0.54      (![X1, X0] : ((k2_tarski(X0,X1) = k2_tarski(X1,X0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u220,axiom,
% 0.22/0.54      (![X0] : ((k3_tarski(k2_tarski(X0,X0)) = k4_subset_1(X0,X0,X0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u219,negated_conjecture,
% 0.22/0.54      ((~(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)))) | (k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u218,negated_conjecture,
% 0.22/0.54      ((~(k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)))) | (k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u217,axiom,
% 0.22/0.54      (![X0] : ((k2_subset_1(X0) = X0)))).
% 0.22/0.54  
% 0.22/0.54  tff(u216,negated_conjecture,
% 0.22/0.54      ((~(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))))) | (k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))))).
% 0.22/0.54  
% 0.22/0.54  tff(u215,negated_conjecture,
% 0.22/0.54      ((~(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))))) | (k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0)))))).
% 0.22/0.54  
% 0.22/0.54  tff(u214,negated_conjecture,
% 0.22/0.54      ((~(k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1)))) | (k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1))))).
% 0.22/0.54  
% 0.22/0.54  tff(u213,negated_conjecture,
% 0.22/0.54      ((~(k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k3_tarski(k2_tarski(sK2,sK2)))) | (k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k3_tarski(k2_tarski(sK2,sK2))))).
% 0.22/0.54  
% 0.22/0.54  tff(u212,negated_conjecture,
% 0.22/0.54      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)))))).
% 0.22/0.54  
% 0.22/0.54  tff(u211,negated_conjecture,
% 0.22/0.54      ((~(k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | (k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)))).
% 0.22/0.54  
% 0.22/0.54  tff(u210,negated_conjecture,
% 0.22/0.54      ((~(k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1))) | (k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)))).
% 0.22/0.54  
% 0.22/0.54  tff(u209,negated_conjecture,
% 0.22/0.54      ((~(k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2)))) | (k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2))))).
% 0.22/0.54  
% 0.22/0.54  tff(u208,negated_conjecture,
% 0.22/0.54      ((~(sK1 = k4_xboole_0(sK1,sK2))) | (sK1 = k4_xboole_0(sK1,sK2)))).
% 0.22/0.54  
% 0.22/0.54  tff(u207,negated_conjecture,
% 0.22/0.54      ((~(sK1 = k4_xboole_0(k2_struct_0(sK0),sK2))) | (sK1 = k4_xboole_0(k2_struct_0(sK0),sK2)))).
% 0.22/0.54  
% 0.22/0.54  tff(u206,negated_conjecture,
% 0.22/0.54      ((~(sK2 = k4_xboole_0(sK2,sK1))) | (sK2 = k4_xboole_0(sK2,sK1)))).
% 0.22/0.54  
% 0.22/0.54  tff(u205,negated_conjecture,
% 0.22/0.54      ((~(sK2 = k4_xboole_0(k2_struct_0(sK0),sK1))) | (sK2 = k4_xboole_0(k2_struct_0(sK0),sK1)))).
% 0.22/0.54  
% 0.22/0.54  tff(u204,axiom,
% 0.22/0.54      (![X1, X0] : ((~r1_xboole_0(X0,X1) | (k4_xboole_0(X0,X1) = X0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u203,axiom,
% 0.22/0.54      (![X1, X0] : ((~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u202,negated_conjecture,
% 0.22/0.54      ((~r1_xboole_0(sK1,sK2)) | r1_xboole_0(sK1,sK2))).
% 0.22/0.54  
% 0.22/0.54  tff(u201,negated_conjecture,
% 0.22/0.54      ((~r1_xboole_0(sK2,sK1)) | r1_xboole_0(sK2,sK1))).
% 0.22/0.54  
% 0.22/0.54  tff(u200,axiom,
% 0.22/0.54      (![X3, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(X3)) | (k3_tarski(k2_tarski(X3,X2)) = k4_subset_1(X3,X3,X2)))))).
% 0.22/0.54  
% 0.22/0.54  tff(u199,axiom,
% 0.22/0.54      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | (k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))))))).
% 0.22/0.54  
% 0.22/0.54  tff(u198,axiom,
% 0.22/0.54      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)))))).
% 0.22/0.54  
% 0.22/0.54  tff(u197,negated_conjecture,
% 0.22/0.54      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | (k4_subset_1(u1_struct_0(sK0),sK2,X1) = k3_tarski(k2_tarski(sK2,X1)))))))).
% 0.22/0.54  
% 0.22/0.54  tff(u196,negated_conjecture,
% 0.22/0.54      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | (k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0)))))))).
% 0.22/0.54  
% 0.22/0.54  tff(u195,negated_conjecture,
% 0.22/0.54      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u194,negated_conjecture,
% 0.22/0.54      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u193,axiom,
% 0.22/0.54      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 0.22/0.54  
% 0.22/0.54  % (18485)# SZS output end Saturation.
% 0.22/0.54  % (18485)------------------------------
% 0.22/0.54  % (18485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18485)Termination reason: Satisfiable
% 0.22/0.54  
% 0.22/0.54  % (18485)Memory used [KB]: 10874
% 0.22/0.54  % (18485)Time elapsed: 0.120 s
% 0.22/0.54  % (18485)------------------------------
% 0.22/0.54  % (18485)------------------------------
% 0.22/0.54  % (18484)Refutation not found, incomplete strategy% (18484)------------------------------
% 0.22/0.54  % (18484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18484)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (18484)Memory used [KB]: 6140
% 0.22/0.54  % (18484)Time elapsed: 0.002 s
% 0.22/0.54  % (18484)------------------------------
% 0.22/0.54  % (18484)------------------------------
% 0.22/0.54  % (18475)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (18477)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (18477)Memory used [KB]: 10746
% 0.22/0.54  % (18468)Success in time 0.179 s
%------------------------------------------------------------------------------
