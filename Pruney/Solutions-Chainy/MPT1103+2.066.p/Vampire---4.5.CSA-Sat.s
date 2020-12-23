%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:42 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 (  42 expanded)
%              Number of leaves         :   42 (  42 expanded)
%              Depth                    :    0
%              Number of atoms          :   62 (  62 expanded)
%              Number of equality atoms :   37 (  37 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u307,negated_conjecture,
    ( ~ ( k2_struct_0(sK0) != sK1 )
    | k2_struct_0(sK0) != sK1 )).

tff(u306,axiom,(
    ! [X1] : k3_xboole_0(X1,X1) = X1 )).

tff(u305,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u304,axiom,(
    ! [X3,X2] : k5_xboole_0(X2,k3_xboole_0(X2,X3)) = k7_subset_1(X2,X2,X3) )).

tff(u303,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

tff(u302,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) )).

tff(u301,axiom,(
    ! [X1,X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0)))) )).

tff(u300,axiom,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(X2,X2) )).

tff(u299,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

tff(u298,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u297,negated_conjecture,(
    k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

tff(u296,negated_conjecture,(
    ! [X1] : k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k7_subset_1(X1,X1,sK1))) )).

tff(u295,axiom,(
    ! [X1,X0] : k1_xboole_0 = k7_subset_1(X0,k1_xboole_0,X1) )).

tff(u294,axiom,(
    ! [X1] : k1_xboole_0 = k7_subset_1(X1,X1,X1) )).

tff(u293,negated_conjecture,(
    ! [X0] : k1_xboole_0 = k7_subset_1(X0,X0,k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))) )).

tff(u292,axiom,(
    ! [X3,X2] : k1_xboole_0 = k7_subset_1(X2,X2,k5_xboole_0(X2,k7_subset_1(X3,X3,X2))) )).

tff(u291,negated_conjecture,(
    k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0)) )).

tff(u290,negated_conjecture,(
    ! [X1] : k1_xboole_0 = k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k7_subset_1(X1,X1,sK1))) )).

tff(u289,axiom,(
    ! [X0] : k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

tff(u288,negated_conjecture,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

tff(u287,negated_conjecture,(
    u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

tff(u286,negated_conjecture,(
    sK1 = k3_xboole_0(sK1,u1_struct_0(sK0)) )).

tff(u285,negated_conjecture,(
    sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

tff(u284,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) )).

tff(u283,axiom,(
    ! [X1,X3,X2] :
      ( ~ r1_tarski(X2,X1)
      | k7_subset_1(X1,X2,X3) = k7_subset_1(X2,X2,X3) ) )).

tff(u282,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) )).

tff(u281,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) )).

tff(u280,axiom,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) )).

tff(u279,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) )).

% (983)Termination reason: Refutation not found, incomplete strategy

tff(u278,negated_conjecture,
    ( ~ ~ r1_tarski(u1_struct_0(sK0),sK1)
    | ~ r1_tarski(u1_struct_0(sK0),sK1) )).

% (983)Memory used [KB]: 1663
tff(u277,negated_conjecture,
    ( ~ ~ r1_tarski(k2_struct_0(sK0),sK1)
    | ~ r1_tarski(k2_struct_0(sK0),sK1) )).

% (983)Time elapsed: 0.109 s
tff(u276,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) )).

% (983)------------------------------
% (983)------------------------------
% (999)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
tff(u275,axiom,(
    ! [X1] : r1_tarski(X1,X1) )).

tff(u274,negated_conjecture,(
    r1_tarski(sK1,u1_struct_0(sK0)) )).

tff(u273,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) ) )).

tff(u272,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) )).

tff(u271,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
      | ~ l1_struct_0(X0) ) )).

tff(u270,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u269,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) )).

tff(u268,axiom,(
    ! [X1] :
      ( ~ l1_struct_0(X1)
      | u1_struct_0(X1) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),u1_struct_0(X1))) ) )).

tff(u267,axiom,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k1_xboole_0)) ) )).

tff(u266,negated_conjecture,(
    l1_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:32:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (975)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.51  % (969)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (994)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (971)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (973)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (994)Refutation not found, incomplete strategy% (994)------------------------------
% 0.21/0.51  % (994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (984)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (983)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (995)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (983)Refutation not found, incomplete strategy% (983)------------------------------
% 0.21/0.52  % (983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (975)# SZS output start Saturation.
% 0.21/0.52  tff(u307,negated_conjecture,
% 0.21/0.52      ((~(k2_struct_0(sK0) != sK1)) | (k2_struct_0(sK0) != sK1))).
% 0.21/0.52  
% 0.21/0.52  tff(u306,axiom,
% 0.21/0.52      (![X1] : ((k3_xboole_0(X1,X1) = X1)))).
% 0.21/0.52  
% 0.21/0.52  tff(u305,axiom,
% 0.21/0.52      (![X0] : ((k5_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.21/0.52  
% 0.21/0.52  tff(u304,axiom,
% 0.21/0.52      (![X3, X2] : ((k5_xboole_0(X2,k3_xboole_0(X2,X3)) = k7_subset_1(X2,X2,X3))))).
% 0.21/0.52  
% 0.21/0.52  tff(u303,axiom,
% 0.21/0.52      (![X0] : ((k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u302,axiom,
% 0.21/0.52      (![X0] : ((k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u301,axiom,
% 0.21/0.52      (![X1, X0] : ((k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0)))))))).
% 0.21/0.52  
% 0.21/0.52  tff(u300,axiom,
% 0.21/0.52      (![X2] : ((k1_xboole_0 = k5_xboole_0(X2,X2))))).
% 0.21/0.52  
% 0.21/0.52  tff(u299,negated_conjecture,
% 0.21/0.52      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)))).
% 0.21/0.52  
% 0.21/0.52  tff(u298,negated_conjecture,
% 0.21/0.52      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 0.21/0.52  
% 0.21/0.52  tff(u297,negated_conjecture,
% 0.21/0.52      (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)))).
% 0.21/0.52  
% 0.21/0.52  tff(u296,negated_conjecture,
% 0.21/0.52      (![X1] : ((k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k7_subset_1(X1,X1,sK1))))))).
% 0.21/0.52  
% 0.21/0.52  tff(u295,axiom,
% 0.21/0.52      (![X1, X0] : ((k1_xboole_0 = k7_subset_1(X0,k1_xboole_0,X1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u294,axiom,
% 0.21/0.52      (![X1] : ((k1_xboole_0 = k7_subset_1(X1,X1,X1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u293,negated_conjecture,
% 0.21/0.52      (![X0] : ((k1_xboole_0 = k7_subset_1(X0,X0,k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))))))).
% 0.21/0.52  
% 0.21/0.52  tff(u292,axiom,
% 0.21/0.52      (![X3, X2] : ((k1_xboole_0 = k7_subset_1(X2,X2,k5_xboole_0(X2,k7_subset_1(X3,X3,X2))))))).
% 0.21/0.52  
% 0.21/0.52  tff(u291,negated_conjecture,
% 0.21/0.52      (k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0)))).
% 0.21/0.52  
% 0.21/0.52  tff(u290,negated_conjecture,
% 0.21/0.52      (![X1] : ((k1_xboole_0 = k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k7_subset_1(X1,X1,sK1))))))).
% 0.21/0.52  
% 0.21/0.52  tff(u289,axiom,
% 0.21/0.52      (![X0] : ((k7_subset_1(X0,X0,k1_xboole_0) = X0)))).
% 0.21/0.52  
% 0.21/0.52  tff(u288,negated_conjecture,
% 0.21/0.52      (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u287,negated_conjecture,
% 0.21/0.52      (u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u286,negated_conjecture,
% 0.21/0.52      (sK1 = k3_xboole_0(sK1,u1_struct_0(sK0)))).
% 0.21/0.52  
% 0.21/0.52  tff(u285,negated_conjecture,
% 0.21/0.52      (sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0))).
% 0.21/0.52  
% 0.21/0.52  tff(u284,negated_conjecture,
% 0.21/0.52      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)))).
% 0.21/0.52  
% 0.21/0.52  tff(u283,axiom,
% 0.21/0.52      (![X1, X3, X2] : ((~r1_tarski(X2,X1) | (k7_subset_1(X1,X2,X3) = k7_subset_1(X2,X2,X3)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u282,axiom,
% 0.21/0.52      (![X1, X0] : ((~r1_tarski(X1,X0) | (X0 = X1) | ~r1_tarski(X0,X1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u281,axiom,
% 0.21/0.52      (![X1, X0] : ((~r1_tarski(X0,X1) | (k3_xboole_0(X0,X1) = X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u280,axiom,
% 0.21/0.52      (![X0] : ((~r1_tarski(X0,k1_xboole_0) | (k1_xboole_0 = X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u279,axiom,
% 0.21/0.52      (![X1, X0] : ((~r1_tarski(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))))).
% 0.21/0.52  
% 0.21/0.52  % (983)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  tff(u278,negated_conjecture,
% 0.21/0.52      ((~~r1_tarski(u1_struct_0(sK0),sK1)) | ~r1_tarski(u1_struct_0(sK0),sK1))).
% 0.21/0.52  
% 0.21/0.52  % (983)Memory used [KB]: 1663
% 0.21/0.52  tff(u277,negated_conjecture,
% 0.21/0.52      ((~~r1_tarski(k2_struct_0(sK0),sK1)) | ~r1_tarski(k2_struct_0(sK0),sK1))).
% 0.21/0.52  
% 0.21/0.52  % (983)Time elapsed: 0.109 s
% 0.21/0.52  tff(u276,axiom,
% 0.21/0.52      (![X0] : (r1_tarski(k1_xboole_0,X0)))).
% 0.21/0.52  
% 0.21/0.52  % (983)------------------------------
% 0.21/0.52  % (983)------------------------------
% 0.21/0.52  % (999)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.52  tff(u275,axiom,
% 0.21/0.52      (![X1] : (r1_tarski(X1,X1)))).
% 0.21/0.52  
% 0.21/0.52  tff(u274,negated_conjecture,
% 0.21/0.52      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.21/0.52  
% 0.21/0.52  tff(u273,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u272,axiom,
% 0.21/0.52      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u271,axiom,
% 0.21/0.52      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1) | ~l1_struct_0(X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u270,negated_conjecture,
% 0.21/0.52      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.52  
% 0.21/0.52  tff(u269,axiom,
% 0.21/0.52      (![X1, X0] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u268,axiom,
% 0.21/0.52      (![X1] : ((~l1_struct_0(X1) | (u1_struct_0(X1) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),u1_struct_0(X1)))))))).
% 0.21/0.52  
% 0.21/0.52  tff(u267,axiom,
% 0.21/0.52      (![X0] : ((~l1_struct_0(X0) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k1_xboole_0))))))).
% 0.21/0.52  
% 0.21/0.52  tff(u266,negated_conjecture,
% 0.21/0.52      l1_struct_0(sK0)).
% 0.21/0.52  
% 0.21/0.52  % (975)# SZS output end Saturation.
% 0.21/0.52  % (975)------------------------------
% 0.21/0.52  % (975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (975)Termination reason: Satisfiable
% 0.21/0.52  
% 0.21/0.52  % (975)Memory used [KB]: 10874
% 0.21/0.52  % (975)Time elapsed: 0.089 s
% 0.21/0.52  % (975)------------------------------
% 0.21/0.52  % (975)------------------------------
% 0.21/0.52  % (977)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (966)Success in time 0.16 s
%------------------------------------------------------------------------------
