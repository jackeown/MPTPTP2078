%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:29 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 154 expanded)
%              Number of leaves         :   16 (  45 expanded)
%              Depth                    :   16
%              Number of atoms          :  125 ( 276 expanded)
%              Number of equality atoms :   44 (  89 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f534,plain,(
    $false ),
    inference(global_subsumption,[],[f488,f532])).

fof(f532,plain,(
    sK0 != k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f529,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

% (12898)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f529,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f521,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f521,plain,(
    ~ r1_xboole_0(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f74,f73,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(definition_unfolding,[],[f48,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f73,plain,(
    ~ r1_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2))) ),
    inference(unit_resulting_resolution,[],[f59,f39])).

fof(f59,plain,(
    ~ r1_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1) ),
    inference(definition_unfolding,[],[f28,f57])).

fof(f28,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f74,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f27,f39])).

fof(f27,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f488,plain,(
    sK0 = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f478,f30])).

fof(f30,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f478,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f62,f467])).

fof(f467,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f466,f246])).

fof(f246,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f212,f97])).

fof(f97,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f75,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f75,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f29,f39])).

fof(f29,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f212,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f61,f30])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f33,f37,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f466,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f185,f445])).

fof(f445,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(unit_resulting_resolution,[],[f235,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f42,f58])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f56])).

fof(f31,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f235,plain,(
    ! [X19] : ~ r2_hidden(sK3,k4_xboole_0(X19,k4_xboole_0(X19,sK1))) ),
    inference(superposition,[],[f145,f61])).

fof(f145,plain,(
    ! [X0] : ~ r2_hidden(sK3,k4_xboole_0(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f134,f70])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f134,plain,(
    ! [X0] : ~ sP5(sK3,X0,sK1) ),
    inference(unit_resulting_resolution,[],[f132,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f132,plain,(
    ~ r2_hidden(sK3,sK1) ),
    inference(superposition,[],[f123,f98])).

fof(f98,plain,(
    sK1 = k4_xboole_0(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f74,f41])).

fof(f123,plain,(
    ! [X0] : ~ r2_hidden(sK3,k4_xboole_0(X0,sK2)) ),
    inference(unit_resulting_resolution,[],[f88,f70])).

fof(f88,plain,(
    ! [X0] : ~ sP5(sK3,sK2,X0) ),
    inference(unit_resulting_resolution,[],[f26,f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f26,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f185,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))) ),
    inference(unit_resulting_resolution,[],[f60,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f60,plain,(
    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f25,f37,f58])).

fof(f25,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:52:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.49  % (12873)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (12885)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.23/0.52  % (12871)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.23/0.52  % (12880)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.23/0.52  % (12892)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.23/0.52  % (12893)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.23/0.52  % (12886)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.23/0.53  % (12896)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.23/0.53  % (12889)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.23/0.53  % (12895)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.23/0.53  % (12893)Refutation not found, incomplete strategy% (12893)------------------------------
% 1.23/0.53  % (12893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (12874)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.23/0.53  % (12877)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.34/0.53  % (12893)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (12893)Memory used [KB]: 10746
% 1.34/0.53  % (12893)Time elapsed: 0.069 s
% 1.34/0.53  % (12893)------------------------------
% 1.34/0.53  % (12893)------------------------------
% 1.34/0.53  % (12875)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.34/0.53  % (12878)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.34/0.53  % (12872)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.34/0.53  % (12881)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.34/0.54  % (12876)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.34/0.54  % (12887)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.34/0.54  % (12883)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.54  % (12888)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.34/0.54  % (12894)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.34/0.54  % (12884)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.34/0.54  % (12882)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.34/0.54  % (12899)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.34/0.55  % (12879)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.34/0.55  % (12890)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.34/0.55  % (12895)Refutation found. Thanks to Tanya!
% 1.34/0.55  % SZS status Theorem for theBenchmark
% 1.34/0.55  % (12891)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.34/0.55  % (12900)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.34/0.56  % (12897)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.34/0.57  % SZS output start Proof for theBenchmark
% 1.34/0.57  fof(f534,plain,(
% 1.34/0.57    $false),
% 1.34/0.57    inference(global_subsumption,[],[f488,f532])).
% 1.34/0.57  fof(f532,plain,(
% 1.34/0.57    sK0 != k4_xboole_0(sK0,sK1)),
% 1.34/0.57    inference(unit_resulting_resolution,[],[f529,f40])).
% 1.34/0.57  fof(f40,plain,(
% 1.34/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f12])).
% 1.34/0.57  fof(f12,axiom,(
% 1.34/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.34/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.34/0.57  % (12898)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.34/0.58  fof(f529,plain,(
% 1.34/0.58    ~r1_xboole_0(sK0,sK1)),
% 1.34/0.58    inference(unit_resulting_resolution,[],[f521,f39])).
% 1.34/0.58  fof(f39,plain,(
% 1.34/0.58    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f23])).
% 1.34/0.58  fof(f23,plain,(
% 1.34/0.58    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.34/0.58    inference(ennf_transformation,[],[f3])).
% 1.34/0.58  fof(f3,axiom,(
% 1.34/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.34/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.34/0.58  fof(f521,plain,(
% 1.34/0.58    ~r1_xboole_0(sK1,sK0)),
% 1.34/0.58    inference(unit_resulting_resolution,[],[f74,f73,f67])).
% 1.34/0.58  fof(f67,plain,(
% 1.34/0.58    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 1.34/0.58    inference(definition_unfolding,[],[f48,f57])).
% 1.34/0.58  fof(f57,plain,(
% 1.34/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.34/0.58    inference(definition_unfolding,[],[f34,f56])).
% 1.34/0.58  fof(f56,plain,(
% 1.34/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.34/0.58    inference(definition_unfolding,[],[f35,f44])).
% 1.34/0.58  fof(f44,plain,(
% 1.34/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f15])).
% 1.34/0.58  fof(f15,axiom,(
% 1.34/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.34/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.34/0.58  fof(f35,plain,(
% 1.34/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f14])).
% 1.34/0.58  fof(f14,axiom,(
% 1.34/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.34/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.34/0.58  fof(f34,plain,(
% 1.34/0.58    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f16])).
% 1.34/0.58  fof(f16,axiom,(
% 1.34/0.58    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.34/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.34/0.58  fof(f48,plain,(
% 1.34/0.58    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f24])).
% 1.34/0.58  fof(f24,plain,(
% 1.34/0.58    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.34/0.58    inference(ennf_transformation,[],[f10])).
% 1.34/0.58  fof(f10,axiom,(
% 1.34/0.58    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.34/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.34/0.58  fof(f73,plain,(
% 1.34/0.58    ~r1_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)))),
% 1.34/0.58    inference(unit_resulting_resolution,[],[f59,f39])).
% 1.34/0.58  fof(f59,plain,(
% 1.34/0.58    ~r1_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1)),
% 1.34/0.58    inference(definition_unfolding,[],[f28,f57])).
% 1.34/0.58  fof(f28,plain,(
% 1.34/0.58    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.34/0.58    inference(cnf_transformation,[],[f21])).
% 1.34/0.58  fof(f21,plain,(
% 1.34/0.58    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 1.34/0.58    inference(flattening,[],[f20])).
% 1.34/0.58  fof(f20,plain,(
% 1.34/0.58    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 1.34/0.58    inference(ennf_transformation,[],[f19])).
% 1.34/0.58  fof(f19,negated_conjecture,(
% 1.34/0.58    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.34/0.58    inference(negated_conjecture,[],[f18])).
% 1.34/0.58  fof(f18,conjecture,(
% 1.34/0.58    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.34/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 1.34/0.58  fof(f74,plain,(
% 1.34/0.58    r1_xboole_0(sK1,sK2)),
% 1.34/0.58    inference(unit_resulting_resolution,[],[f27,f39])).
% 1.34/0.58  fof(f27,plain,(
% 1.34/0.58    r1_xboole_0(sK2,sK1)),
% 1.34/0.58    inference(cnf_transformation,[],[f21])).
% 1.34/0.58  fof(f488,plain,(
% 1.34/0.58    sK0 = k4_xboole_0(sK0,sK1)),
% 1.34/0.58    inference(forward_demodulation,[],[f478,f30])).
% 1.34/0.58  fof(f30,plain,(
% 1.34/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.34/0.58    inference(cnf_transformation,[],[f6])).
% 1.34/0.58  fof(f6,axiom,(
% 1.34/0.58    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.34/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.34/0.58  fof(f478,plain,(
% 1.34/0.58    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)),
% 1.34/0.58    inference(superposition,[],[f62,f467])).
% 1.34/0.58  fof(f467,plain,(
% 1.34/0.58    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.34/0.58    inference(forward_demodulation,[],[f466,f246])).
% 1.34/0.58  fof(f246,plain,(
% 1.34/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.34/0.58    inference(forward_demodulation,[],[f212,f97])).
% 1.34/0.58  fof(f97,plain,(
% 1.34/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.34/0.58    inference(unit_resulting_resolution,[],[f75,f41])).
% 1.34/0.58  fof(f41,plain,(
% 1.34/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f12])).
% 1.34/0.58  fof(f75,plain,(
% 1.34/0.58    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.34/0.58    inference(unit_resulting_resolution,[],[f29,f39])).
% 1.34/0.58  fof(f29,plain,(
% 1.34/0.58    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f9])).
% 1.34/0.58  fof(f9,axiom,(
% 1.34/0.58    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.34/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.34/0.58  fof(f212,plain,(
% 1.34/0.58    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 1.34/0.58    inference(superposition,[],[f61,f30])).
% 1.34/0.58  fof(f61,plain,(
% 1.34/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.34/0.58    inference(definition_unfolding,[],[f33,f37,f37])).
% 1.34/0.58  fof(f37,plain,(
% 1.34/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.34/0.58    inference(cnf_transformation,[],[f8])).
% 1.34/0.58  fof(f8,axiom,(
% 1.34/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.34/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.34/0.58  fof(f33,plain,(
% 1.34/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f1])).
% 1.34/0.58  fof(f1,axiom,(
% 1.34/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.34/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.34/0.58  fof(f466,plain,(
% 1.34/0.58    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.34/0.58    inference(backward_demodulation,[],[f185,f445])).
% 1.34/0.58  fof(f445,plain,(
% 1.34/0.58    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))) )),
% 1.34/0.58    inference(unit_resulting_resolution,[],[f235,f65])).
% 1.34/0.58  fof(f65,plain,(
% 1.34/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 1.34/0.58    inference(definition_unfolding,[],[f42,f58])).
% 1.34/0.58  fof(f58,plain,(
% 1.34/0.58    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.34/0.58    inference(definition_unfolding,[],[f31,f56])).
% 1.34/0.58  fof(f31,plain,(
% 1.34/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f13])).
% 1.34/0.58  fof(f13,axiom,(
% 1.34/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.34/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.34/0.58  fof(f42,plain,(
% 1.34/0.58    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 1.34/0.58    inference(cnf_transformation,[],[f17])).
% 1.34/0.58  fof(f17,axiom,(
% 1.34/0.58    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.34/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.34/0.58  fof(f235,plain,(
% 1.34/0.58    ( ! [X19] : (~r2_hidden(sK3,k4_xboole_0(X19,k4_xboole_0(X19,sK1)))) )),
% 1.34/0.58    inference(superposition,[],[f145,f61])).
% 1.34/0.58  fof(f145,plain,(
% 1.34/0.58    ( ! [X0] : (~r2_hidden(sK3,k4_xboole_0(sK1,X0))) )),
% 1.34/0.58    inference(unit_resulting_resolution,[],[f134,f70])).
% 1.34/0.58  fof(f70,plain,(
% 1.34/0.58    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | sP5(X3,X1,X0)) )),
% 1.34/0.58    inference(equality_resolution,[],[f53])).
% 1.34/0.58  fof(f53,plain,(
% 1.34/0.58    ( ! [X2,X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.34/0.58    inference(cnf_transformation,[],[f2])).
% 1.34/0.58  fof(f2,axiom,(
% 1.34/0.58    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.34/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.34/0.58  fof(f134,plain,(
% 1.34/0.58    ( ! [X0] : (~sP5(sK3,X0,sK1)) )),
% 1.34/0.58    inference(unit_resulting_resolution,[],[f132,f50])).
% 1.34/0.58  fof(f50,plain,(
% 1.34/0.58    ( ! [X0,X3,X1] : (~sP5(X3,X1,X0) | r2_hidden(X3,X0)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f2])).
% 1.34/0.58  fof(f132,plain,(
% 1.34/0.58    ~r2_hidden(sK3,sK1)),
% 1.34/0.58    inference(superposition,[],[f123,f98])).
% 1.34/0.58  fof(f98,plain,(
% 1.34/0.58    sK1 = k4_xboole_0(sK1,sK2)),
% 1.34/0.58    inference(unit_resulting_resolution,[],[f74,f41])).
% 1.34/0.58  fof(f123,plain,(
% 1.34/0.58    ( ! [X0] : (~r2_hidden(sK3,k4_xboole_0(X0,sK2))) )),
% 1.34/0.58    inference(unit_resulting_resolution,[],[f88,f70])).
% 1.34/0.58  fof(f88,plain,(
% 1.34/0.58    ( ! [X0] : (~sP5(sK3,sK2,X0)) )),
% 1.34/0.58    inference(unit_resulting_resolution,[],[f26,f51])).
% 1.34/0.58  fof(f51,plain,(
% 1.34/0.58    ( ! [X0,X3,X1] : (~sP5(X3,X1,X0) | ~r2_hidden(X3,X1)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f2])).
% 1.34/0.58  fof(f26,plain,(
% 1.34/0.58    r2_hidden(sK3,sK2)),
% 1.34/0.58    inference(cnf_transformation,[],[f21])).
% 1.34/0.58  fof(f185,plain,(
% 1.34/0.58    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)))),
% 1.34/0.58    inference(unit_resulting_resolution,[],[f60,f63])).
% 1.34/0.58  fof(f63,plain,(
% 1.34/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.34/0.58    inference(definition_unfolding,[],[f38,f37])).
% 1.34/0.58  fof(f38,plain,(
% 1.34/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.34/0.58    inference(cnf_transformation,[],[f22])).
% 1.34/0.58  fof(f22,plain,(
% 1.34/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.34/0.58    inference(ennf_transformation,[],[f5])).
% 1.34/0.58  fof(f5,axiom,(
% 1.34/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.34/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.34/0.58  fof(f60,plain,(
% 1.34/0.58    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))),
% 1.34/0.58    inference(definition_unfolding,[],[f25,f37,f58])).
% 1.34/0.58  fof(f25,plain,(
% 1.34/0.58    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.34/0.58    inference(cnf_transformation,[],[f21])).
% 1.34/0.58  fof(f62,plain,(
% 1.34/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.34/0.58    inference(definition_unfolding,[],[f36,f37])).
% 1.34/0.58  fof(f36,plain,(
% 1.34/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.34/0.58    inference(cnf_transformation,[],[f7])).
% 1.34/0.58  fof(f7,axiom,(
% 1.34/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.34/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.34/0.58  % SZS output end Proof for theBenchmark
% 1.34/0.58  % (12895)------------------------------
% 1.34/0.58  % (12895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.58  % (12895)Termination reason: Refutation
% 1.34/0.58  
% 1.34/0.58  % (12895)Memory used [KB]: 6524
% 1.34/0.58  % (12895)Time elapsed: 0.139 s
% 1.34/0.58  % (12895)------------------------------
% 1.34/0.58  % (12895)------------------------------
% 1.34/0.58  % (12865)Success in time 0.227 s
%------------------------------------------------------------------------------
