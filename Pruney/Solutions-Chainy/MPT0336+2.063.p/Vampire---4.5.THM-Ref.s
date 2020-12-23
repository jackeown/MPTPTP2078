%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:32 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 163 expanded)
%              Number of leaves         :   13 (  46 expanded)
%              Depth                    :   16
%              Number of atoms          :  135 ( 336 expanded)
%              Number of equality atoms :   56 ( 122 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f298,plain,(
    $false ),
    inference(subsumption_resolution,[],[f291,f65])).

fof(f65,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f63,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f63,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f33,f22])).

fof(f22,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f291,plain,(
    k1_xboole_0 != k3_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f73,f252])).

fof(f252,plain,(
    ! [X13] : k3_xboole_0(sK1,X13) = k3_xboole_0(sK1,k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,X13))) ),
    inference(trivial_inequality_removal,[],[f246])).

fof(f246,plain,(
    ! [X13] :
      ( k1_xboole_0 != k1_xboole_0
      | k3_xboole_0(sK1,X13) = k3_xboole_0(sK1,k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,X13))) ) ),
    inference(superposition,[],[f120,f203])).

fof(f203,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f200])).

fof(f200,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k3_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f107,f196])).

fof(f196,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f193,f63])).

fof(f193,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | k1_xboole_0 != k3_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f189,f85])).

% (25517)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f85,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | k1_xboole_0 != k3_xboole_0(sK2,X0) ) ),
    inference(resolution,[],[f76,f21])).

fof(f21,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f17])).

% (25539)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f76,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X1,X2)
      | k1_xboole_0 != k3_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f29,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f189,plain,
    ( r2_hidden(sK3,sK1)
    | k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f180,f58])).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f25,f26])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f180,plain,(
    ! [X4] :
      ( ~ r1_tarski(k3_xboole_0(sK0,sK1),X4)
      | r2_hidden(sK3,X4)
      | k1_xboole_0 = k3_xboole_0(sK0,sK1) ) ),
    inference(superposition,[],[f55,f167])).

% (25516)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f167,plain,
    ( k3_xboole_0(sK0,sK1) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f51,f48])).

fof(f48,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f20,f46])).

fof(f46,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f24,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f37,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f24,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | k3_enumset1(X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f34,f46,f46])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f39,f44])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f107,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 != k3_xboole_0(X3,X4)
      | k1_xboole_0 = k3_xboole_0(X4,X3) ) ),
    inference(resolution,[],[f102,f33])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X1,X0)
      | r1_xboole_0(X1,X0) ) ),
    inference(resolution,[],[f87,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f87,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(sK4(X4,X5),X6)
      | k1_xboole_0 != k3_xboole_0(X5,X6)
      | r1_xboole_0(X4,X5) ) ),
    inference(resolution,[],[f76,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f120,plain,(
    ! [X6,X4,X5] :
      ( k1_xboole_0 != k3_xboole_0(X4,X6)
      | k3_xboole_0(X4,X5) = k3_xboole_0(X4,k3_tarski(k3_enumset1(X6,X6,X6,X6,X5))) ) ),
    inference(resolution,[],[f52,f32])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X2) = k3_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ) ),
    inference(definition_unfolding,[],[f38,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f44])).

fof(f27,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f73,plain,(
    k1_xboole_0 != k3_xboole_0(sK1,k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2))) ),
    inference(superposition,[],[f62,f26])).

fof(f62,plain,(
    k1_xboole_0 != k3_xboole_0(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2)),sK1) ),
    inference(resolution,[],[f32,f47])).

fof(f47,plain,(
    ~ r1_xboole_0(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2)),sK1) ),
    inference(definition_unfolding,[],[f23,f45])).

fof(f23,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_vampire %s %d
% 0.16/0.36  % Computer   : n007.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % WCLimit    : 600
% 0.16/0.36  % DateTime   : Tue Dec  1 19:40:36 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.23/0.53  % (25520)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.54  % (25536)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.54  % (25527)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.23/0.54  % (25524)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.23/0.54  % (25537)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.23/0.54  % (25512)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.23/0.54  % (25519)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.54  % (25540)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.23/0.54  % (25524)Refutation not found, incomplete strategy% (25524)------------------------------
% 0.23/0.54  % (25524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (25524)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (25524)Memory used [KB]: 10746
% 0.23/0.54  % (25524)Time elapsed: 0.100 s
% 0.23/0.54  % (25524)------------------------------
% 0.23/0.54  % (25524)------------------------------
% 0.23/0.55  % (25536)Refutation not found, incomplete strategy% (25536)------------------------------
% 0.23/0.55  % (25536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (25512)Refutation not found, incomplete strategy% (25512)------------------------------
% 0.23/0.55  % (25512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (25512)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (25512)Memory used [KB]: 1791
% 0.23/0.55  % (25512)Time elapsed: 0.116 s
% 0.23/0.55  % (25512)------------------------------
% 0.23/0.55  % (25512)------------------------------
% 0.23/0.55  % (25528)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.23/0.55  % (25531)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.23/0.55  % (25531)Refutation not found, incomplete strategy% (25531)------------------------------
% 0.23/0.55  % (25531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (25531)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (25531)Memory used [KB]: 10618
% 0.23/0.55  % (25531)Time elapsed: 0.114 s
% 0.23/0.55  % (25531)------------------------------
% 0.23/0.55  % (25531)------------------------------
% 0.23/0.56  % (25520)Refutation found. Thanks to Tanya!
% 0.23/0.56  % SZS status Theorem for theBenchmark
% 0.23/0.56  % (25536)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (25536)Memory used [KB]: 10746
% 0.23/0.56  % (25536)Time elapsed: 0.058 s
% 0.23/0.56  % (25536)------------------------------
% 0.23/0.56  % (25536)------------------------------
% 0.23/0.56  % SZS output start Proof for theBenchmark
% 0.23/0.56  fof(f298,plain,(
% 0.23/0.56    $false),
% 0.23/0.56    inference(subsumption_resolution,[],[f291,f65])).
% 0.23/0.56  fof(f65,plain,(
% 0.23/0.56    k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 0.23/0.56    inference(superposition,[],[f63,f26])).
% 0.23/0.56  fof(f26,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f1])).
% 0.23/0.56  fof(f1,axiom,(
% 0.23/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.23/0.56  fof(f63,plain,(
% 0.23/0.56    k1_xboole_0 = k3_xboole_0(sK2,sK1)),
% 0.23/0.56    inference(resolution,[],[f33,f22])).
% 0.23/0.56  fof(f22,plain,(
% 0.23/0.56    r1_xboole_0(sK2,sK1)),
% 0.23/0.56    inference(cnf_transformation,[],[f17])).
% 0.23/0.56  fof(f17,plain,(
% 0.23/0.56    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 0.23/0.56    inference(flattening,[],[f16])).
% 0.23/0.56  fof(f16,plain,(
% 0.23/0.56    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 0.23/0.56    inference(ennf_transformation,[],[f14])).
% 0.23/0.56  fof(f14,negated_conjecture,(
% 0.23/0.56    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.23/0.56    inference(negated_conjecture,[],[f13])).
% 0.23/0.56  fof(f13,conjecture,(
% 0.23/0.56    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 0.23/0.56  fof(f33,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.23/0.56    inference(cnf_transformation,[],[f2])).
% 0.23/0.56  fof(f2,axiom,(
% 0.23/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.23/0.56  fof(f291,plain,(
% 0.23/0.56    k1_xboole_0 != k3_xboole_0(sK1,sK2)),
% 0.23/0.56    inference(superposition,[],[f73,f252])).
% 0.23/0.56  fof(f252,plain,(
% 0.23/0.56    ( ! [X13] : (k3_xboole_0(sK1,X13) = k3_xboole_0(sK1,k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,X13)))) )),
% 0.23/0.56    inference(trivial_inequality_removal,[],[f246])).
% 0.23/0.56  fof(f246,plain,(
% 0.23/0.56    ( ! [X13] : (k1_xboole_0 != k1_xboole_0 | k3_xboole_0(sK1,X13) = k3_xboole_0(sK1,k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,X13)))) )),
% 0.23/0.56    inference(superposition,[],[f120,f203])).
% 0.23/0.56  fof(f203,plain,(
% 0.23/0.56    k1_xboole_0 = k3_xboole_0(sK1,sK0)),
% 0.23/0.56    inference(trivial_inequality_removal,[],[f200])).
% 0.23/0.56  fof(f200,plain,(
% 0.23/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_xboole_0(sK1,sK0)),
% 0.23/0.56    inference(superposition,[],[f107,f196])).
% 0.23/0.56  fof(f196,plain,(
% 0.23/0.56    k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.23/0.56    inference(subsumption_resolution,[],[f193,f63])).
% 0.23/0.56  fof(f193,plain,(
% 0.23/0.56    k1_xboole_0 = k3_xboole_0(sK0,sK1) | k1_xboole_0 != k3_xboole_0(sK2,sK1)),
% 0.23/0.56    inference(resolution,[],[f189,f85])).
% 0.23/0.56  % (25517)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.23/0.56  fof(f85,plain,(
% 0.23/0.56    ( ! [X0] : (~r2_hidden(sK3,X0) | k1_xboole_0 != k3_xboole_0(sK2,X0)) )),
% 0.23/0.56    inference(resolution,[],[f76,f21])).
% 0.23/0.56  fof(f21,plain,(
% 0.23/0.56    r2_hidden(sK3,sK2)),
% 0.23/0.56    inference(cnf_transformation,[],[f17])).
% 0.23/0.56  % (25539)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.23/0.56  fof(f76,plain,(
% 0.23/0.56    ( ! [X2,X3,X1] : (~r2_hidden(X1,X3) | ~r2_hidden(X1,X2) | k1_xboole_0 != k3_xboole_0(X3,X2)) )),
% 0.23/0.56    inference(resolution,[],[f29,f32])).
% 0.23/0.56  fof(f32,plain,(
% 0.23/0.56    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.23/0.56    inference(cnf_transformation,[],[f2])).
% 0.23/0.56  fof(f29,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f18])).
% 0.23/0.56  fof(f18,plain,(
% 0.23/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.23/0.56    inference(ennf_transformation,[],[f15])).
% 0.23/0.56  fof(f15,plain,(
% 0.23/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.23/0.56    inference(rectify,[],[f3])).
% 0.23/0.56  fof(f3,axiom,(
% 0.23/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.23/0.56  fof(f189,plain,(
% 0.23/0.56    r2_hidden(sK3,sK1) | k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.23/0.56    inference(resolution,[],[f180,f58])).
% 0.23/0.56  fof(f58,plain,(
% 0.23/0.56    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 0.23/0.56    inference(superposition,[],[f25,f26])).
% 0.23/0.56  fof(f25,plain,(
% 0.23/0.56    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f4])).
% 0.23/0.56  fof(f4,axiom,(
% 0.23/0.56    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.23/0.56  fof(f180,plain,(
% 0.23/0.56    ( ! [X4] : (~r1_tarski(k3_xboole_0(sK0,sK1),X4) | r2_hidden(sK3,X4) | k1_xboole_0 = k3_xboole_0(sK0,sK1)) )),
% 0.23/0.56    inference(superposition,[],[f55,f167])).
% 0.23/0.56  % (25516)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.56  fof(f167,plain,(
% 0.23/0.56    k3_xboole_0(sK0,sK1) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) | k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.23/0.56    inference(resolution,[],[f51,f48])).
% 0.23/0.56  fof(f48,plain,(
% 0.23/0.56    r1_tarski(k3_xboole_0(sK0,sK1),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),
% 0.23/0.56    inference(definition_unfolding,[],[f20,f46])).
% 0.23/0.56  fof(f46,plain,(
% 0.23/0.56    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.23/0.56    inference(definition_unfolding,[],[f24,f44])).
% 0.23/0.56  fof(f44,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.23/0.56    inference(definition_unfolding,[],[f28,f43])).
% 0.23/0.56  fof(f43,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.23/0.56    inference(definition_unfolding,[],[f37,f42])).
% 0.23/0.56  fof(f42,plain,(
% 0.23/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f9])).
% 0.23/0.56  fof(f9,axiom,(
% 0.23/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.23/0.56  fof(f37,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f8])).
% 0.23/0.56  fof(f8,axiom,(
% 0.23/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.23/0.56  fof(f28,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f7])).
% 0.23/0.56  fof(f7,axiom,(
% 0.23/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.23/0.56  fof(f24,plain,(
% 0.23/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f6])).
% 0.23/0.56  fof(f6,axiom,(
% 0.23/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.23/0.56  fof(f20,plain,(
% 0.23/0.56    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.23/0.56    inference(cnf_transformation,[],[f17])).
% 0.23/0.56  fof(f51,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) | k3_enumset1(X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 0.23/0.56    inference(definition_unfolding,[],[f34,f46,f46])).
% 0.23/0.56  fof(f34,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.23/0.56    inference(cnf_transformation,[],[f10])).
% 0.23/0.56  fof(f10,axiom,(
% 0.23/0.56    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.23/0.56  fof(f55,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (~r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 0.23/0.56    inference(definition_unfolding,[],[f39,f44])).
% 0.23/0.56  fof(f39,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f12])).
% 0.23/0.56  fof(f12,axiom,(
% 0.23/0.56    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.23/0.56  fof(f107,plain,(
% 0.23/0.56    ( ! [X4,X3] : (k1_xboole_0 != k3_xboole_0(X3,X4) | k1_xboole_0 = k3_xboole_0(X4,X3)) )),
% 0.23/0.56    inference(resolution,[],[f102,f33])).
% 0.23/0.56  fof(f102,plain,(
% 0.23/0.56    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.23/0.56    inference(duplicate_literal_removal,[],[f98])).
% 0.23/0.56  fof(f98,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X1,X0) | r1_xboole_0(X1,X0)) )),
% 0.23/0.56    inference(resolution,[],[f87,f30])).
% 0.23/0.56  fof(f30,plain,(
% 0.23/0.56    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f18])).
% 0.23/0.56  fof(f87,plain,(
% 0.23/0.56    ( ! [X6,X4,X5] : (~r2_hidden(sK4(X4,X5),X6) | k1_xboole_0 != k3_xboole_0(X5,X6) | r1_xboole_0(X4,X5)) )),
% 0.23/0.56    inference(resolution,[],[f76,f31])).
% 0.23/0.56  fof(f31,plain,(
% 0.23/0.56    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f18])).
% 0.23/0.56  fof(f120,plain,(
% 0.23/0.56    ( ! [X6,X4,X5] : (k1_xboole_0 != k3_xboole_0(X4,X6) | k3_xboole_0(X4,X5) = k3_xboole_0(X4,k3_tarski(k3_enumset1(X6,X6,X6,X6,X5)))) )),
% 0.23/0.56    inference(resolution,[],[f52,f32])).
% 0.23/0.56  fof(f52,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X2) = k3_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))) )),
% 0.23/0.56    inference(definition_unfolding,[],[f38,f45])).
% 0.23/0.56  fof(f45,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.23/0.56    inference(definition_unfolding,[],[f27,f44])).
% 0.23/0.56  fof(f27,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f11])).
% 0.23/0.56  fof(f11,axiom,(
% 0.23/0.56    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.23/0.56  fof(f38,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f19])).
% 0.23/0.56  fof(f19,plain,(
% 0.23/0.56    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 0.23/0.56    inference(ennf_transformation,[],[f5])).
% 0.23/0.56  fof(f5,axiom,(
% 0.23/0.56    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).
% 0.23/0.56  fof(f73,plain,(
% 0.23/0.56    k1_xboole_0 != k3_xboole_0(sK1,k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2)))),
% 0.23/0.56    inference(superposition,[],[f62,f26])).
% 0.23/0.56  fof(f62,plain,(
% 0.23/0.56    k1_xboole_0 != k3_xboole_0(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2)),sK1)),
% 0.23/0.56    inference(resolution,[],[f32,f47])).
% 0.23/0.56  fof(f47,plain,(
% 0.23/0.56    ~r1_xboole_0(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2)),sK1)),
% 0.23/0.56    inference(definition_unfolding,[],[f23,f45])).
% 0.23/0.56  fof(f23,plain,(
% 0.23/0.56    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.23/0.56    inference(cnf_transformation,[],[f17])).
% 0.23/0.56  % SZS output end Proof for theBenchmark
% 0.23/0.56  % (25520)------------------------------
% 0.23/0.56  % (25520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (25520)Termination reason: Refutation
% 0.23/0.56  
% 0.23/0.56  % (25520)Memory used [KB]: 6524
% 0.23/0.56  % (25520)Time elapsed: 0.110 s
% 0.23/0.56  % (25520)------------------------------
% 0.23/0.56  % (25520)------------------------------
% 0.23/0.56  % (25507)Success in time 0.182 s
%------------------------------------------------------------------------------
