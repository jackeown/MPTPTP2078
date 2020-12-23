%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:17 EST 2020

% Result     : Theorem 1.70s
% Output     : Refutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 228 expanded)
%              Number of leaves         :   15 (  62 expanded)
%              Depth                    :   17
%              Number of atoms          :  159 ( 752 expanded)
%              Number of equality atoms :   81 ( 311 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f342,plain,(
    $false ),
    inference(subsumption_resolution,[],[f45,f339])).

fof(f339,plain,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(condensation,[],[f338])).

fof(f338,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)
      | k1_xboole_0 = k10_relat_1(k1_xboole_0,X1) ) ),
    inference(condensation,[],[f267])).

fof(f267,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X1
      | k1_xboole_0 = k10_relat_1(k1_xboole_0,X2)
      | k1_xboole_0 = k10_relat_1(k1_xboole_0,X3) ) ),
    inference(superposition,[],[f264,f264])).

fof(f264,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k10_relat_1(k1_xboole_0,X2)
      | sK3(k1_xboole_0) = X3 ) ),
    inference(forward_demodulation,[],[f263,f135])).

fof(f135,plain,(
    k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(condensation,[],[f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)
      | k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) ) ),
    inference(superposition,[],[f104,f104])).

fof(f104,plain,(
    ! [X0] :
      ( sK3(k1_xboole_0) = X0
      | k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) ) ),
    inference(resolution,[],[f102,f51])).

% (10442)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f51,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

fof(f102,plain,(
    ! [X1] :
      ( v1_relat_1(k1_xboole_0)
      | sK3(k1_xboole_0) = X1 ) ),
    inference(resolution,[],[f99,f85])).

fof(f85,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f46,f63])).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f99,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k1_xboole_0),X0)
      | v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f97,f68])).

fof(f68,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK3(X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK3(X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f60,f56])).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f263,plain,(
    ! [X2,X3] :
      ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k10_relat_1(k1_xboole_0,X2)
      | sK3(k1_xboole_0) = X3 ) ),
    inference(forward_demodulation,[],[f262,f55])).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f262,plain,(
    ! [X2,X3] :
      ( k10_relat_1(k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)))
      | sK3(k1_xboole_0) = X3 ) ),
    inference(forward_demodulation,[],[f257,f67])).

fof(f67,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f257,plain,(
    ! [X2,X3] :
      ( k10_relat_1(k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,k4_xboole_0(k2_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),X2)))
      | sK3(k1_xboole_0) = X3 ) ),
    inference(resolution,[],[f79,f102])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f50,f65])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(f45,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f30])).

fof(f30,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:02:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (10427)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.56  % (10429)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.56  % (10427)Refutation not found, incomplete strategy% (10427)------------------------------
% 0.21/0.56  % (10427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (10427)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (10427)Memory used [KB]: 1663
% 0.21/0.56  % (10427)Time elapsed: 0.125 s
% 0.21/0.56  % (10427)------------------------------
% 0.21/0.56  % (10427)------------------------------
% 1.41/0.56  % (10429)Refutation not found, incomplete strategy% (10429)------------------------------
% 1.41/0.56  % (10429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.57  % (10435)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.58  % (10448)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.41/0.58  % (10429)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.58  
% 1.41/0.58  % (10429)Memory used [KB]: 10618
% 1.41/0.58  % (10429)Time elapsed: 0.123 s
% 1.41/0.58  % (10429)------------------------------
% 1.41/0.58  % (10429)------------------------------
% 1.41/0.58  % (10447)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.58  % (10435)Refutation not found, incomplete strategy% (10435)------------------------------
% 1.41/0.58  % (10435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.58  % (10448)Refutation not found, incomplete strategy% (10448)------------------------------
% 1.41/0.58  % (10448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.58  % (10448)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.58  
% 1.41/0.58  % (10448)Memory used [KB]: 1663
% 1.41/0.58  % (10448)Time elapsed: 0.145 s
% 1.41/0.58  % (10448)------------------------------
% 1.41/0.58  % (10448)------------------------------
% 1.70/0.58  % (10437)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.70/0.58  % (10437)Refutation not found, incomplete strategy% (10437)------------------------------
% 1.70/0.58  % (10437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.58  % (10437)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.58  
% 1.70/0.58  % (10437)Memory used [KB]: 10618
% 1.70/0.58  % (10437)Time elapsed: 0.143 s
% 1.70/0.58  % (10437)------------------------------
% 1.70/0.58  % (10437)------------------------------
% 1.70/0.59  % (10432)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.70/0.59  % (10447)Refutation not found, incomplete strategy% (10447)------------------------------
% 1.70/0.59  % (10447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.59  % (10435)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.59  
% 1.70/0.59  % (10435)Memory used [KB]: 10618
% 1.70/0.59  % (10435)Time elapsed: 0.143 s
% 1.70/0.59  % (10435)------------------------------
% 1.70/0.59  % (10435)------------------------------
% 1.70/0.59  % (10447)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.59  
% 1.70/0.59  % (10447)Memory used [KB]: 10746
% 1.70/0.59  % (10447)Time elapsed: 0.149 s
% 1.70/0.59  % (10447)------------------------------
% 1.70/0.59  % (10447)------------------------------
% 1.70/0.59  % (10430)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.70/0.60  % (10450)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.70/0.60  % (10440)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.70/0.60  % (10450)Refutation not found, incomplete strategy% (10450)------------------------------
% 1.70/0.60  % (10450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.60  % (10450)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.60  
% 1.70/0.60  % (10450)Memory used [KB]: 1791
% 1.70/0.60  % (10450)Time elapsed: 0.124 s
% 1.70/0.60  % (10450)------------------------------
% 1.70/0.60  % (10450)------------------------------
% 1.70/0.60  % (10431)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.70/0.61  % (10428)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.70/0.61  % (10432)Refutation found. Thanks to Tanya!
% 1.70/0.61  % SZS status Theorem for theBenchmark
% 1.70/0.61  % SZS output start Proof for theBenchmark
% 1.70/0.61  fof(f342,plain,(
% 1.70/0.61    $false),
% 1.70/0.61    inference(subsumption_resolution,[],[f45,f339])).
% 1.70/0.61  fof(f339,plain,(
% 1.70/0.61    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) )),
% 1.70/0.61    inference(condensation,[],[f338])).
% 1.70/0.61  fof(f338,plain,(
% 1.70/0.61    ( ! [X0,X1] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) | k1_xboole_0 = k10_relat_1(k1_xboole_0,X1)) )),
% 1.70/0.61    inference(condensation,[],[f267])).
% 1.70/0.61  fof(f267,plain,(
% 1.70/0.61    ( ! [X2,X0,X3,X1] : (X0 = X1 | k1_xboole_0 = k10_relat_1(k1_xboole_0,X2) | k1_xboole_0 = k10_relat_1(k1_xboole_0,X3)) )),
% 1.70/0.61    inference(superposition,[],[f264,f264])).
% 1.70/0.61  fof(f264,plain,(
% 1.70/0.61    ( ! [X2,X3] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X2) | sK3(k1_xboole_0) = X3) )),
% 1.70/0.61    inference(forward_demodulation,[],[f263,f135])).
% 1.70/0.61  fof(f135,plain,(
% 1.70/0.61    k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)),
% 1.70/0.61    inference(condensation,[],[f134])).
% 1.70/0.61  fof(f134,plain,(
% 1.70/0.61    ( ! [X0,X1] : (X0 = X1 | k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)) )),
% 1.70/0.61    inference(duplicate_literal_removal,[],[f109])).
% 1.70/0.61  fof(f109,plain,(
% 1.70/0.61    ( ! [X0,X1] : (X0 = X1 | k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)) )),
% 1.70/0.61    inference(superposition,[],[f104,f104])).
% 1.70/0.61  fof(f104,plain,(
% 1.70/0.61    ( ! [X0] : (sK3(k1_xboole_0) = X0 | k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)) )),
% 1.70/0.61    inference(resolution,[],[f102,f51])).
% 1.70/0.61  % (10442)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.70/0.61  fof(f51,plain,(
% 1.70/0.61    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f23])).
% 1.70/0.61  fof(f23,plain,(
% 1.70/0.61    ! [X0] : (k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 1.70/0.61    inference(ennf_transformation,[],[f16])).
% 1.70/0.61  fof(f16,axiom,(
% 1.70/0.61    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 1.70/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).
% 1.70/0.61  fof(f102,plain,(
% 1.70/0.61    ( ! [X1] : (v1_relat_1(k1_xboole_0) | sK3(k1_xboole_0) = X1) )),
% 1.70/0.61    inference(resolution,[],[f99,f85])).
% 1.70/0.61  fof(f85,plain,(
% 1.70/0.61    ( ! [X0,X3] : (~r2_hidden(X3,k2_tarski(X0,X0)) | X0 = X3) )),
% 1.70/0.61    inference(equality_resolution,[],[f78])).
% 1.70/0.61  fof(f78,plain,(
% 1.70/0.61    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 1.70/0.61    inference(definition_unfolding,[],[f46,f63])).
% 1.70/0.61  fof(f63,plain,(
% 1.70/0.61    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f8])).
% 1.70/0.61  fof(f8,axiom,(
% 1.70/0.61    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.70/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.70/0.61  fof(f46,plain,(
% 1.70/0.61    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.70/0.61    inference(cnf_transformation,[],[f35])).
% 1.70/0.61  fof(f35,plain,(
% 1.70/0.61    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.70/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).
% 1.70/0.61  fof(f34,plain,(
% 1.70/0.61    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 1.70/0.61    introduced(choice_axiom,[])).
% 1.70/0.62  fof(f33,plain,(
% 1.70/0.62    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.70/0.62    inference(rectify,[],[f32])).
% 1.70/0.62  fof(f32,plain,(
% 1.70/0.62    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.70/0.62    inference(nnf_transformation,[],[f6])).
% 1.70/0.62  fof(f6,axiom,(
% 1.70/0.62    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.70/0.62  fof(f99,plain,(
% 1.70/0.62    ( ! [X0] : (r2_hidden(sK3(k1_xboole_0),X0) | v1_relat_1(k1_xboole_0)) )),
% 1.70/0.62    inference(resolution,[],[f97,f68])).
% 1.70/0.62  fof(f68,plain,(
% 1.70/0.62    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_relat_1(X0)) )),
% 1.70/0.62    inference(cnf_transformation,[],[f44])).
% 1.70/0.62  fof(f44,plain,(
% 1.70/0.62    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK3(X0) & r2_hidden(sK3(X0),X0)))),
% 1.70/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f43])).
% 1.70/0.62  fof(f43,plain,(
% 1.70/0.62    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK3(X0) & r2_hidden(sK3(X0),X0)))),
% 1.70/0.62    introduced(choice_axiom,[])).
% 1.70/0.62  fof(f26,plain,(
% 1.70/0.62    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.70/0.62    inference(ennf_transformation,[],[f20])).
% 1.70/0.62  fof(f20,plain,(
% 1.70/0.62    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 1.70/0.62    inference(unused_predicate_definition_removal,[],[f14])).
% 1.70/0.62  fof(f14,axiom,(
% 1.70/0.62    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 1.70/0.62  fof(f97,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,X1)) )),
% 1.70/0.62    inference(resolution,[],[f60,f56])).
% 1.70/0.62  fof(f56,plain,(
% 1.70/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.70/0.62    inference(cnf_transformation,[],[f2])).
% 1.70/0.62  fof(f2,axiom,(
% 1.70/0.62    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.70/0.62  fof(f60,plain,(
% 1.70/0.62    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 1.70/0.62    inference(cnf_transformation,[],[f42])).
% 1.70/0.62  fof(f42,plain,(
% 1.70/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.70/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).
% 1.70/0.62  fof(f41,plain,(
% 1.70/0.62    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.70/0.62    introduced(choice_axiom,[])).
% 1.70/0.62  fof(f40,plain,(
% 1.70/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.70/0.62    inference(rectify,[],[f39])).
% 1.70/0.62  fof(f39,plain,(
% 1.70/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.70/0.62    inference(nnf_transformation,[],[f25])).
% 1.70/0.62  fof(f25,plain,(
% 1.70/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.70/0.62    inference(ennf_transformation,[],[f1])).
% 1.70/0.62  fof(f1,axiom,(
% 1.70/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.70/0.62  fof(f263,plain,(
% 1.70/0.62    ( ! [X2,X3] : (k10_relat_1(k1_xboole_0,k1_xboole_0) = k10_relat_1(k1_xboole_0,X2) | sK3(k1_xboole_0) = X3) )),
% 1.70/0.62    inference(forward_demodulation,[],[f262,f55])).
% 1.70/0.62  fof(f55,plain,(
% 1.70/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.70/0.62    inference(cnf_transformation,[],[f4])).
% 1.70/0.62  fof(f4,axiom,(
% 1.70/0.62    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.70/0.62  fof(f262,plain,(
% 1.70/0.62    ( ! [X2,X3] : (k10_relat_1(k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))) | sK3(k1_xboole_0) = X3) )),
% 1.70/0.62    inference(forward_demodulation,[],[f257,f67])).
% 1.70/0.62  fof(f67,plain,(
% 1.70/0.62    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.70/0.62    inference(cnf_transformation,[],[f17])).
% 1.70/0.62  fof(f17,axiom,(
% 1.70/0.62    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.70/0.62  fof(f257,plain,(
% 1.70/0.62    ( ! [X2,X3] : (k10_relat_1(k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,k4_xboole_0(k2_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),X2))) | sK3(k1_xboole_0) = X3) )),
% 1.70/0.62    inference(resolution,[],[f79,f102])).
% 1.70/0.62  fof(f79,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)))) )),
% 1.70/0.62    inference(definition_unfolding,[],[f50,f65])).
% 1.70/0.62  fof(f65,plain,(
% 1.70/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.70/0.62    inference(cnf_transformation,[],[f3])).
% 1.70/0.62  fof(f3,axiom,(
% 1.70/0.62    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.70/0.62  fof(f50,plain,(
% 1.70/0.62    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.70/0.62    inference(cnf_transformation,[],[f22])).
% 1.70/0.62  fof(f22,plain,(
% 1.70/0.62    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.70/0.62    inference(ennf_transformation,[],[f15])).
% 1.70/0.62  fof(f15,axiom,(
% 1.70/0.62    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 1.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).
% 1.70/0.62  fof(f45,plain,(
% 1.70/0.62    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 1.70/0.62    inference(cnf_transformation,[],[f31])).
% 1.70/0.62  fof(f31,plain,(
% 1.70/0.62    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 1.70/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f30])).
% 1.70/0.62  fof(f30,plain,(
% 1.70/0.62    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 1.70/0.62    introduced(choice_axiom,[])).
% 1.70/0.62  fof(f21,plain,(
% 1.70/0.62    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 1.70/0.62    inference(ennf_transformation,[],[f19])).
% 1.70/0.62  fof(f19,negated_conjecture,(
% 1.70/0.62    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 1.70/0.62    inference(negated_conjecture,[],[f18])).
% 1.70/0.62  fof(f18,conjecture,(
% 1.70/0.62    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 1.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
% 1.70/0.62  % SZS output end Proof for theBenchmark
% 1.70/0.62  % (10432)------------------------------
% 1.70/0.62  % (10432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.62  % (10432)Termination reason: Refutation
% 1.70/0.62  
% 1.70/0.62  % (10432)Memory used [KB]: 6396
% 1.70/0.62  % (10432)Time elapsed: 0.168 s
% 1.70/0.62  % (10432)------------------------------
% 1.70/0.62  % (10432)------------------------------
% 1.70/0.62  % (10426)Success in time 0.252 s
%------------------------------------------------------------------------------
