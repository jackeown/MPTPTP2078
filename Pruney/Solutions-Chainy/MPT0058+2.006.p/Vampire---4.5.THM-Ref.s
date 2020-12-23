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
% DateTime   : Thu Dec  3 12:30:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 221 expanded)
%              Number of leaves         :    9 (  61 expanded)
%              Depth                    :   15
%              Number of atoms          :  137 (1132 expanded)
%              Number of equality atoms :   51 ( 250 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f971,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f970])).

fof(f970,plain,(
    sK0 != sK0 ),
    inference(superposition,[],[f38,f804])).

fof(f804,plain,(
    ! [X30,X33] : k2_xboole_0(X30,k4_xboole_0(X30,X33)) = X30 ),
    inference(forward_demodulation,[],[f803,f722])).

fof(f722,plain,(
    ! [X14,X15,X16] : k4_xboole_0(X14,k4_xboole_0(k4_xboole_0(X15,X16),X15)) = X14 ),
    inference(resolution,[],[f715,f260])).

fof(f260,plain,(
    ! [X30,X31,X32] : ~ r2_hidden(X32,k4_xboole_0(k4_xboole_0(X30,X31),X30)) ),
    inference(subsumption_resolution,[],[f245,f34])).

fof(f34,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f15])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f245,plain,(
    ! [X30,X31,X32] :
      ( ~ r2_hidden(X32,k4_xboole_0(k4_xboole_0(X30,X31),X30))
      | ~ r2_hidden(X32,k4_xboole_0(X30,X31)) ) ),
    inference(superposition,[],[f33,f143])).

fof(f143,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f110,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f21,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f110,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f70,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(definition_unfolding,[],[f22,f19])).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

fof(f70,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X6) = k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X5)) ),
    inference(superposition,[],[f55,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f31,f30])).

fof(f33,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f715,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK2(X3,X4,X3),X4)
      | k4_xboole_0(X3,X4) = X3 ) ),
    inference(subsumption_resolution,[],[f713,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f713,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK2(X3,X4,X3),X4)
      | ~ r2_hidden(sK2(X3,X4,X3),X3)
      | k4_xboole_0(X3,X4) = X3 ) ),
    inference(duplicate_literal_removal,[],[f709])).

fof(f709,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK2(X3,X4,X3),X4)
      | ~ r2_hidden(sK2(X3,X4,X3),X3)
      | k4_xboole_0(X3,X4) = X3
      | k4_xboole_0(X3,X4) = X3 ) ),
    inference(resolution,[],[f28,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f26])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f803,plain,(
    ! [X30,X33,X31,X32] : k4_xboole_0(X30,k4_xboole_0(k4_xboole_0(X31,X32),X31)) = k2_xboole_0(X30,k4_xboole_0(X30,X33)) ),
    inference(forward_demodulation,[],[f758,f267])).

fof(f267,plain,(
    ! [X17,X18,X16] : k4_xboole_0(k4_xboole_0(X16,X17),X16) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X16,X17),X16),X18) ),
    inference(resolution,[],[f260,f121])).

fof(f758,plain,(
    ! [X30,X33,X31,X32] : k4_xboole_0(X30,k4_xboole_0(k4_xboole_0(k4_xboole_0(X31,X32),X31),k4_xboole_0(k4_xboole_0(k4_xboole_0(X31,X32),X31),X33))) = k2_xboole_0(X30,k4_xboole_0(X30,X33)) ),
    inference(superposition,[],[f31,f722])).

fof(f38,plain,(
    sK0 != k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f37,f18])).

fof(f37,plain,(
    sK0 != k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) ),
    inference(superposition,[],[f35,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f35,plain,(
    sK0 != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f29,f18])).

fof(f29,plain,(
    sK0 != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    inference(definition_unfolding,[],[f17,f19])).

fof(f17,plain,(
    sK0 != k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    sK0 != k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) != X0
   => sK0 != k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) != X0 ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:09:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (29657)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.49  % (29649)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.49  % (29649)Refutation not found, incomplete strategy% (29649)------------------------------
% 0.21/0.49  % (29649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (29649)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (29649)Memory used [KB]: 10618
% 0.21/0.50  % (29657)Refutation not found, incomplete strategy% (29657)------------------------------
% 0.21/0.50  % (29657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (29649)Time elapsed: 0.083 s
% 0.21/0.50  % (29649)------------------------------
% 0.21/0.50  % (29649)------------------------------
% 0.21/0.50  % (29657)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (29657)Memory used [KB]: 6268
% 0.21/0.50  % (29657)Time elapsed: 0.081 s
% 0.21/0.50  % (29657)------------------------------
% 0.21/0.50  % (29657)------------------------------
% 0.21/0.51  % (29660)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (29644)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (29636)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (29636)Refutation not found, incomplete strategy% (29636)------------------------------
% 0.21/0.53  % (29636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29636)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (29636)Memory used [KB]: 6140
% 0.21/0.53  % (29636)Time elapsed: 0.114 s
% 0.21/0.53  % (29636)------------------------------
% 0.21/0.53  % (29636)------------------------------
% 0.21/0.53  % (29640)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (29634)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (29650)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (29634)Refutation not found, incomplete strategy% (29634)------------------------------
% 0.21/0.53  % (29634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29634)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (29634)Memory used [KB]: 10618
% 0.21/0.53  % (29634)Time elapsed: 0.112 s
% 0.21/0.53  % (29634)------------------------------
% 0.21/0.53  % (29634)------------------------------
% 0.21/0.53  % (29648)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (29661)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (29635)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (29654)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (29652)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (29652)Refutation not found, incomplete strategy% (29652)------------------------------
% 0.21/0.54  % (29652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29652)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (29652)Memory used [KB]: 10618
% 0.21/0.54  % (29652)Time elapsed: 0.129 s
% 0.21/0.54  % (29652)------------------------------
% 0.21/0.54  % (29652)------------------------------
% 0.21/0.54  % (29639)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (29653)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (29653)Refutation not found, incomplete strategy% (29653)------------------------------
% 0.21/0.54  % (29653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29653)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (29653)Memory used [KB]: 1663
% 0.21/0.54  % (29653)Time elapsed: 0.140 s
% 0.21/0.54  % (29653)------------------------------
% 0.21/0.54  % (29653)------------------------------
% 0.21/0.54  % (29659)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (29642)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (29642)Refutation not found, incomplete strategy% (29642)------------------------------
% 0.21/0.55  % (29642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (29642)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (29642)Memory used [KB]: 10618
% 0.21/0.55  % (29642)Time elapsed: 0.126 s
% 0.21/0.55  % (29642)------------------------------
% 0.21/0.55  % (29642)------------------------------
% 0.21/0.55  % (29633)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (29645)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (29643)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (29656)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (29637)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (29646)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (29632)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (29632)Refutation not found, incomplete strategy% (29632)------------------------------
% 0.21/0.55  % (29632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (29632)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (29632)Memory used [KB]: 1663
% 0.21/0.55  % (29632)Time elapsed: 0.145 s
% 0.21/0.55  % (29632)------------------------------
% 0.21/0.55  % (29632)------------------------------
% 0.21/0.55  % (29640)Refutation not found, incomplete strategy% (29640)------------------------------
% 0.21/0.55  % (29640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (29640)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (29640)Memory used [KB]: 10618
% 0.21/0.55  % (29640)Time elapsed: 0.135 s
% 0.21/0.55  % (29640)------------------------------
% 0.21/0.55  % (29640)------------------------------
% 0.21/0.56  % (29651)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.56  % (29654)Refutation not found, incomplete strategy% (29654)------------------------------
% 0.21/0.56  % (29654)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (29654)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (29654)Memory used [KB]: 10618
% 0.21/0.56  % (29654)Time elapsed: 0.122 s
% 0.21/0.56  % (29654)------------------------------
% 0.21/0.56  % (29654)------------------------------
% 0.21/0.56  % (29638)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.56  % (29662)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 0.21/0.56  % (29658)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.57  % (29647)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.57  % (29647)Refutation not found, incomplete strategy% (29647)------------------------------
% 0.21/0.57  % (29647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (29647)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (29647)Memory used [KB]: 6140
% 0.21/0.57  % (29647)Time elapsed: 0.002 s
% 0.21/0.57  % (29647)------------------------------
% 0.21/0.57  % (29647)------------------------------
% 0.21/0.57  % (29663)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 0.21/0.58  % (29655)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.58  % (29662)Refutation not found, incomplete strategy% (29662)------------------------------
% 0.21/0.58  % (29662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (29662)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (29662)Memory used [KB]: 6140
% 0.21/0.58  % (29662)Time elapsed: 0.025 s
% 0.21/0.58  % (29662)------------------------------
% 0.21/0.58  % (29662)------------------------------
% 0.21/0.59  % (29641)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.59  % (29641)Refutation not found, incomplete strategy% (29641)------------------------------
% 0.21/0.59  % (29641)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (29641)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (29641)Memory used [KB]: 10618
% 0.21/0.59  % (29641)Time elapsed: 0.172 s
% 0.21/0.59  % (29641)------------------------------
% 0.21/0.59  % (29641)------------------------------
% 0.21/0.60  % (29635)Refutation found. Thanks to Tanya!
% 0.21/0.60  % SZS status Theorem for theBenchmark
% 0.21/0.60  % SZS output start Proof for theBenchmark
% 0.21/0.60  fof(f971,plain,(
% 0.21/0.60    $false),
% 0.21/0.60    inference(trivial_inequality_removal,[],[f970])).
% 0.21/0.60  fof(f970,plain,(
% 0.21/0.60    sK0 != sK0),
% 0.21/0.60    inference(superposition,[],[f38,f804])).
% 0.21/0.60  fof(f804,plain,(
% 0.21/0.60    ( ! [X30,X33] : (k2_xboole_0(X30,k4_xboole_0(X30,X33)) = X30) )),
% 0.21/0.60    inference(forward_demodulation,[],[f803,f722])).
% 0.21/0.60  fof(f722,plain,(
% 0.21/0.60    ( ! [X14,X15,X16] : (k4_xboole_0(X14,k4_xboole_0(k4_xboole_0(X15,X16),X15)) = X14) )),
% 0.21/0.60    inference(resolution,[],[f715,f260])).
% 0.21/0.60  fof(f260,plain,(
% 0.21/0.60    ( ! [X30,X31,X32] : (~r2_hidden(X32,k4_xboole_0(k4_xboole_0(X30,X31),X30))) )),
% 0.21/0.60    inference(subsumption_resolution,[],[f245,f34])).
% 0.21/0.60  fof(f34,plain,(
% 0.21/0.60    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 0.21/0.60    inference(equality_resolution,[],[f23])).
% 0.21/0.60  fof(f23,plain,(
% 0.21/0.60    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.60    inference(cnf_transformation,[],[f16])).
% 0.21/0.60  fof(f16,plain,(
% 0.21/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f15])).
% 0.21/0.60  fof(f15,plain,(
% 0.21/0.60    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f14,plain,(
% 0.21/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.60    inference(rectify,[],[f13])).
% 0.21/0.60  fof(f13,plain,(
% 0.21/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.60    inference(flattening,[],[f12])).
% 0.21/0.60  fof(f12,plain,(
% 0.21/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.60    inference(nnf_transformation,[],[f2])).
% 0.21/0.60  fof(f2,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.60  fof(f245,plain,(
% 0.21/0.60    ( ! [X30,X31,X32] : (~r2_hidden(X32,k4_xboole_0(k4_xboole_0(X30,X31),X30)) | ~r2_hidden(X32,k4_xboole_0(X30,X31))) )),
% 0.21/0.60    inference(superposition,[],[f33,f143])).
% 0.21/0.60  fof(f143,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.60    inference(superposition,[],[f110,f30])).
% 0.21/0.60  fof(f30,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.60    inference(definition_unfolding,[],[f21,f19])).
% 0.21/0.60  fof(f19,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f6])).
% 0.21/0.60  fof(f6,axiom,(
% 0.21/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.60  fof(f21,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f5])).
% 0.21/0.60  fof(f5,axiom,(
% 0.21/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.60  fof(f110,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 0.21/0.60    inference(superposition,[],[f70,f31])).
% 0.21/0.60  fof(f31,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 0.21/0.60    inference(definition_unfolding,[],[f22,f19])).
% 0.21/0.60  fof(f22,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f3])).
% 0.21/0.60  fof(f3,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).
% 0.21/0.60  fof(f70,plain,(
% 0.21/0.60    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X5))) )),
% 0.21/0.60    inference(superposition,[],[f55,f18])).
% 0.21/0.60  fof(f18,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f1])).
% 0.21/0.60  fof(f1,axiom,(
% 0.21/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.60  fof(f55,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X1))) )),
% 0.21/0.60    inference(superposition,[],[f31,f30])).
% 0.21/0.60  fof(f33,plain,(
% 0.21/0.60    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.21/0.60    inference(equality_resolution,[],[f24])).
% 0.21/0.60  fof(f24,plain,(
% 0.21/0.60    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.60    inference(cnf_transformation,[],[f16])).
% 0.21/0.60  fof(f715,plain,(
% 0.21/0.60    ( ! [X4,X3] : (r2_hidden(sK2(X3,X4,X3),X4) | k4_xboole_0(X3,X4) = X3) )),
% 0.21/0.60    inference(subsumption_resolution,[],[f713,f26])).
% 0.21/0.60  fof(f26,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.60    inference(cnf_transformation,[],[f16])).
% 0.21/0.60  fof(f713,plain,(
% 0.21/0.60    ( ! [X4,X3] : (r2_hidden(sK2(X3,X4,X3),X4) | ~r2_hidden(sK2(X3,X4,X3),X3) | k4_xboole_0(X3,X4) = X3) )),
% 0.21/0.60    inference(duplicate_literal_removal,[],[f709])).
% 0.21/0.60  fof(f709,plain,(
% 0.21/0.60    ( ! [X4,X3] : (r2_hidden(sK2(X3,X4,X3),X4) | ~r2_hidden(sK2(X3,X4,X3),X3) | k4_xboole_0(X3,X4) = X3 | k4_xboole_0(X3,X4) = X3) )),
% 0.21/0.60    inference(resolution,[],[f28,f121])).
% 0.21/0.60  fof(f121,plain,(
% 0.21/0.60    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) )),
% 0.21/0.60    inference(factoring,[],[f26])).
% 0.21/0.60  fof(f28,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.60    inference(cnf_transformation,[],[f16])).
% 0.21/0.60  fof(f803,plain,(
% 0.21/0.60    ( ! [X30,X33,X31,X32] : (k4_xboole_0(X30,k4_xboole_0(k4_xboole_0(X31,X32),X31)) = k2_xboole_0(X30,k4_xboole_0(X30,X33))) )),
% 0.21/0.60    inference(forward_demodulation,[],[f758,f267])).
% 0.21/0.60  fof(f267,plain,(
% 0.21/0.60    ( ! [X17,X18,X16] : (k4_xboole_0(k4_xboole_0(X16,X17),X16) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X16,X17),X16),X18)) )),
% 0.21/0.60    inference(resolution,[],[f260,f121])).
% 0.21/0.60  fof(f758,plain,(
% 0.21/0.60    ( ! [X30,X33,X31,X32] : (k4_xboole_0(X30,k4_xboole_0(k4_xboole_0(k4_xboole_0(X31,X32),X31),k4_xboole_0(k4_xboole_0(k4_xboole_0(X31,X32),X31),X33))) = k2_xboole_0(X30,k4_xboole_0(X30,X33))) )),
% 0.21/0.60    inference(superposition,[],[f31,f722])).
% 0.21/0.60  fof(f38,plain,(
% 0.21/0.60    sK0 != k2_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.60    inference(superposition,[],[f37,f18])).
% 0.21/0.60  fof(f37,plain,(
% 0.21/0.60    sK0 != k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)),
% 0.21/0.60    inference(superposition,[],[f35,f20])).
% 0.21/0.60  fof(f20,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f4])).
% 0.21/0.60  fof(f4,axiom,(
% 0.21/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.60  fof(f35,plain,(
% 0.21/0.60    sK0 != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.21/0.60    inference(superposition,[],[f29,f18])).
% 0.21/0.60  fof(f29,plain,(
% 0.21/0.60    sK0 != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 0.21/0.60    inference(definition_unfolding,[],[f17,f19])).
% 0.21/0.60  fof(f17,plain,(
% 0.21/0.60    sK0 != k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 0.21/0.60    inference(cnf_transformation,[],[f11])).
% 0.21/0.60  fof(f11,plain,(
% 0.21/0.60    sK0 != k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).
% 0.21/0.60  fof(f10,plain,(
% 0.21/0.60    ? [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) != X0 => sK0 != k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f9,plain,(
% 0.21/0.60    ? [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) != X0),
% 0.21/0.60    inference(ennf_transformation,[],[f8])).
% 0.21/0.60  fof(f8,negated_conjecture,(
% 0.21/0.60    ~! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.60    inference(negated_conjecture,[],[f7])).
% 0.21/0.60  fof(f7,conjecture,(
% 0.21/0.60    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.60  % SZS output end Proof for theBenchmark
% 0.21/0.60  % (29635)------------------------------
% 0.21/0.60  % (29635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (29635)Termination reason: Refutation
% 0.21/0.60  
% 0.21/0.60  % (29635)Memory used [KB]: 11513
% 0.21/0.60  % (29635)Time elapsed: 0.192 s
% 0.21/0.60  % (29635)------------------------------
% 0.21/0.60  % (29635)------------------------------
% 2.02/0.62  % (29631)Success in time 0.252 s
%------------------------------------------------------------------------------
