%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:51 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 134 expanded)
%              Number of leaves         :   12 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :  172 ( 370 expanded)
%              Number of equality atoms :  123 ( 279 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f97,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f96])).

fof(f96,plain,(
    sK1 != sK1 ),
    inference(superposition,[],[f25,f82])).

fof(f82,plain,(
    sK1 = sK2 ),
    inference(resolution,[],[f77,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f42,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f13,f14])).

fof(f14,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f77,plain,(
    ! [X6,X8,X7] :
      ( ~ sP0(X6,X7,X8,k3_enumset1(sK2,sK2,sK2,sK2,sK1))
      | sK2 = X6 ) ),
    inference(resolution,[],[f74,f51])).

fof(f51,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | ~ sP0(X5,X1,X2,X3) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK3(X0,X1,X2,X3) != X0
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X0
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X2
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).

fof(f21,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK3(X0,X1,X2,X3) != X0
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X0
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X2
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f74,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k3_enumset1(sK2,sK2,sK2,sK2,sK1))
      | sK2 = X4 ) ),
    inference(duplicate_literal_removal,[],[f73])).

fof(f73,plain,(
    ! [X4] :
      ( sK2 = X4
      | sK2 = X4
      | ~ r2_hidden(X4,k3_enumset1(sK2,sK2,sK2,sK2,sK1))
      | sK2 = X4 ) ),
    inference(resolution,[],[f34,f69])).

fof(f69,plain,(
    sP0(sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK1)) ),
    inference(superposition,[],[f54,f61])).

fof(f61,plain,(
    k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k3_enumset1(sK2,sK2,sK2,sK2,sK1) ),
    inference(forward_demodulation,[],[f59,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)) ),
    inference(definition_unfolding,[],[f31,f45,f46,f46])).

fof(f46,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f26,f45])).

fof(f26,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f44])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f59,plain,(
    k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k2_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f55,f47])).

fof(f47,plain,(
    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f24,f46,f46,f46])).

fof(f24,plain,(
    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK1 != sK2
    & k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f12,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK1 != sK2
      & k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[],[f29,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f34,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | X1 = X5
      | X2 = X5
      | ~ r2_hidden(X5,X3)
      | X0 = X5 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f25,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:29:48 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.52  % (28668)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.52  % (28684)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.53  % (28657)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.53  % (28676)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.54  % (28668)Refutation found. Thanks to Tanya!
% 0.19/0.54  % SZS status Theorem for theBenchmark
% 0.19/0.54  % SZS output start Proof for theBenchmark
% 0.19/0.54  fof(f97,plain,(
% 0.19/0.54    $false),
% 0.19/0.54    inference(trivial_inequality_removal,[],[f96])).
% 0.19/0.54  fof(f96,plain,(
% 0.19/0.54    sK1 != sK1),
% 0.19/0.54    inference(superposition,[],[f25,f82])).
% 0.19/0.54  fof(f82,plain,(
% 0.19/0.54    sK1 = sK2),
% 0.19/0.54    inference(resolution,[],[f77,f54])).
% 0.19/0.54  fof(f54,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 0.19/0.54    inference(equality_resolution,[],[f50])).
% 0.19/0.54  fof(f50,plain,(
% 0.19/0.54    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 0.19/0.54    inference(definition_unfolding,[],[f42,f44])).
% 0.19/0.54  fof(f44,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.19/0.54    inference(definition_unfolding,[],[f32,f33])).
% 0.19/0.54  fof(f33,plain,(
% 0.19/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f9])).
% 0.19/0.54  fof(f9,axiom,(
% 0.19/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.19/0.54  fof(f32,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f8])).
% 0.19/0.54  fof(f8,axiom,(
% 0.19/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.54  fof(f42,plain,(
% 0.19/0.54    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.19/0.54    inference(cnf_transformation,[],[f23])).
% 0.19/0.54  fof(f23,plain,(
% 0.19/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 0.19/0.54    inference(nnf_transformation,[],[f15])).
% 0.19/0.54  fof(f15,plain,(
% 0.19/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 0.19/0.54    inference(definition_folding,[],[f13,f14])).
% 0.19/0.54  fof(f14,plain,(
% 0.19/0.54    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.19/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.19/0.54  fof(f13,plain,(
% 0.19/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.19/0.54    inference(ennf_transformation,[],[f4])).
% 0.19/0.54  fof(f4,axiom,(
% 0.19/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.19/0.54  fof(f77,plain,(
% 0.19/0.54    ( ! [X6,X8,X7] : (~sP0(X6,X7,X8,k3_enumset1(sK2,sK2,sK2,sK2,sK1)) | sK2 = X6) )),
% 0.19/0.54    inference(resolution,[],[f74,f51])).
% 0.19/0.54  fof(f51,plain,(
% 0.19/0.54    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | ~sP0(X5,X1,X2,X3)) )),
% 0.19/0.54    inference(equality_resolution,[],[f37])).
% 0.19/0.54  fof(f37,plain,(
% 0.19/0.54    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f22])).
% 0.19/0.54  fof(f22,plain,(
% 0.19/0.54    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK3(X0,X1,X2,X3) != X0 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X2) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X0 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X2 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.19/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).
% 0.19/0.54  fof(f21,plain,(
% 0.19/0.54    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X0 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X2) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X0 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X2 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 0.19/0.54    introduced(choice_axiom,[])).
% 0.19/0.54  fof(f20,plain,(
% 0.19/0.54    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.19/0.54    inference(rectify,[],[f19])).
% 0.19/0.54  fof(f19,plain,(
% 0.19/0.54    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 0.19/0.54    inference(flattening,[],[f18])).
% 0.19/0.54  fof(f18,plain,(
% 0.19/0.54    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 0.19/0.54    inference(nnf_transformation,[],[f14])).
% 0.19/0.54  fof(f74,plain,(
% 0.19/0.54    ( ! [X4] : (~r2_hidden(X4,k3_enumset1(sK2,sK2,sK2,sK2,sK1)) | sK2 = X4) )),
% 0.19/0.54    inference(duplicate_literal_removal,[],[f73])).
% 0.19/0.54  fof(f73,plain,(
% 0.19/0.54    ( ! [X4] : (sK2 = X4 | sK2 = X4 | ~r2_hidden(X4,k3_enumset1(sK2,sK2,sK2,sK2,sK1)) | sK2 = X4) )),
% 0.19/0.54    inference(resolution,[],[f34,f69])).
% 0.19/0.54  fof(f69,plain,(
% 0.19/0.54    sP0(sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK1))),
% 0.19/0.54    inference(superposition,[],[f54,f61])).
% 0.19/0.54  fof(f61,plain,(
% 0.19/0.54    k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k3_enumset1(sK2,sK2,sK2,sK2,sK1)),
% 0.19/0.54    inference(forward_demodulation,[],[f59,f48])).
% 0.19/0.54  fof(f48,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))) )),
% 0.19/0.54    inference(definition_unfolding,[],[f31,f45,f46,f46])).
% 0.19/0.54  fof(f46,plain,(
% 0.19/0.54    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.19/0.54    inference(definition_unfolding,[],[f26,f45])).
% 0.19/0.54  fof(f26,plain,(
% 0.19/0.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f6])).
% 0.19/0.54  fof(f6,axiom,(
% 0.19/0.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.54  fof(f45,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.19/0.54    inference(definition_unfolding,[],[f30,f44])).
% 0.19/0.54  fof(f30,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f7])).
% 0.19/0.54  fof(f7,axiom,(
% 0.19/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.54  fof(f31,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.19/0.54    inference(cnf_transformation,[],[f5])).
% 0.19/0.54  fof(f5,axiom,(
% 0.19/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.19/0.54  fof(f59,plain,(
% 0.19/0.54    k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k2_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.19/0.54    inference(superposition,[],[f55,f47])).
% 0.19/0.54  fof(f47,plain,(
% 0.19/0.54    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 0.19/0.54    inference(definition_unfolding,[],[f24,f46,f46,f46])).
% 0.19/0.54  fof(f24,plain,(
% 0.19/0.54    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 0.19/0.54    inference(cnf_transformation,[],[f17])).
% 0.19/0.54  fof(f17,plain,(
% 0.19/0.54    sK1 != sK2 & k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 0.19/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f12,f16])).
% 0.19/0.54  fof(f16,plain,(
% 0.19/0.54    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK1 != sK2 & k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 0.19/0.54    introduced(choice_axiom,[])).
% 0.19/0.54  fof(f12,plain,(
% 0.19/0.54    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.19/0.54    inference(ennf_transformation,[],[f11])).
% 0.19/0.54  fof(f11,negated_conjecture,(
% 0.19/0.54    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.19/0.54    inference(negated_conjecture,[],[f10])).
% 0.19/0.54  fof(f10,conjecture,(
% 0.19/0.54    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).
% 0.19/0.54  fof(f55,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0) )),
% 0.19/0.54    inference(superposition,[],[f29,f28])).
% 0.19/0.54  fof(f28,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f2])).
% 0.19/0.54  fof(f2,axiom,(
% 0.19/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.54  fof(f29,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.19/0.54    inference(cnf_transformation,[],[f3])).
% 0.19/0.54  fof(f3,axiom,(
% 0.19/0.54    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.19/0.54  fof(f34,plain,(
% 0.19/0.54    ( ! [X2,X0,X5,X3,X1] : (~sP0(X0,X1,X2,X3) | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3) | X0 = X5) )),
% 0.19/0.54    inference(cnf_transformation,[],[f22])).
% 0.19/0.54  fof(f25,plain,(
% 0.19/0.54    sK1 != sK2),
% 0.19/0.54    inference(cnf_transformation,[],[f17])).
% 0.19/0.54  % SZS output end Proof for theBenchmark
% 0.19/0.54  % (28668)------------------------------
% 0.19/0.54  % (28668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (28668)Termination reason: Refutation
% 0.19/0.54  
% 0.19/0.54  % (28668)Memory used [KB]: 6268
% 0.19/0.54  % (28668)Time elapsed: 0.125 s
% 0.19/0.54  % (28668)------------------------------
% 0.19/0.54  % (28668)------------------------------
% 0.19/0.54  % (28655)Success in time 0.19 s
%------------------------------------------------------------------------------
