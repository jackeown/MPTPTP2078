%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 153 expanded)
%              Number of leaves         :    8 (  35 expanded)
%              Depth                    :   20
%              Number of atoms          :  138 ( 485 expanded)
%              Number of equality atoms :   81 ( 324 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f87,plain,(
    $false ),
    inference(subsumption_resolution,[],[f86,f77])).

fof(f77,plain,(
    r2_hidden(sK1,k1_tarski(sK1)) ),
    inference(backward_demodulation,[],[f58,f67])).

fof(f67,plain,(
    sK1 = sK2 ),
    inference(resolution,[],[f57,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f57,plain,(
    ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(trivial_inequality_removal,[],[f56])).

fof(f56,plain,
    ( k1_tarski(sK1) != k1_tarski(sK1)
    | ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(superposition,[],[f50,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f50,plain,(
    k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(subsumption_resolution,[],[f48,f40])).

fof(f40,plain,(
    ! [X0] : sP0(X0,k1_tarski(X0)) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f4,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f48,plain,
    ( k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | ~ sP0(sK1,k1_tarski(sK1)) ),
    inference(resolution,[],[f46,f39])).

fof(f39,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ sP0(X3,X1) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f46,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(trivial_inequality_removal,[],[f45])).

fof(f45,plain,
    ( k1_tarski(sK1) != k1_tarski(sK1)
    | ~ r2_hidden(sK1,k1_tarski(sK1))
    | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(superposition,[],[f37,f43])).

fof(f43,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1))
    | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(trivial_inequality_removal,[],[f42])).

fof(f42,plain,
    ( sK1 != sK1
    | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1))
    | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(superposition,[],[f41,f26])).

fof(f26,plain,
    ( sK1 = sK2
    | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( sK1 = sK2
      | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) )
    & ( sK1 != sK2
      | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ( X0 = X1
          | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
        & ( X0 != X1
          | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) )
   => ( ( sK1 = sK2
        | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) )
      & ( sK1 != sK2
        | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( X0 = X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
      & ( X0 != X1
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <~> X0 != X1 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      <=> X0 != X1 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f41,plain,
    ( sK1 != sK2
    | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) ),
    inference(inner_rewriting,[],[f25])).

fof(f25,plain,
    ( sK1 != sK2
    | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f58,plain,(
    r2_hidden(sK1,k1_tarski(sK2)) ),
    inference(trivial_inequality_removal,[],[f55])).

fof(f55,plain,
    ( k1_tarski(sK1) != k1_tarski(sK1)
    | r2_hidden(sK1,k1_tarski(sK2)) ),
    inference(superposition,[],[f50,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f86,plain,(
    ~ r2_hidden(sK1,k1_tarski(sK1)) ),
    inference(trivial_inequality_removal,[],[f85])).

fof(f85,plain,
    ( k1_tarski(sK1) != k1_tarski(sK1)
    | ~ r2_hidden(sK1,k1_tarski(sK1)) ),
    inference(superposition,[],[f37,f78])).

fof(f78,plain,(
    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) ),
    inference(trivial_inequality_removal,[],[f71])).

fof(f71,plain,
    ( sK1 != sK1
    | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) ),
    inference(backward_demodulation,[],[f41,f67])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:22:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (2467)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.53  % (2464)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  % (2465)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % (2467)Refutation not found, incomplete strategy% (2467)------------------------------
% 0.22/0.53  % (2467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (2467)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (2467)Memory used [KB]: 1663
% 0.22/0.53  % (2467)Time elapsed: 0.093 s
% 0.22/0.53  % (2467)------------------------------
% 0.22/0.53  % (2467)------------------------------
% 0.22/0.54  % (2468)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.54  % (2462)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.54  % (2468)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f86,f77])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    r2_hidden(sK1,k1_tarski(sK1))),
% 0.22/0.54    inference(backward_demodulation,[],[f58,f67])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    sK1 = sK2),
% 0.22/0.54    inference(resolution,[],[f57,f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    k1_tarski(sK1) != k1_tarski(sK1) | ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 0.22/0.54    inference(superposition,[],[f50,f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 0.22/0.54    inference(unused_predicate_definition_removal,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 0.22/0.54    inference(subsumption_resolution,[],[f48,f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ( ! [X0] : (sP0(X0,k1_tarski(X0))) )),
% 0.22/0.54    inference(equality_resolution,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ( ! [X0,X1] : (sP0(X0,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k1_tarski(X0) != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> sP0(X0,X1))),
% 0.22/0.54    inference(definition_folding,[],[f4,f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | ~sP0(sK1,k1_tarski(sK1))),
% 0.22/0.54    inference(resolution,[],[f46,f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X3,X1] : (r2_hidden(X3,X1) | ~sP0(X3,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | ~sP0(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1] : ((sP0(X0,X1) | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 0.22/0.54    inference(rectify,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 0.22/0.54    inference(nnf_transformation,[],[f14])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ~r2_hidden(sK1,k1_tarski(sK1)) | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    k1_tarski(sK1) != k1_tarski(sK1) | ~r2_hidden(sK1,k1_tarski(sK1)) | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 0.22/0.54    inference(superposition,[],[f37,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    sK1 != sK1 | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 0.22/0.54    inference(superposition,[],[f41,f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    sK1 = sK2 | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    (sK1 = sK2 | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) & (sK1 != sK2 | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f16,f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ? [X0,X1] : ((X0 = X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) & (X0 != X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) => ((sK1 = sK2 | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) & (sK1 != sK2 | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ? [X0,X1] : ((X0 = X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) & (X0 != X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.22/0.54    inference(nnf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,plain,(
% 0.22/0.54    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <~> X0 != X1)),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.22/0.54    inference(negated_conjecture,[],[f7])).
% 0.22/0.54  fof(f7,conjecture,(
% 0.22/0.54    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    sK1 != sK2 | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1))),
% 0.22/0.54    inference(inner_rewriting,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    sK1 != sK2 | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 0.22/0.54    inference(nnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    r2_hidden(sK1,k1_tarski(sK2))),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    k1_tarski(sK1) != k1_tarski(sK1) | r2_hidden(sK1,k1_tarski(sK2))),
% 0.22/0.54    inference(superposition,[],[f50,f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ~r2_hidden(sK1,k1_tarski(sK1))),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f85])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    k1_tarski(sK1) != k1_tarski(sK1) | ~r2_hidden(sK1,k1_tarski(sK1))),
% 0.22/0.54    inference(superposition,[],[f37,f78])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1))),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f71])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    sK1 != sK1 | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1))),
% 0.22/0.54    inference(backward_demodulation,[],[f41,f67])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (2468)------------------------------
% 0.22/0.54  % (2468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (2468)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (2468)Memory used [KB]: 1663
% 0.22/0.54  % (2468)Time elapsed: 0.100 s
% 0.22/0.54  % (2468)------------------------------
% 0.22/0.54  % (2468)------------------------------
% 0.22/0.54  % (2465)Refutation not found, incomplete strategy% (2465)------------------------------
% 0.22/0.54  % (2465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (2481)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.54  % (2465)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (2465)Memory used [KB]: 6012
% 0.22/0.54  % (2465)Time elapsed: 0.093 s
% 0.22/0.54  % (2465)------------------------------
% 0.22/0.54  % (2465)------------------------------
% 0.22/0.55  % (2459)Success in time 0.175 s
%------------------------------------------------------------------------------
