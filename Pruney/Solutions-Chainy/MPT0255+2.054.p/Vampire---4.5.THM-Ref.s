%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 (  93 expanded)
%              Number of leaves         :   15 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  159 ( 210 expanded)
%              Number of equality atoms :   77 ( 106 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(subsumption_resolution,[],[f118,f73])).

fof(f73,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(resolution,[],[f71,f34])).

fof(f34,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).

% (3118)Termination reason: Refutation not found, incomplete strategy

% (3118)Memory used [KB]: 1663
% (3118)Time elapsed: 0.110 s
% (3118)------------------------------
% (3118)------------------------------
% (3109)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f71,plain,(
    ! [X0,X1] : r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(resolution,[],[f61,f60])).

% (3105)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
fof(f60,plain,(
    ! [X4,X2,X0] :
      ( ~ sP0(X0,X4,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( sK6(X0,X1,X2) != X0
              & sK6(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sK6(X0,X1,X2) = X0
            | sK6(X0,X1,X2) = X1
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK6(X0,X1,X2) != X0
            & sK6(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sK6(X0,X1,X2) = X0
          | sK6(X0,X1,X2) = X1
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f61,plain,(
    ! [X0,X1] : sP0(X1,X0,k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k3_enumset1(X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f48,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f41,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f6,f16])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f118,plain,(
    v1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f116,f33])).

fof(f33,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f116,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | v1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(superposition,[],[f56,f94])).

fof(f94,plain,(
    o_0_0_xboole_0 = k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK2),sK3)) ),
    inference(forward_demodulation,[],[f54,f66])).

fof(f66,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[],[f65,f33])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f36,f34])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f14,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f54,plain,(
    k1_xboole_0 = k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f32,f53,f52])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f39,f52])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f32,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)
   => k1_xboole_0 = k2_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f40,f53])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X0,X1))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X0,X1))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
     => ~ v1_xboole_0(k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:25:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (3110)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (3110)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (3126)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (3118)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (3118)Refutation not found, incomplete strategy% (3118)------------------------------
% 0.20/0.52  % (3118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f118,f73])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_xboole_0(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.20/0.52    inference(resolution,[],[f71,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).
% 0.20/0.52  % (3118)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (3118)Memory used [KB]: 1663
% 0.20/0.52  % (3118)Time elapsed: 0.110 s
% 0.20/0.52  % (3118)------------------------------
% 0.20/0.52  % (3118)------------------------------
% 0.20/0.52  % (3109)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.52    inference(rectify,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.52    inference(nnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.20/0.52    inference(resolution,[],[f61,f60])).
% 0.20/0.52  % (3105)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ( ! [X4,X2,X0] : (~sP0(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 0.20/0.52    inference(equality_resolution,[],[f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP0(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((sK6(X0,X1,X2) != X0 & sK6(X0,X1,X2) != X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X0 | sK6(X0,X1,X2) = X1 | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK6(X0,X1,X2) != X0 & sK6(X0,X1,X2) != X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X0 | sK6(X0,X1,X2) = X1 | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.20/0.52    inference(rectify,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.20/0.52    inference(flattening,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.20/0.52    inference(nnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X0,X1] : (sP0(X1,X0,k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.20/0.52    inference(equality_resolution,[],[f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_enumset1(X0,X0,X0,X0,X1) != X2) )),
% 0.20/0.52    inference(definition_unfolding,[],[f48,f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f38,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f41,f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 0.20/0.52    inference(nnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.20/0.52    inference(definition_folding,[],[f6,f16])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.20/0.52  fof(f118,plain,(
% 0.20/0.52    v1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f116,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    v1_xboole_0(o_0_0_xboole_0)),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    v1_xboole_0(o_0_0_xboole_0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).
% 0.20/0.52  fof(f116,plain,(
% 0.20/0.52    ~v1_xboole_0(o_0_0_xboole_0) | v1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 0.20/0.52    inference(superposition,[],[f56,f94])).
% 0.20/0.52  fof(f94,plain,(
% 0.20/0.52    o_0_0_xboole_0 = k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK2),sK3))),
% 0.20/0.52    inference(forward_demodulation,[],[f54,f66])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    o_0_0_xboole_0 = k1_xboole_0),
% 0.20/0.52    inference(resolution,[],[f65,f33])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(resolution,[],[f36,f34])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f14,f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    k1_xboole_0 = k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK2),sK3))),
% 0.20/0.52    inference(definition_unfolding,[],[f32,f53,f52])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f39,f52])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    k1_xboole_0 = k2_xboole_0(k2_tarski(sK1,sK2),sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    k1_xboole_0 = k2_xboole_0(k2_tarski(sK1,sK2),sK3)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) => k1_xboole_0 = k2_xboole_0(k2_tarski(sK1,sK2),sK3)),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.20/0.52    inference(negated_conjecture,[],[f11])).
% 0.20/0.52  fof(f11,conjecture,(
% 0.20/0.52    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f40,f53])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_xboole_0(k2_xboole_0(X0,X1)) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0,X1] : (~v1_xboole_0(k2_xboole_0(X0,X1)) | v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : (~v1_xboole_0(X0) => ~v1_xboole_0(k2_xboole_0(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_xboole_0)).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (3110)------------------------------
% 0.20/0.52  % (3110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (3110)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (3110)Memory used [KB]: 10746
% 0.20/0.52  % (3110)Time elapsed: 0.097 s
% 0.20/0.52  % (3110)------------------------------
% 0.20/0.52  % (3110)------------------------------
% 0.20/0.52  % (3103)Success in time 0.154 s
%------------------------------------------------------------------------------
