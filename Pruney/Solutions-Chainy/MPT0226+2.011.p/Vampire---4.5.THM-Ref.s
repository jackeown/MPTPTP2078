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
% DateTime   : Thu Dec  3 12:36:15 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   55 (  89 expanded)
%              Number of leaves         :   13 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :  131 ( 208 expanded)
%              Number of equality atoms :   70 ( 130 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f105,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f104])).

fof(f104,plain,(
    sK0 != sK0 ),
    inference(superposition,[],[f33,f102])).

fof(f102,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f88,f71])).

fof(f71,plain,(
    ! [X3] : r2_hidden(X3,k1_enumset1(X3,X3,X3)) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_enumset1(X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f39,f54])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f88,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_enumset1(sK0,sK0,sK0))
      | sK0 = sK1 ) ),
    inference(backward_demodulation,[],[f87,f82])).

fof(f82,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f81,f44])).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f81,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f56,f64])).

fof(f64,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f46,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f87,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_xboole_0))
      | sK0 = sK1 ) ),
    inference(resolution,[],[f78,f72])).

fof(f72,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_enumset1(X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f38,f54])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f78,plain,(
    ! [X0] :
      ( r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1))
      | ~ r2_hidden(X0,k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_xboole_0)) ) ),
    inference(resolution,[],[f75,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_enumset1(X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f54])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f75,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_xboole_0))
      | ~ r1_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) ) ),
    inference(superposition,[],[f65,f58])).

fof(f58,plain,(
    k1_xboole_0 = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f32,f54,f54])).

fof(f32,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( sK0 != sK1
    & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f34])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f33,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 10:06:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.52  % (13734)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.23/0.52  % (13717)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.23/0.53  % (13728)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.23/0.53  % (13720)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.23/0.54  % (13711)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.23/0.54  % (13720)Refutation not found, incomplete strategy% (13720)------------------------------
% 0.23/0.54  % (13720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (13720)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (13720)Memory used [KB]: 1791
% 0.23/0.54  % (13720)Time elapsed: 0.057 s
% 0.23/0.54  % (13720)------------------------------
% 0.23/0.54  % (13720)------------------------------
% 0.23/0.54  % (13711)Refutation found. Thanks to Tanya!
% 0.23/0.54  % SZS status Theorem for theBenchmark
% 0.23/0.54  % SZS output start Proof for theBenchmark
% 0.23/0.54  fof(f105,plain,(
% 0.23/0.54    $false),
% 0.23/0.54    inference(trivial_inequality_removal,[],[f104])).
% 0.23/0.54  fof(f104,plain,(
% 0.23/0.54    sK0 != sK0),
% 0.23/0.54    inference(superposition,[],[f33,f102])).
% 0.23/0.54  fof(f102,plain,(
% 0.23/0.54    sK0 = sK1),
% 0.23/0.54    inference(resolution,[],[f88,f71])).
% 0.23/0.54  fof(f71,plain,(
% 0.23/0.54    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 0.23/0.54    inference(equality_resolution,[],[f70])).
% 0.23/0.54  fof(f70,plain,(
% 0.23/0.54    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 0.23/0.54    inference(equality_resolution,[],[f61])).
% 0.23/0.54  fof(f61,plain,(
% 0.23/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 0.23/0.54    inference(definition_unfolding,[],[f39,f54])).
% 0.23/0.54  fof(f54,plain,(
% 0.23/0.54    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.23/0.54    inference(definition_unfolding,[],[f43,f51])).
% 0.23/0.54  fof(f51,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f14])).
% 0.23/0.54  fof(f14,axiom,(
% 0.23/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.23/0.54  fof(f43,plain,(
% 0.23/0.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f13])).
% 0.23/0.54  fof(f13,axiom,(
% 0.23/0.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.23/0.54  fof(f39,plain,(
% 0.23/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.23/0.54    inference(cnf_transformation,[],[f29])).
% 0.23/0.54  fof(f29,plain,(
% 0.23/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.23/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 0.23/0.54  fof(f28,plain,(
% 0.23/0.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 0.23/0.54    introduced(choice_axiom,[])).
% 0.23/0.54  fof(f27,plain,(
% 0.23/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.23/0.54    inference(rectify,[],[f26])).
% 0.23/0.54  fof(f26,plain,(
% 0.23/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.23/0.54    inference(nnf_transformation,[],[f10])).
% 0.23/0.54  fof(f10,axiom,(
% 0.23/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.23/0.54  fof(f88,plain,(
% 0.23/0.54    ( ! [X0] : (~r2_hidden(X0,k1_enumset1(sK0,sK0,sK0)) | sK0 = sK1) )),
% 0.23/0.54    inference(backward_demodulation,[],[f87,f82])).
% 0.23/0.54  fof(f82,plain,(
% 0.23/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.54    inference(forward_demodulation,[],[f81,f44])).
% 0.23/0.54  fof(f44,plain,(
% 0.23/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.54    inference(cnf_transformation,[],[f6])).
% 0.23/0.54  fof(f6,axiom,(
% 0.23/0.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.23/0.54  fof(f81,plain,(
% 0.23/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 0.23/0.54    inference(superposition,[],[f56,f64])).
% 0.23/0.54  fof(f64,plain,(
% 0.23/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.23/0.54    inference(definition_unfolding,[],[f46,f34])).
% 0.23/0.54  fof(f34,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f5])).
% 0.23/0.54  fof(f5,axiom,(
% 0.23/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.23/0.54  fof(f46,plain,(
% 0.23/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f4])).
% 0.23/0.54  fof(f4,axiom,(
% 0.23/0.54    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.23/0.54  fof(f56,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.23/0.54    inference(definition_unfolding,[],[f35,f34])).
% 0.23/0.54  fof(f35,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f3])).
% 0.23/0.54  fof(f3,axiom,(
% 0.23/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.23/0.54  fof(f87,plain,(
% 0.23/0.54    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_xboole_0)) | sK0 = sK1) )),
% 0.23/0.54    inference(resolution,[],[f78,f72])).
% 0.23/0.54  fof(f72,plain,(
% 0.23/0.54    ( ! [X0,X3] : (~r2_hidden(X3,k1_enumset1(X0,X0,X0)) | X0 = X3) )),
% 0.23/0.54    inference(equality_resolution,[],[f62])).
% 0.23/0.54  fof(f62,plain,(
% 0.23/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 0.23/0.54    inference(definition_unfolding,[],[f38,f54])).
% 0.23/0.54  fof(f38,plain,(
% 0.23/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.23/0.54    inference(cnf_transformation,[],[f29])).
% 0.23/0.54  fof(f78,plain,(
% 0.23/0.54    ( ! [X0] : (r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1)) | ~r2_hidden(X0,k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_xboole_0))) )),
% 0.23/0.54    inference(resolution,[],[f75,f63])).
% 0.23/0.54  fof(f63,plain,(
% 0.23/0.54    ( ! [X0,X1] : (r1_xboole_0(k1_enumset1(X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.23/0.54    inference(definition_unfolding,[],[f42,f54])).
% 0.23/0.54  fof(f42,plain,(
% 0.23/0.54    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f22])).
% 0.23/0.54  fof(f22,plain,(
% 0.23/0.54    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.23/0.54    inference(ennf_transformation,[],[f17])).
% 0.23/0.54  fof(f17,axiom,(
% 0.23/0.54    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.23/0.54  fof(f75,plain,(
% 0.23/0.54    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_xboole_0)) | ~r1_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))) )),
% 0.23/0.54    inference(superposition,[],[f65,f58])).
% 0.23/0.54  fof(f58,plain,(
% 0.23/0.54    k1_xboole_0 = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))),
% 0.23/0.54    inference(definition_unfolding,[],[f32,f54,f54])).
% 0.23/0.54  fof(f32,plain,(
% 0.23/0.54    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.23/0.54    inference(cnf_transformation,[],[f25])).
% 0.23/0.54  fof(f25,plain,(
% 0.23/0.54    sK0 != sK1 & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.23/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f24])).
% 0.23/0.54  fof(f24,plain,(
% 0.23/0.54    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.23/0.54    introduced(choice_axiom,[])).
% 0.23/0.54  fof(f21,plain,(
% 0.23/0.54    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.23/0.54    inference(ennf_transformation,[],[f19])).
% 0.23/0.54  fof(f19,negated_conjecture,(
% 0.23/0.54    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.23/0.54    inference(negated_conjecture,[],[f18])).
% 0.23/0.54  fof(f18,conjecture,(
% 0.23/0.54    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).
% 0.23/0.54  fof(f65,plain,(
% 0.23/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 0.23/0.54    inference(definition_unfolding,[],[f48,f34])).
% 0.23/0.54  fof(f48,plain,(
% 0.23/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f31])).
% 0.23/0.54  fof(f31,plain,(
% 0.23/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.23/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f30])).
% 0.23/0.54  fof(f30,plain,(
% 0.23/0.54    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.23/0.54    introduced(choice_axiom,[])).
% 0.23/0.54  fof(f23,plain,(
% 0.23/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.23/0.54    inference(ennf_transformation,[],[f20])).
% 0.23/0.54  fof(f20,plain,(
% 0.23/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.23/0.54    inference(rectify,[],[f2])).
% 0.23/0.54  fof(f2,axiom,(
% 0.23/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.23/0.54  fof(f33,plain,(
% 0.23/0.54    sK0 != sK1),
% 0.23/0.54    inference(cnf_transformation,[],[f25])).
% 0.23/0.54  % SZS output end Proof for theBenchmark
% 0.23/0.54  % (13711)------------------------------
% 0.23/0.54  % (13711)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (13711)Termination reason: Refutation
% 0.23/0.54  
% 0.23/0.54  % (13711)Memory used [KB]: 1791
% 0.23/0.54  % (13711)Time elapsed: 0.072 s
% 0.23/0.54  % (13711)------------------------------
% 0.23/0.54  % (13711)------------------------------
% 0.23/0.54  % (13699)Success in time 0.168 s
%------------------------------------------------------------------------------
