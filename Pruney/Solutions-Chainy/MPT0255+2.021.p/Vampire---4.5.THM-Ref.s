%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:37 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   37 (  39 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :    9
%              Number of atoms          :  125 ( 127 expanded)
%              Number of equality atoms :   68 (  70 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f78,plain,(
    $false ),
    inference(subsumption_resolution,[],[f76,f61])).

% (3015)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
fof(f61,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f60,f29])).

fof(f29,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f37,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f76,plain,(
    r2_hidden(sK0,k1_xboole_0) ),
    inference(superposition,[],[f50,f64])).

fof(f64,plain,(
    k1_xboole_0 = k2_tarski(sK0,sK1) ),
    inference(forward_demodulation,[],[f63,f30])).

fof(f63,plain,(
    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0) ),
    inference(resolution,[],[f38,f52])).

fof(f52,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f32,f28])).

fof(f28,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)
   => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f50,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
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
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
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
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:22:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (3017)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.50  % (3033)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.19/0.51  % (3012)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.19/0.51  % (3017)Refutation found. Thanks to Tanya!
% 1.19/0.51  % SZS status Theorem for theBenchmark
% 1.19/0.51  % SZS output start Proof for theBenchmark
% 1.19/0.51  fof(f78,plain,(
% 1.19/0.51    $false),
% 1.19/0.51    inference(subsumption_resolution,[],[f76,f61])).
% 1.19/0.51  % (3015)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.19/0.51  fof(f61,plain,(
% 1.19/0.51    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.19/0.51    inference(subsumption_resolution,[],[f60,f29])).
% 1.19/0.51  fof(f29,plain,(
% 1.19/0.51    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.19/0.51    inference(cnf_transformation,[],[f5])).
% 1.19/0.51  fof(f5,axiom,(
% 1.19/0.51    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.19/0.51  fof(f60,plain,(
% 1.19/0.51    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 1.19/0.51    inference(superposition,[],[f37,f30])).
% 1.19/0.51  fof(f30,plain,(
% 1.19/0.51    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.19/0.51    inference(cnf_transformation,[],[f4])).
% 1.19/0.51  fof(f4,axiom,(
% 1.19/0.51    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.19/0.51  fof(f37,plain,(
% 1.19/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.19/0.51    inference(cnf_transformation,[],[f22])).
% 1.19/0.51  fof(f22,plain,(
% 1.19/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f21])).
% 1.19/0.51  fof(f21,plain,(
% 1.19/0.51    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 1.19/0.51    introduced(choice_axiom,[])).
% 1.19/0.51  fof(f17,plain,(
% 1.19/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.19/0.51    inference(ennf_transformation,[],[f15])).
% 1.19/0.51  fof(f15,plain,(
% 1.19/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.19/0.51    inference(rectify,[],[f1])).
% 1.19/0.51  fof(f1,axiom,(
% 1.19/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.19/0.51  fof(f76,plain,(
% 1.19/0.51    r2_hidden(sK0,k1_xboole_0)),
% 1.19/0.51    inference(superposition,[],[f50,f64])).
% 1.19/0.51  fof(f64,plain,(
% 1.19/0.51    k1_xboole_0 = k2_tarski(sK0,sK1)),
% 1.19/0.51    inference(forward_demodulation,[],[f63,f30])).
% 1.19/0.51  fof(f63,plain,(
% 1.19/0.51    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0)),
% 1.19/0.51    inference(resolution,[],[f38,f52])).
% 1.19/0.51  fof(f52,plain,(
% 1.19/0.51    r1_tarski(k2_tarski(sK0,sK1),k1_xboole_0)),
% 1.19/0.51    inference(superposition,[],[f32,f28])).
% 1.19/0.51  fof(f28,plain,(
% 1.19/0.51    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.19/0.51    inference(cnf_transformation,[],[f20])).
% 1.19/0.51  fof(f20,plain,(
% 1.19/0.51    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f19])).
% 1.19/0.51  fof(f19,plain,(
% 1.19/0.51    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.19/0.51    introduced(choice_axiom,[])).
% 1.19/0.51  fof(f16,plain,(
% 1.19/0.51    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.19/0.51    inference(ennf_transformation,[],[f14])).
% 1.19/0.51  fof(f14,negated_conjecture,(
% 1.19/0.51    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.19/0.51    inference(negated_conjecture,[],[f13])).
% 1.19/0.51  fof(f13,conjecture,(
% 1.19/0.51    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 1.19/0.51  fof(f32,plain,(
% 1.19/0.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.19/0.51    inference(cnf_transformation,[],[f6])).
% 1.19/0.51  fof(f6,axiom,(
% 1.19/0.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.19/0.51  fof(f38,plain,(
% 1.19/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.19/0.51    inference(cnf_transformation,[],[f18])).
% 1.19/0.51  fof(f18,plain,(
% 1.19/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.19/0.51    inference(ennf_transformation,[],[f3])).
% 1.19/0.51  fof(f3,axiom,(
% 1.19/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.19/0.51  fof(f50,plain,(
% 1.19/0.51    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 1.19/0.51    inference(equality_resolution,[],[f49])).
% 1.19/0.51  fof(f49,plain,(
% 1.19/0.51    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 1.19/0.51    inference(equality_resolution,[],[f41])).
% 1.19/0.51  fof(f41,plain,(
% 1.19/0.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.19/0.51    inference(cnf_transformation,[],[f27])).
% 1.19/0.51  fof(f27,plain,(
% 1.19/0.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).
% 1.19/0.51  fof(f26,plain,(
% 1.19/0.51    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.19/0.51    introduced(choice_axiom,[])).
% 1.19/0.51  fof(f25,plain,(
% 1.19/0.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.19/0.51    inference(rectify,[],[f24])).
% 1.19/0.51  fof(f24,plain,(
% 1.19/0.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.19/0.51    inference(flattening,[],[f23])).
% 1.19/0.51  fof(f23,plain,(
% 1.19/0.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.19/0.51    inference(nnf_transformation,[],[f8])).
% 1.19/0.51  fof(f8,axiom,(
% 1.19/0.51    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.19/0.51  % SZS output end Proof for theBenchmark
% 1.19/0.51  % (3017)------------------------------
% 1.19/0.51  % (3017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.51  % (3017)Termination reason: Refutation
% 1.19/0.51  
% 1.19/0.51  % (3017)Memory used [KB]: 1791
% 1.19/0.51  % (3017)Time elapsed: 0.105 s
% 1.19/0.51  % (3017)------------------------------
% 1.19/0.51  % (3017)------------------------------
% 1.19/0.52  % (3009)Success in time 0.16 s
%------------------------------------------------------------------------------
