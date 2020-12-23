%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 100 expanded)
%              Number of leaves         :    9 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  125 ( 338 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f92,plain,(
    $false ),
    inference(subsumption_resolution,[],[f91,f42])).

fof(f42,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f41,f27])).

fof(f27,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    & r1_xboole_0(sK1,sK3)
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(X0,X2)
        & r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK1,sK3)
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X3)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X3)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_xboole_1)).

fof(f41,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r1_xboole_0(sK1,sK3) ) ),
    inference(superposition,[],[f30,f40])).

fof(f40,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f36,f27])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f30,f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f14,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f10,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
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

fof(f91,plain,(
    r2_hidden(sK4(sK0,sK2),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f88,f25])).

fof(f25,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f88,plain,
    ( ~ r1_tarski(sK0,sK1)
    | r2_hidden(sK4(sK0,sK2),k1_xboole_0) ),
    inference(resolution,[],[f84,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ r1_tarski(k3_xboole_0(sK0,sK2),X0)
      | r2_hidden(sK4(sK0,sK2),X0) ) ),
    inference(resolution,[],[f49,f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f49,plain,(
    r2_hidden(sK4(sK0,sK2),k3_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f29,f28])).

fof(f28,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f84,plain,(
    ! [X2] :
      ( r1_tarski(k3_xboole_0(X2,sK2),k1_xboole_0)
      | ~ r1_tarski(X2,sK1) ) ),
    inference(resolution,[],[f81,f26])).

fof(f26,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK3)
      | r1_tarski(k3_xboole_0(X0,X1),k1_xboole_0)
      | ~ r1_tarski(X0,sK1) ) ),
    inference(superposition,[],[f31,f40])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:20:25 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.55  % (20158)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.57  % (20170)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.57  % (20173)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.57  % (20158)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f92,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(subsumption_resolution,[],[f91,f42])).
% 0.22/0.57  fof(f42,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f41,f27])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    r1_xboole_0(sK1,sK3)),
% 0.22/0.57    inference(cnf_transformation,[],[f16])).
% 0.22/0.57  fof(f16,plain,(
% 0.22/0.57    ~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK3) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1)),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f15])).
% 0.22/0.57  fof(f15,plain,(
% 0.22/0.57    ? [X0,X1,X2,X3] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK3) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f9,plain,(
% 0.22/0.57    ? [X0,X1,X2,X3] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 0.22/0.57    inference(flattening,[],[f8])).
% 0.22/0.57  fof(f8,plain,(
% 0.22/0.57    ? [X0,X1,X2,X3] : (~r1_xboole_0(X0,X2) & (r1_xboole_0(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 0.22/0.57    inference(ennf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,negated_conjecture,(
% 0.22/0.57    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.57    inference(negated_conjecture,[],[f5])).
% 0.22/0.57  fof(f5,conjecture,(
% 0.22/0.57    ! [X0,X1,X2,X3] : ((r1_xboole_0(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_xboole_1)).
% 0.22/0.57  fof(f41,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~r1_xboole_0(sK1,sK3)) )),
% 0.22/0.57    inference(superposition,[],[f30,f40])).
% 0.22/0.57  fof(f40,plain,(
% 0.22/0.57    k1_xboole_0 = k3_xboole_0(sK1,sK3)),
% 0.22/0.57    inference(resolution,[],[f36,f27])).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.57    inference(resolution,[],[f30,f35])).
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0)),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f14,f23])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f14,plain,(
% 0.22/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.57    inference(ennf_transformation,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f18])).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f10,f17])).
% 0.22/0.57  fof(f17,plain,(
% 0.22/0.57    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f10,plain,(
% 0.22/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.57    inference(ennf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,plain,(
% 0.22/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.57    inference(rectify,[],[f2])).
% 0.22/0.57  fof(f2,axiom,(
% 0.22/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.57  fof(f91,plain,(
% 0.22/0.57    r2_hidden(sK4(sK0,sK2),k1_xboole_0)),
% 0.22/0.57    inference(subsumption_resolution,[],[f88,f25])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    r1_tarski(sK0,sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f16])).
% 0.22/0.57  fof(f88,plain,(
% 0.22/0.57    ~r1_tarski(sK0,sK1) | r2_hidden(sK4(sK0,sK2),k1_xboole_0)),
% 0.22/0.57    inference(resolution,[],[f84,f53])).
% 0.22/0.57  fof(f53,plain,(
% 0.22/0.57    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK0,sK2),X0) | r2_hidden(sK4(sK0,sK2),X0)) )),
% 0.22/0.57    inference(resolution,[],[f49,f32])).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f22])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f21])).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f20,plain,(
% 0.22/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.57    inference(rectify,[],[f19])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.57    inference(nnf_transformation,[],[f13])).
% 0.22/0.57  fof(f13,plain,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.57  fof(f49,plain,(
% 0.22/0.57    r2_hidden(sK4(sK0,sK2),k3_xboole_0(sK0,sK2))),
% 0.22/0.57    inference(resolution,[],[f29,f28])).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    ~r1_xboole_0(sK0,sK2)),
% 0.22/0.57    inference(cnf_transformation,[],[f16])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f18])).
% 0.22/0.57  fof(f84,plain,(
% 0.22/0.57    ( ! [X2] : (r1_tarski(k3_xboole_0(X2,sK2),k1_xboole_0) | ~r1_tarski(X2,sK1)) )),
% 0.22/0.57    inference(resolution,[],[f81,f26])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    r1_tarski(sK2,sK3)),
% 0.22/0.57    inference(cnf_transformation,[],[f16])).
% 0.22/0.57  fof(f81,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(X1,sK3) | r1_tarski(k3_xboole_0(X0,X1),k1_xboole_0) | ~r1_tarski(X0,sK1)) )),
% 0.22/0.57    inference(superposition,[],[f31,f40])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f12])).
% 0.22/0.57  fof(f12,plain,(
% 0.22/0.57    ! [X0,X1,X2,X3] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.22/0.57    inference(flattening,[],[f11])).
% 0.22/0.57  fof(f11,plain,(
% 0.22/0.57    ! [X0,X1,X2,X3] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 0.22/0.57    inference(ennf_transformation,[],[f4])).
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_xboole_1)).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (20158)------------------------------
% 0.22/0.57  % (20158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (20158)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (20158)Memory used [KB]: 6268
% 0.22/0.57  % (20158)Time elapsed: 0.146 s
% 0.22/0.57  % (20158)------------------------------
% 0.22/0.57  % (20158)------------------------------
% 0.22/0.58  % (20152)Success in time 0.216 s
%------------------------------------------------------------------------------
