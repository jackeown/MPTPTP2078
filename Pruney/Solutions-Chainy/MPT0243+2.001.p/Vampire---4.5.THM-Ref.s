%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 152 expanded)
%              Number of leaves         :    7 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  104 ( 488 expanded)
%              Number of equality atoms :    4 (  16 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f57,plain,(
    $false ),
    inference(subsumption_resolution,[],[f56,f49])).

fof(f49,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f48,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f48,plain,(
    ~ r1_tarski(k1_tarski(sK1),sK2) ),
    inference(subsumption_resolution,[],[f47,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,
    ( ~ r1_tarski(k1_tarski(sK1),sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(subsumption_resolution,[],[f46,f41])).

fof(f41,plain,(
    r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f38,f24])).

fof(f38,plain,(
    r1_tarski(k1_tarski(sK0),sK2) ),
    inference(subsumption_resolution,[],[f35,f25])).

fof(f35,plain,
    ( r1_tarski(k1_tarski(sK0),sK2)
    | r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f33,f19])).

fof(f19,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),sK2)
    | r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(sK0,sK2)
      | ~ r1_tarski(k2_tarski(sK0,sK1),sK2) )
    & ( ( r2_hidden(sK1,sK2)
        & r2_hidden(sK0,sK2) )
      | r1_tarski(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | ~ r1_tarski(k2_tarski(X0,X1),X2) )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | r1_tarski(k2_tarski(X0,X1),X2) ) )
   => ( ( ~ r2_hidden(sK1,sK2)
        | ~ r2_hidden(sK0,sK2)
        | ~ r1_tarski(k2_tarski(sK0,sK1),sK2) )
      & ( ( r2_hidden(sK1,sK2)
          & r2_hidden(sK0,sK2) )
        | r1_tarski(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r1_tarski(k1_tarski(X0),X2) ) ),
    inference(superposition,[],[f28,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f46,plain,
    ( ~ r1_tarski(k1_tarski(sK1),sK2)
    | ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(subsumption_resolution,[],[f42,f38])).

fof(f42,plain,
    ( ~ r1_tarski(k1_tarski(sK1),sK2)
    | ~ r1_tarski(k1_tarski(sK0),sK2)
    | ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f40,f21])).

fof(f21,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r1_tarski(k1_tarski(X1),X2)
      | ~ r1_tarski(k1_tarski(X0),X2) ) ),
    inference(superposition,[],[f29,f23])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f56,plain,(
    r2_hidden(sK1,sK2) ),
    inference(subsumption_resolution,[],[f51,f48])).

fof(f51,plain,
    ( r1_tarski(k1_tarski(sK1),sK2)
    | r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f36,f20])).

fof(f20,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),sK2)
    | r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X1,X0),X2)
      | r1_tarski(k1_tarski(X0),X2) ) ),
    inference(superposition,[],[f33,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:56:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (31385)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.46  % (31374)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (31374)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(subsumption_resolution,[],[f56,f49])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    ~r2_hidden(sK1,sK2)),
% 0.21/0.46    inference(resolution,[],[f48,f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.46    inference(nnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    ~r1_tarski(k1_tarski(sK1),sK2)),
% 0.21/0.46    inference(subsumption_resolution,[],[f47,f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    ~r1_tarski(k1_tarski(sK1),sK2) | ~r2_hidden(sK1,sK2)),
% 0.21/0.46    inference(subsumption_resolution,[],[f46,f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    r2_hidden(sK0,sK2)),
% 0.21/0.46    inference(resolution,[],[f38,f24])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    r1_tarski(k1_tarski(sK0),sK2)),
% 0.21/0.46    inference(subsumption_resolution,[],[f35,f25])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    r1_tarski(k1_tarski(sK0),sK2) | r2_hidden(sK0,sK2)),
% 0.21/0.46    inference(resolution,[],[f33,f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    r1_tarski(k2_tarski(sK0,sK1),sK2) | r2_hidden(sK0,sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    (~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~r1_tarski(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | r1_tarski(k2_tarski(sK0,sK1),sK2))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2))) => ((~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~r1_tarski(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | r1_tarski(k2_tarski(sK0,sK1),sK2)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.46    inference(flattening,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.46    inference(nnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.46    inference(ennf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.46    inference(negated_conjecture,[],[f7])).
% 0.21/0.46  fof(f7,conjecture,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r1_tarski(k1_tarski(X0),X2)) )),
% 0.21/0.46    inference(superposition,[],[f28,f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    ~r1_tarski(k1_tarski(sK1),sK2) | ~r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2)),
% 0.21/0.46    inference(subsumption_resolution,[],[f42,f38])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ~r1_tarski(k1_tarski(sK1),sK2) | ~r1_tarski(k1_tarski(sK0),sK2) | ~r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2)),
% 0.21/0.46    inference(resolution,[],[f40,f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ~r1_tarski(k2_tarski(sK0,sK1),sK2) | ~r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r1_tarski(k1_tarski(X1),X2) | ~r1_tarski(k1_tarski(X0),X2)) )),
% 0.21/0.46    inference(superposition,[],[f29,f23])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.46    inference(flattening,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    r2_hidden(sK1,sK2)),
% 0.21/0.46    inference(subsumption_resolution,[],[f51,f48])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    r1_tarski(k1_tarski(sK1),sK2) | r2_hidden(sK1,sK2)),
% 0.21/0.46    inference(resolution,[],[f36,f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    r1_tarski(k2_tarski(sK0,sK1),sK2) | r2_hidden(sK1,sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X1,X0),X2) | r1_tarski(k1_tarski(X0),X2)) )),
% 0.21/0.46    inference(superposition,[],[f33,f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (31374)------------------------------
% 0.21/0.46  % (31374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (31374)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (31374)Memory used [KB]: 1663
% 0.21/0.46  % (31374)Time elapsed: 0.046 s
% 0.21/0.46  % (31374)------------------------------
% 0.21/0.46  % (31374)------------------------------
% 0.21/0.46  % (31370)Success in time 0.1 s
%------------------------------------------------------------------------------
