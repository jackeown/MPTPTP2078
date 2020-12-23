%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 121 expanded)
%              Number of leaves         :    8 (  32 expanded)
%              Depth                    :   17
%              Number of atoms          :   97 ( 283 expanded)
%              Number of equality atoms :   53 ( 152 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f98,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f20,f96])).

fof(f96,plain,(
    ! [X2,X0] : X0 = X2 ),
    inference(subsumption_resolution,[],[f95,f33])).

fof(f33,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f95,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(sK0,sK0)
      | X0 = X2 ) ),
    inference(forward_demodulation,[],[f91,f78])).

fof(f78,plain,(
    ! [X2] : sK0 = X2 ),
    inference(subsumption_resolution,[],[f73,f21])).

fof(f21,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f73,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_xboole_0,k1_tarski(X2))
      | sK0 = X2 ) ),
    inference(superposition,[],[f51,f69])).

fof(f69,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f66,f21])).

fof(f66,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(sK0))
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(superposition,[],[f41,f61])).

fof(f61,plain,(
    k1_xboole_0 = k2_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f58,f20])).

fof(f58,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK1)
    | sK0 = sK2 ),
    inference(resolution,[],[f46,f51])).

fof(f46,plain,
    ( r1_tarski(k1_tarski(sK0),k1_tarski(sK2))
    | k1_xboole_0 = k2_tarski(sK0,sK1) ),
    inference(superposition,[],[f23,f44])).

fof(f44,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | k1_xboole_0 = k2_tarski(sK0,sK1) ),
    inference(resolution,[],[f28,f19])).

fof(f19,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) )
   => ( sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => X0 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f41,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k2_tarski(X2,X3),k1_tarski(X2))
      | k1_tarski(X2) = k2_tarski(X2,X3) ) ),
    inference(resolution,[],[f27,f23])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X1),k1_tarski(X0))
      | X0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X1),k1_tarski(X0))
      | X0 = X1
      | X0 = X1 ) ),
    inference(superposition,[],[f32,f22])).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))
      | X0 = X1
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f91,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(k1_tarski(X0),sK0)
      | X0 = X2 ) ),
    inference(condensation,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),sK0)
      | X0 = X1
      | X0 = X2 ) ),
    inference(backward_demodulation,[],[f32,f78])).

fof(f20,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:33:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (32340)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.49  % (32356)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.49  % (32337)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (32348)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.50  % (32339)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.50  % (32339)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f20,f96])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    ( ! [X2,X0] : (X0 = X2) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f95,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(flattening,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~r1_tarski(sK0,sK0) | X0 = X2) )),
% 0.21/0.50    inference(forward_demodulation,[],[f91,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X2] : (sK0 = X2) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f73,f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X2] : (~r1_tarski(k1_xboole_0,k1_tarski(X2)) | sK0 = X2) )),
% 0.21/0.50    inference(superposition,[],[f51,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    k1_xboole_0 = k1_tarski(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f66,f21])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ~r1_tarski(k1_xboole_0,k1_tarski(sK0)) | k1_xboole_0 = k1_tarski(sK0)),
% 0.21/0.50    inference(superposition,[],[f41,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    k1_xboole_0 = k2_tarski(sK0,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f58,f20])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    k1_xboole_0 = k2_tarski(sK0,sK1) | sK0 = sK2),
% 0.21/0.50    inference(resolution,[],[f46,f51])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    r1_tarski(k1_tarski(sK0),k1_tarski(sK2)) | k1_xboole_0 = k2_tarski(sK0,sK1)),
% 0.21/0.50    inference(superposition,[],[f23,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    k2_tarski(sK0,sK1) = k1_tarski(sK2) | k1_xboole_0 = k2_tarski(sK0,sK1)),
% 0.21/0.50    inference(resolution,[],[f28,f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))) => (sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 0.21/0.50    inference(negated_conjecture,[],[f9])).
% 0.21/0.50  fof(f9,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~r1_tarski(k2_tarski(X2,X3),k1_tarski(X2)) | k1_tarski(X2) = k2_tarski(X2,X3)) )),
% 0.21/0.50    inference(resolution,[],[f27,f23])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X1),k1_tarski(X0)) | X0 = X1) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X1),k1_tarski(X0)) | X0 = X1 | X0 = X1) )),
% 0.21/0.50    inference(superposition,[],[f32,f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) | X0 = X1 | X0 = X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (X0 = X2 | X0 = X1 | ~r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~r1_tarski(k1_tarski(X0),sK0) | X0 = X2) )),
% 0.21/0.50    inference(condensation,[],[f81])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_tarski(k1_tarski(X0),sK0) | X0 = X1 | X0 = X2) )),
% 0.21/0.50    inference(backward_demodulation,[],[f32,f78])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    sK0 != sK2),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (32339)------------------------------
% 0.21/0.50  % (32339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (32339)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (32339)Memory used [KB]: 1791
% 0.21/0.50  % (32339)Time elapsed: 0.096 s
% 0.21/0.50  % (32339)------------------------------
% 0.21/0.50  % (32339)------------------------------
% 0.21/0.50  % (32331)Success in time 0.144 s
%------------------------------------------------------------------------------
