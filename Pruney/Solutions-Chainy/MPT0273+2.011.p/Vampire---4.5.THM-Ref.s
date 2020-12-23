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
% DateTime   : Thu Dec  3 12:41:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 486 expanded)
%              Number of leaves         :    4 ( 115 expanded)
%              Depth                    :   20
%              Number of atoms          :  155 (2188 expanded)
%              Number of equality atoms :   87 (1190 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f56,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f55,f54,f29])).

fof(f29,plain,(
    ! [X2,X1] :
      ( k2_tarski(X1,X1) = k4_xboole_0(k2_tarski(X1,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f20,f16])).

fof(f16,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

% (28979)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f2])).

% (28981)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(f54,plain,(
    k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK0),sK2) ),
    inference(forward_demodulation,[],[f53,f48])).

fof(f48,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f47,f37])).

fof(f37,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK0,sK0)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f34,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k2_tarski(X0,X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f17,f16])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,
    ( sK0 = sK1
    | r2_hidden(sK0,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK0,sK0) ),
    inference(resolution,[],[f33,f22])).

fof(f22,plain,
    ( ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f14,f16])).

fof(f14,plain,
    ( ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( ( ( sK0 != sK1
        & ~ r2_hidden(sK1,sK2) )
      | r2_hidden(sK0,sK2)
      | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( ( sK0 = sK1
          | r2_hidden(sK1,sK2) )
        & ~ r2_hidden(sK0,sK2) )
      | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2] :
        ( ( ( X0 != X1
            & ~ r2_hidden(X1,X2) )
          | r2_hidden(X0,X2)
          | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( ( X0 = X1
              | r2_hidden(X1,X2) )
            & ~ r2_hidden(X0,X2) )
          | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( ( sK0 != sK1
          & ~ r2_hidden(sK1,sK2) )
        | r2_hidden(sK0,sK2)
        | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( ( sK0 = sK1
            | r2_hidden(sK1,sK2) )
          & ~ r2_hidden(sK0,sK2) )
        | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2)
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2)
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_zfmisc_1)).

fof(f33,plain,
    ( r2_hidden(sK1,sK2)
    | sK0 = sK1 ),
    inference(trivial_inequality_removal,[],[f32])).

fof(f32,plain,
    ( k2_tarski(sK0,sK0) != k2_tarski(sK0,sK0)
    | r2_hidden(sK1,sK2)
    | sK0 = sK1 ),
    inference(duplicate_literal_removal,[],[f30])).

fof(f30,plain,
    ( k2_tarski(sK0,sK0) != k2_tarski(sK0,sK0)
    | r2_hidden(sK1,sK2)
    | sK0 = sK1
    | r2_hidden(sK1,sK2)
    | sK0 = sK1 ),
    inference(superposition,[],[f27,f23])).

fof(f23,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK0)
    | r2_hidden(sK1,sK2)
    | sK0 = sK1 ),
    inference(definition_unfolding,[],[f13,f16])).

fof(f13,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,sK2)
    | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f18,f16])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( X0 = X1
      | r2_hidden(X1,X2)
      | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f47,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK0)
    | sK0 = sK1 ),
    inference(duplicate_literal_removal,[],[f43])).

fof(f43,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK0)
    | sK0 = sK1
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK0) ),
    inference(resolution,[],[f35,f24])).

fof(f24,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f12,f16])).

fof(f12,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK2)
      | k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,sK1),sK2)
      | sK0 = sK1 ) ),
    inference(resolution,[],[f33,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f19,f16])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f53,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK0,sK0) ),
    inference(subsumption_resolution,[],[f52,f28])).

fof(f52,plain,
    ( r2_hidden(sK0,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK0,sK0) ),
    inference(trivial_inequality_removal,[],[f49])).

fof(f49,plain,
    ( sK0 != sK0
    | r2_hidden(sK0,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK0,sK0) ),
    inference(backward_demodulation,[],[f21,f48])).

fof(f21,plain,
    ( sK0 != sK1
    | r2_hidden(sK0,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f15,f16])).

fof(f15,plain,
    ( sK0 != sK1
    | r2_hidden(sK0,sK2)
    | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f55,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f51,f54])).

fof(f51,plain,
    ( k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),sK2)
    | ~ r2_hidden(sK0,sK2) ),
    inference(backward_demodulation,[],[f24,f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:55:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (28968)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.50  % (28988)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (28980)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (28985)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.51  % (28988)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f55,f54,f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X2,X1] : (k2_tarski(X1,X1) = k4_xboole_0(k2_tarski(X1,X1),X2) | r2_hidden(X1,X2)) )),
% 0.20/0.51    inference(equality_resolution,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | X0 != X1 | r2_hidden(X0,X2)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f20,f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.51  % (28979)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | X0 != X1 | r2_hidden(X0,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.20/0.51    inference(flattening,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.20/0.51    inference(nnf_transformation,[],[f2])).
% 0.20/0.51  % (28981)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK0),sK2)),
% 0.20/0.51    inference(forward_demodulation,[],[f53,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    sK0 = sK1),
% 0.20/0.51    inference(subsumption_resolution,[],[f47,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK0,sK0) | sK0 = sK1),
% 0.20/0.51    inference(subsumption_resolution,[],[f34,f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k2_tarski(X0,X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f17,f16])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    sK0 = sK1 | r2_hidden(sK0,sK2) | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK0,sK0)),
% 0.20/0.51    inference(resolution,[],[f33,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ~r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK0,sK0)),
% 0.20/0.51    inference(definition_unfolding,[],[f14,f16])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ~r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ((sK0 != sK1 & ~r2_hidden(sK1,sK2)) | r2_hidden(sK0,sK2) | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & (((sK0 = sK1 | r2_hidden(sK1,sK2)) & ~r2_hidden(sK0,sK2)) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).
% 0.20/0.51  fof(f8,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2))) => (((sK0 != sK1 & ~r2_hidden(sK1,sK2)) | r2_hidden(sK0,sK2) | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & (((sK0 = sK1 | r2_hidden(sK1,sK2)) & ~r2_hidden(sK0,sK2)) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f7,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.20/0.51    inference(flattening,[],[f6])).
% 0.20/0.51  fof(f6,plain,(
% 0.20/0.51    ? [X0,X1,X2] : ((((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.20/0.51    inference(nnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 0.20/0.51    inference(negated_conjecture,[],[f3])).
% 0.20/0.51  fof(f3,conjecture,(
% 0.20/0.51    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_zfmisc_1)).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    r2_hidden(sK1,sK2) | sK0 = sK1),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    k2_tarski(sK0,sK0) != k2_tarski(sK0,sK0) | r2_hidden(sK1,sK2) | sK0 = sK1),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    k2_tarski(sK0,sK0) != k2_tarski(sK0,sK0) | r2_hidden(sK1,sK2) | sK0 = sK1 | r2_hidden(sK1,sK2) | sK0 = sK1),
% 0.20/0.51    inference(superposition,[],[f27,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK0) | r2_hidden(sK1,sK2) | sK0 = sK1),
% 0.20/0.51    inference(definition_unfolding,[],[f13,f16])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    sK0 = sK1 | r2_hidden(sK1,sK2) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k2_tarski(X0,X0) != k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | X0 = X1) )),
% 0.20/0.51    inference(definition_unfolding,[],[f18,f16])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (X0 = X1 | r2_hidden(X1,X2) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK0) | sK0 = sK1),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK0) | sK0 = sK1 | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK0)),
% 0.20/0.51    inference(resolution,[],[f35,f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ~r2_hidden(sK0,sK2) | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK0)),
% 0.20/0.51    inference(definition_unfolding,[],[f12,f16])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ~r2_hidden(sK0,sK2) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(X0,sK2) | k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,sK1),sK2) | sK0 = sK1) )),
% 0.20/0.51    inference(resolution,[],[f33,f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f19,f16])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK0,sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f52,f28])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    r2_hidden(sK0,sK2) | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK0,sK0)),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    sK0 != sK0 | r2_hidden(sK0,sK2) | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK0,sK0)),
% 0.20/0.51    inference(backward_demodulation,[],[f21,f48])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    sK0 != sK1 | r2_hidden(sK0,sK2) | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK0,sK0)),
% 0.20/0.51    inference(definition_unfolding,[],[f15,f16])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    sK0 != sK1 | r2_hidden(sK0,sK2) | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ~r2_hidden(sK0,sK2)),
% 0.20/0.51    inference(subsumption_resolution,[],[f51,f54])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),sK2) | ~r2_hidden(sK0,sK2)),
% 0.20/0.51    inference(backward_demodulation,[],[f24,f48])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (28988)------------------------------
% 0.20/0.51  % (28988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (28988)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (28988)Memory used [KB]: 6268
% 0.20/0.51  % (28988)Time elapsed: 0.082 s
% 0.20/0.51  % (28988)------------------------------
% 0.20/0.51  % (28988)------------------------------
% 0.20/0.51  % (28965)Success in time 0.163 s
%------------------------------------------------------------------------------
