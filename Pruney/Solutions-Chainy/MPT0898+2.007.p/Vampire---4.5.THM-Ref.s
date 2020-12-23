%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:16 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 211 expanded)
%              Number of leaves         :    7 (  63 expanded)
%              Depth                    :   17
%              Number of atoms          :   91 ( 462 expanded)
%              Number of equality atoms :   90 ( 461 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f193,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f159,f51,f168,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

% (840)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f168,plain,(
    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(forward_demodulation,[],[f167,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f167,plain,(
    k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f159,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0) != k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f18,f22,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k3_zfmisc_1(X0,X0,X0) != k3_zfmisc_1(X1,X1,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k3_zfmisc_1(X0,X0,X0) != k3_zfmisc_1(X1,X1,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_mcart_1)).

fof(f51,plain,(
    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f17,f28,f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | X2 = X5 ) ),
    inference(definition_unfolding,[],[f26,f22,f22,f22])).

fof(f26,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).

fof(f28,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1) ),
    inference(definition_unfolding,[],[f16,f27,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f16,plain,(
    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( sK0 != sK1
    & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) )
   => ( sK0 != sK1
      & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_mcart_1)).

fof(f17,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f159,plain,(
    k1_xboole_0 != sK0 ),
    inference(backward_demodulation,[],[f17,f147])).

fof(f147,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f146,f19])).

fof(f146,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK1)
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f145])).

fof(f145,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK1,sK1)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK1,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f19,f125])).

fof(f125,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f118])).

% (846)Termination reason: Refutation not found, incomplete strategy
fof(f118,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f19,f94])).

fof(f94,plain,(
    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1) ),
    inference(backward_demodulation,[],[f28,f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.09  % Command    : run_vampire %s %d
% 0.08/0.28  % Computer   : n006.cluster.edu
% 0.08/0.28  % Model      : x86_64 x86_64
% 0.08/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.28  % Memory     : 8042.1875MB
% 0.08/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.28  % CPULimit   : 60
% 0.08/0.28  % WCLimit    : 600
% 0.08/0.28  % DateTime   : Tue Dec  1 16:21:37 EST 2020
% 0.08/0.28  % CPUTime    : 
% 0.13/0.39  % (836)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.13/0.40  % (835)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.13/0.40  % (836)Refutation found. Thanks to Tanya!
% 0.13/0.40  % SZS status Theorem for theBenchmark
% 0.13/0.41  % (854)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.13/0.41  % (834)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.13/0.41  % (846)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.13/0.41  % (846)Refutation not found, incomplete strategy% (846)------------------------------
% 0.13/0.41  % (846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.41  % (844)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.13/0.41  % SZS output start Proof for theBenchmark
% 0.13/0.41  fof(f193,plain,(
% 0.13/0.41    $false),
% 0.13/0.41    inference(unit_resulting_resolution,[],[f159,f51,f168,f19])).
% 0.13/0.41  fof(f19,plain,(
% 0.13/0.41    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.13/0.41    inference(cnf_transformation,[],[f15])).
% 0.13/0.41  fof(f15,plain,(
% 0.13/0.41    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.13/0.41    inference(flattening,[],[f14])).
% 0.13/0.41  fof(f14,plain,(
% 0.13/0.41    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.13/0.41    inference(nnf_transformation,[],[f1])).
% 0.13/0.41  % (840)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.13/0.41  fof(f1,axiom,(
% 0.13/0.41    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.13/0.41  fof(f168,plain,(
% 0.13/0.41    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)),
% 0.13/0.41    inference(forward_demodulation,[],[f167,f33])).
% 0.13/0.41  fof(f33,plain,(
% 0.13/0.41    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.13/0.41    inference(equality_resolution,[],[f21])).
% 0.13/0.41  fof(f21,plain,(
% 0.13/0.41    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.13/0.41    inference(cnf_transformation,[],[f15])).
% 0.13/0.41  fof(f167,plain,(
% 0.13/0.41    k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 0.13/0.41    inference(unit_resulting_resolution,[],[f159,f29])).
% 0.13/0.41  fof(f29,plain,(
% 0.13/0.41    ( ! [X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0) != k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1) | X0 = X1) )),
% 0.13/0.41    inference(definition_unfolding,[],[f18,f22,f22])).
% 0.13/0.41  fof(f22,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f2])).
% 0.13/0.41  fof(f2,axiom,(
% 0.13/0.41    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.13/0.41  fof(f18,plain,(
% 0.13/0.41    ( ! [X0,X1] : (X0 = X1 | k3_zfmisc_1(X0,X0,X0) != k3_zfmisc_1(X1,X1,X1)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f9])).
% 0.13/0.41  fof(f9,plain,(
% 0.13/0.41    ! [X0,X1] : (X0 = X1 | k3_zfmisc_1(X0,X0,X0) != k3_zfmisc_1(X1,X1,X1))),
% 0.13/0.41    inference(ennf_transformation,[],[f5])).
% 0.13/0.41  fof(f5,axiom,(
% 0.13/0.41    ! [X0,X1] : (k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) => X0 = X1)),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_mcart_1)).
% 0.13/0.41  fof(f51,plain,(
% 0.13/0.41    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)),
% 0.13/0.41    inference(unit_resulting_resolution,[],[f17,f28,f30])).
% 0.13/0.41  fof(f30,plain,(
% 0.13/0.41    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | X2 = X5) )),
% 0.13/0.41    inference(definition_unfolding,[],[f26,f22,f22,f22])).
% 0.13/0.41  fof(f26,plain,(
% 0.13/0.41    ( ! [X4,X2,X0,X5,X3,X1] : (X2 = X5 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f11])).
% 0.13/0.41  fof(f11,plain,(
% 0.13/0.41    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 0.13/0.41    inference(flattening,[],[f10])).
% 0.13/0.41  fof(f10,plain,(
% 0.13/0.41    ! [X0,X1,X2,X3,X4,X5] : (((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 0.13/0.41    inference(ennf_transformation,[],[f4])).
% 0.13/0.41  fof(f4,axiom,(
% 0.13/0.41    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)))),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).
% 0.13/0.41  fof(f28,plain,(
% 0.13/0.41    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1)),
% 0.13/0.41    inference(definition_unfolding,[],[f16,f27,f27])).
% 0.13/0.41  fof(f27,plain,(
% 0.13/0.41    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.13/0.41    inference(definition_unfolding,[],[f23,f22])).
% 0.13/0.41  fof(f23,plain,(
% 0.13/0.41    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f3])).
% 0.13/0.41  fof(f3,axiom,(
% 0.13/0.41    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.13/0.41  fof(f16,plain,(
% 0.13/0.41    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1)),
% 0.13/0.41    inference(cnf_transformation,[],[f13])).
% 0.13/0.41  fof(f13,plain,(
% 0.13/0.41    sK0 != sK1 & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1)),
% 0.13/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f12])).
% 0.13/0.41  fof(f12,plain,(
% 0.13/0.41    ? [X0,X1] : (X0 != X1 & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)) => (sK0 != sK1 & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1))),
% 0.13/0.41    introduced(choice_axiom,[])).
% 0.13/0.41  fof(f8,plain,(
% 0.13/0.41    ? [X0,X1] : (X0 != X1 & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1))),
% 0.13/0.41    inference(ennf_transformation,[],[f7])).
% 0.13/0.41  fof(f7,negated_conjecture,(
% 0.13/0.41    ~! [X0,X1] : (k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) => X0 = X1)),
% 0.13/0.41    inference(negated_conjecture,[],[f6])).
% 0.13/0.41  fof(f6,conjecture,(
% 0.13/0.41    ! [X0,X1] : (k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) => X0 = X1)),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_mcart_1)).
% 0.13/0.41  fof(f17,plain,(
% 0.13/0.41    sK0 != sK1),
% 0.13/0.41    inference(cnf_transformation,[],[f13])).
% 0.13/0.41  fof(f159,plain,(
% 0.13/0.41    k1_xboole_0 != sK0),
% 0.13/0.41    inference(backward_demodulation,[],[f17,f147])).
% 0.13/0.41  fof(f147,plain,(
% 0.13/0.41    k1_xboole_0 = sK1),
% 0.13/0.41    inference(subsumption_resolution,[],[f146,f19])).
% 0.13/0.41  fof(f146,plain,(
% 0.13/0.41    k1_xboole_0 = k2_zfmisc_1(sK1,sK1) | k1_xboole_0 = sK1),
% 0.13/0.41    inference(trivial_inequality_removal,[],[f145])).
% 0.13/0.41  fof(f145,plain,(
% 0.13/0.41    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(sK1,sK1) | k1_xboole_0 = sK1),
% 0.13/0.41    inference(duplicate_literal_removal,[],[f138])).
% 0.13/0.41  fof(f138,plain,(
% 0.13/0.41    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(sK1,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.13/0.41    inference(superposition,[],[f19,f125])).
% 0.13/0.41  fof(f125,plain,(
% 0.13/0.41    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) | k1_xboole_0 = sK1),
% 0.13/0.41    inference(trivial_inequality_removal,[],[f118])).
% 0.13/0.41  % (846)Termination reason: Refutation not found, incomplete strategy
% 0.13/0.41  fof(f118,plain,(
% 0.13/0.41    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) | k1_xboole_0 = sK1),
% 0.13/0.41    inference(superposition,[],[f19,f94])).
% 0.13/0.41  fof(f94,plain,(
% 0.13/0.41    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1)),
% 0.13/0.41    inference(backward_demodulation,[],[f28,f51])).
% 0.13/0.41  % SZS output end Proof for theBenchmark
% 0.13/0.41  % (836)------------------------------
% 0.13/0.41  % (836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.41  % (836)Termination reason: Refutation
% 0.13/0.41  
% 0.13/0.41  % (836)Memory used [KB]: 1791
% 0.13/0.41  % (836)Time elapsed: 0.086 s
% 0.13/0.41  % (836)------------------------------
% 0.13/0.41  % (836)------------------------------
% 0.13/0.41  
% 0.13/0.42  % (846)Memory used [KB]: 1663
% 0.13/0.42  % (846)Time elapsed: 0.061 s
% 0.13/0.42  % (846)------------------------------
% 0.13/0.42  % (846)------------------------------
% 0.13/0.42  % (830)Success in time 0.126 s
%------------------------------------------------------------------------------
