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
% DateTime   : Thu Dec  3 12:49:29 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   57 (  73 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  137 ( 154 expanded)
%              Number of equality atoms :   82 (  99 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f174,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f117,f146,f43])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

% (19492)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f146,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f138,f42])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

fof(f138,plain,
    ( k1_xboole_0 != k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f36,f105])).

fof(f105,plain,(
    ! [X0] :
      ( k9_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f104,f40])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f104,plain,(
    ! [X0] :
      ( k9_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f60,f37])).

fof(f37,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f48,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).

fof(f36,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f27])).

fof(f27,plain,
    ( ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(f117,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f36,f103])).

fof(f103,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X7,k1_xboole_0)
      | X5 = X6 ) ),
    inference(forward_demodulation,[],[f102,f68])).

fof(f68,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
      | k2_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

fof(f102,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X7,k4_xboole_0(k2_tarski(X5,X5),k2_tarski(X5,X5)))
      | X5 = X6 ) ),
    inference(subsumption_resolution,[],[f101,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f49,f41,f41])).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f101,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X7,k4_xboole_0(k2_tarski(X5,X5),k2_tarski(X5,X5)))
      | ~ r1_xboole_0(k2_tarski(X5,X5),k2_tarski(X6,X6))
      | X5 = X6 ) ),
    inference(superposition,[],[f58,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f51,f41,f41,f41])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f45])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:53:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.49  % (19488)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.50  % (19488)Refutation found. Thanks to Tanya!
% 0.19/0.50  % SZS status Theorem for theBenchmark
% 0.19/0.50  % SZS output start Proof for theBenchmark
% 0.19/0.50  fof(f174,plain,(
% 0.19/0.50    $false),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f117,f146,f43])).
% 0.19/0.50  fof(f43,plain,(
% 0.19/0.50    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_relat_1(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f30])).
% 0.19/0.50  % (19492)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.50  fof(f30,plain,(
% 0.19/0.50    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f29])).
% 0.19/0.50  fof(f29,plain,(
% 0.19/0.50    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f20,plain,(
% 0.19/0.50    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f17])).
% 0.19/0.50  fof(f17,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 0.19/0.50    inference(unused_predicate_definition_removal,[],[f10])).
% 0.19/0.50  fof(f10,axiom,(
% 0.19/0.50    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.19/0.50  fof(f146,plain,(
% 0.19/0.50    ~v1_relat_1(k1_xboole_0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f138,f42])).
% 0.19/0.50  fof(f42,plain,(
% 0.19/0.50    ( ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f19])).
% 0.19/0.50  fof(f19,plain,(
% 0.19/0.50    ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f12])).
% 0.19/0.50  fof(f12,axiom,(
% 0.19/0.50    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).
% 0.19/0.50  fof(f138,plain,(
% 0.19/0.50    k1_xboole_0 != k9_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.19/0.50    inference(superposition,[],[f36,f105])).
% 0.19/0.50  fof(f105,plain,(
% 0.19/0.50    ( ! [X0] : (k9_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.19/0.50    inference(forward_demodulation,[],[f104,f40])).
% 0.19/0.50  fof(f40,plain,(
% 0.19/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f3])).
% 0.19/0.50  fof(f3,axiom,(
% 0.19/0.50    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.19/0.50  fof(f104,plain,(
% 0.19/0.50    ( ! [X0] : (k9_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) | ~v1_relat_1(k1_xboole_0)) )),
% 0.19/0.50    inference(superposition,[],[f60,f37])).
% 0.19/0.50  fof(f37,plain,(
% 0.19/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.19/0.50    inference(cnf_transformation,[],[f13])).
% 0.19/0.50  fof(f13,axiom,(
% 0.19/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.19/0.50  fof(f60,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 0.19/0.50    inference(definition_unfolding,[],[f48,f45])).
% 0.19/0.50  fof(f45,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f2])).
% 0.19/0.50  fof(f2,axiom,(
% 0.19/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.19/0.50  fof(f48,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f22])).
% 0.19/0.50  fof(f22,plain,(
% 0.19/0.50    ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.50    inference(ennf_transformation,[],[f11])).
% 0.19/0.50  fof(f11,axiom,(
% 0.19/0.50    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).
% 0.19/0.50  fof(f36,plain,(
% 0.19/0.50    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f28])).
% 0.19/0.50  fof(f28,plain,(
% 0.19/0.50    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f27])).
% 0.19/0.50  fof(f27,plain,(
% 0.19/0.50    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f18,plain,(
% 0.19/0.50    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 0.19/0.50    inference(ennf_transformation,[],[f15])).
% 0.19/0.50  fof(f15,negated_conjecture,(
% 0.19/0.50    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.19/0.50    inference(negated_conjecture,[],[f14])).
% 0.19/0.50  fof(f14,conjecture,(
% 0.19/0.50    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 0.19/0.50  fof(f117,plain,(
% 0.19/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f36,f103])).
% 0.19/0.50  fof(f103,plain,(
% 0.19/0.50    ( ! [X6,X7,X5] : (~r2_hidden(X7,k1_xboole_0) | X5 = X6) )),
% 0.19/0.50    inference(forward_demodulation,[],[f102,f68])).
% 0.19/0.50  fof(f68,plain,(
% 0.19/0.50    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X1,X2))) )),
% 0.19/0.50    inference(equality_resolution,[],[f56])).
% 0.19/0.50  fof(f56,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) | k2_tarski(X1,X2) != X0) )),
% 0.19/0.50    inference(cnf_transformation,[],[f35])).
% 0.19/0.50  fof(f35,plain,(
% 0.19/0.50    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))))),
% 0.19/0.50    inference(flattening,[],[f34])).
% 0.19/0.50  fof(f34,plain,(
% 0.19/0.50    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))))),
% 0.19/0.50    inference(nnf_transformation,[],[f24])).
% 0.19/0.50  fof(f24,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f9])).
% 0.19/0.50  fof(f9,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).
% 0.19/0.50  fof(f102,plain,(
% 0.19/0.50    ( ! [X6,X7,X5] : (~r2_hidden(X7,k4_xboole_0(k2_tarski(X5,X5),k2_tarski(X5,X5))) | X5 = X6) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f101,f61])).
% 0.19/0.50  fof(f61,plain,(
% 0.19/0.50    ( ! [X0,X1] : (r1_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) | X0 = X1) )),
% 0.19/0.50    inference(definition_unfolding,[],[f49,f41,f41])).
% 0.19/0.50  fof(f41,plain,(
% 0.19/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f6])).
% 0.19/0.50  fof(f6,axiom,(
% 0.19/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.50  fof(f49,plain,(
% 0.19/0.50    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.19/0.50    inference(cnf_transformation,[],[f23])).
% 0.19/0.50  fof(f23,plain,(
% 0.19/0.50    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.19/0.50    inference(ennf_transformation,[],[f7])).
% 0.19/0.50  fof(f7,axiom,(
% 0.19/0.50    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 0.19/0.50  fof(f101,plain,(
% 0.19/0.50    ( ! [X6,X7,X5] : (~r2_hidden(X7,k4_xboole_0(k2_tarski(X5,X5),k2_tarski(X5,X5))) | ~r1_xboole_0(k2_tarski(X5,X5),k2_tarski(X6,X6)) | X5 = X6) )),
% 0.19/0.50    inference(superposition,[],[f58,f62])).
% 0.19/0.50  fof(f62,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) | X0 = X1) )),
% 0.19/0.50    inference(definition_unfolding,[],[f51,f41,f41,f41])).
% 0.19/0.50  fof(f51,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.19/0.50    inference(cnf_transformation,[],[f33])).
% 0.19/0.50  fof(f33,plain,(
% 0.19/0.50    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.19/0.50    inference(nnf_transformation,[],[f8])).
% 0.19/0.50  fof(f8,axiom,(
% 0.19/0.50    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.19/0.50  fof(f58,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.50    inference(definition_unfolding,[],[f47,f45])).
% 0.19/0.50  fof(f47,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f32])).
% 0.19/0.50  fof(f32,plain,(
% 0.19/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f31])).
% 0.19/0.50  fof(f31,plain,(
% 0.19/0.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f21,plain,(
% 0.19/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.19/0.50    inference(ennf_transformation,[],[f16])).
% 0.19/0.50  fof(f16,plain,(
% 0.19/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.50    inference(rectify,[],[f1])).
% 0.19/0.50  fof(f1,axiom,(
% 0.19/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.19/0.50  % SZS output end Proof for theBenchmark
% 0.19/0.50  % (19488)------------------------------
% 0.19/0.50  % (19488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (19488)Termination reason: Refutation
% 0.19/0.50  
% 0.19/0.50  % (19488)Memory used [KB]: 1791
% 0.19/0.50  % (19488)Time elapsed: 0.086 s
% 0.19/0.50  % (19488)------------------------------
% 0.19/0.50  % (19488)------------------------------
% 0.19/0.50  % (19483)Success in time 0.146 s
%------------------------------------------------------------------------------
