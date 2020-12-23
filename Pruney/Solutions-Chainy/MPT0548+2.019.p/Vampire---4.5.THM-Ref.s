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
% DateTime   : Thu Dec  3 12:49:24 EST 2020

% Result     : Theorem 1.14s
% Output     : Refutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :   48 (  58 expanded)
%              Number of leaves         :   13 (  17 expanded)
%              Depth                    :   16
%              Number of atoms          :  140 ( 162 expanded)
%              Number of equality atoms :   46 (  56 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f93,plain,(
    $false ),
    inference(subsumption_resolution,[],[f33,f92])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f91,f39])).

fof(f39,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f91,plain,(
    ! [X0] : k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f90,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

fof(f90,plain,(
    ! [X0] : k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k7_relat_1(k1_xboole_0,X0)) ),
    inference(resolution,[],[f87,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f87,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,
    ( v1_relat_1(k1_xboole_0)
    | v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f83,f40])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f83,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1(X0),k1_xboole_0)
      | v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f81,f35])).

fof(f35,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f81,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1(X0),k5_xboole_0(k1_xboole_0,k1_xboole_0))
      | v1_relat_1(X0) ) ),
    inference(superposition,[],[f78,f75])).

fof(f75,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f56,f67])).

fof(f67,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f43,f35])).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(definition_unfolding,[],[f36,f42])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(X0),k5_xboole_0(X1,k3_xboole_0(X1,X0)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f65,f40])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f45,f42])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f33,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f24])).

fof(f24,plain,
    ( ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:47:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (8944)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.14/0.52  % (8931)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.14/0.52  % (8934)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.14/0.52  % (8936)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.14/0.52  % (8935)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.14/0.53  % (8936)Refutation found. Thanks to Tanya!
% 1.14/0.53  % SZS status Theorem for theBenchmark
% 1.14/0.53  % SZS output start Proof for theBenchmark
% 1.14/0.53  fof(f93,plain,(
% 1.14/0.53    $false),
% 1.14/0.53    inference(subsumption_resolution,[],[f33,f92])).
% 1.14/0.53  fof(f92,plain,(
% 1.14/0.53    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 1.14/0.53    inference(forward_demodulation,[],[f91,f39])).
% 1.14/0.53  fof(f39,plain,(
% 1.14/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.14/0.53    inference(cnf_transformation,[],[f17])).
% 1.14/0.53  fof(f17,axiom,(
% 1.14/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.14/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.14/0.53  fof(f91,plain,(
% 1.14/0.53    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)) )),
% 1.14/0.53    inference(forward_demodulation,[],[f90,f37])).
% 1.14/0.53  fof(f37,plain,(
% 1.14/0.53    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 1.14/0.53    inference(cnf_transformation,[],[f15])).
% 1.14/0.53  fof(f15,axiom,(
% 1.14/0.53    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 1.14/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).
% 1.14/0.53  fof(f90,plain,(
% 1.14/0.53    ( ! [X0] : (k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k7_relat_1(k1_xboole_0,X0))) )),
% 1.14/0.53    inference(resolution,[],[f87,f34])).
% 1.14/0.53  fof(f34,plain,(
% 1.14/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.14/0.53    inference(cnf_transformation,[],[f22])).
% 1.14/0.53  fof(f22,plain,(
% 1.14/0.53    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.14/0.53    inference(ennf_transformation,[],[f16])).
% 1.14/0.53  fof(f16,axiom,(
% 1.14/0.53    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.14/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.14/0.53  fof(f87,plain,(
% 1.14/0.53    v1_relat_1(k1_xboole_0)),
% 1.14/0.53    inference(duplicate_literal_removal,[],[f85])).
% 1.14/0.53  fof(f85,plain,(
% 1.14/0.53    v1_relat_1(k1_xboole_0) | v1_relat_1(k1_xboole_0)),
% 1.14/0.53    inference(resolution,[],[f83,f40])).
% 1.14/0.53  fof(f40,plain,(
% 1.14/0.53    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_relat_1(X0)) )),
% 1.14/0.53    inference(cnf_transformation,[],[f27])).
% 1.14/0.53  fof(f27,plain,(
% 1.14/0.53    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 1.14/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f26])).
% 1.14/0.53  fof(f26,plain,(
% 1.14/0.53    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 1.14/0.53    introduced(choice_axiom,[])).
% 1.14/0.53  fof(f23,plain,(
% 1.14/0.53    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.14/0.53    inference(ennf_transformation,[],[f20])).
% 1.14/0.53  fof(f20,plain,(
% 1.14/0.53    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 1.14/0.53    inference(unused_predicate_definition_removal,[],[f14])).
% 1.14/0.53  fof(f14,axiom,(
% 1.14/0.53    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.14/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 1.14/0.53  fof(f83,plain,(
% 1.14/0.53    ( ! [X0] : (~r2_hidden(sK1(X0),k1_xboole_0) | v1_relat_1(X0)) )),
% 1.14/0.53    inference(forward_demodulation,[],[f81,f35])).
% 1.14/0.53  fof(f35,plain,(
% 1.14/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.14/0.53    inference(cnf_transformation,[],[f7])).
% 1.14/0.53  fof(f7,axiom,(
% 1.14/0.53    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.14/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.14/0.53  fof(f81,plain,(
% 1.14/0.53    ( ! [X0] : (~r2_hidden(sK1(X0),k5_xboole_0(k1_xboole_0,k1_xboole_0)) | v1_relat_1(X0)) )),
% 1.14/0.53    inference(superposition,[],[f78,f75])).
% 1.14/0.53  fof(f75,plain,(
% 1.14/0.53    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) )),
% 1.14/0.53    inference(superposition,[],[f56,f67])).
% 1.14/0.53  fof(f67,plain,(
% 1.14/0.53    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.14/0.53    inference(superposition,[],[f43,f35])).
% 1.14/0.53  fof(f43,plain,(
% 1.14/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.14/0.53    inference(cnf_transformation,[],[f1])).
% 1.14/0.53  fof(f1,axiom,(
% 1.14/0.53    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.14/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.14/0.53  fof(f56,plain,(
% 1.14/0.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 1.14/0.53    inference(definition_unfolding,[],[f36,f42])).
% 1.14/0.53  fof(f42,plain,(
% 1.14/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.14/0.53    inference(cnf_transformation,[],[f4])).
% 1.14/0.53  fof(f4,axiom,(
% 1.14/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.14/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.14/0.53  fof(f36,plain,(
% 1.14/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.14/0.53    inference(cnf_transformation,[],[f6])).
% 1.14/0.53  fof(f6,axiom,(
% 1.14/0.53    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.14/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.14/0.53  fof(f78,plain,(
% 1.14/0.53    ( ! [X0,X1] : (~r2_hidden(sK1(X0),k5_xboole_0(X1,k3_xboole_0(X1,X0))) | v1_relat_1(X0)) )),
% 1.14/0.53    inference(resolution,[],[f65,f40])).
% 1.14/0.53  fof(f65,plain,(
% 1.14/0.53    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.14/0.53    inference(equality_resolution,[],[f61])).
% 1.14/0.53  fof(f61,plain,(
% 1.14/0.53    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.14/0.53    inference(definition_unfolding,[],[f45,f42])).
% 1.14/0.53  fof(f45,plain,(
% 1.14/0.53    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.14/0.53    inference(cnf_transformation,[],[f32])).
% 1.14/0.53  fof(f32,plain,(
% 1.14/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.14/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 1.14/0.53  fof(f31,plain,(
% 1.14/0.53    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.14/0.53    introduced(choice_axiom,[])).
% 1.14/0.53  fof(f30,plain,(
% 1.14/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.14/0.53    inference(rectify,[],[f29])).
% 1.14/0.53  fof(f29,plain,(
% 1.14/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.14/0.53    inference(flattening,[],[f28])).
% 1.14/0.53  fof(f28,plain,(
% 1.14/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.14/0.53    inference(nnf_transformation,[],[f3])).
% 1.14/0.53  fof(f3,axiom,(
% 1.14/0.53    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.14/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.14/0.53  fof(f33,plain,(
% 1.14/0.53    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 1.14/0.53    inference(cnf_transformation,[],[f25])).
% 1.14/0.53  fof(f25,plain,(
% 1.14/0.53    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 1.14/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f24])).
% 1.14/0.53  fof(f24,plain,(
% 1.14/0.53    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 1.14/0.53    introduced(choice_axiom,[])).
% 1.14/0.53  fof(f21,plain,(
% 1.14/0.53    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 1.14/0.53    inference(ennf_transformation,[],[f19])).
% 1.14/0.53  fof(f19,negated_conjecture,(
% 1.14/0.53    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 1.14/0.53    inference(negated_conjecture,[],[f18])).
% 1.14/0.53  fof(f18,conjecture,(
% 1.14/0.53    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 1.14/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
% 1.14/0.53  % SZS output end Proof for theBenchmark
% 1.14/0.53  % (8936)------------------------------
% 1.14/0.53  % (8936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.14/0.53  % (8936)Termination reason: Refutation
% 1.14/0.53  
% 1.14/0.53  % (8936)Memory used [KB]: 6268
% 1.14/0.53  % (8936)Time elapsed: 0.119 s
% 1.14/0.53  % (8936)------------------------------
% 1.14/0.53  % (8936)------------------------------
% 1.14/0.53  % (8932)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.31/0.54  % (8930)Success in time 0.166 s
%------------------------------------------------------------------------------
