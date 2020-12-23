%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0680+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 325 expanded)
%              Number of leaves         :    8 (  80 expanded)
%              Depth                    :   19
%              Number of atoms          :  201 (1356 expanded)
%              Number of equality atoms :   80 ( 403 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f146,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f51,f91,f99])).

fof(f99,plain,(
    ! [X0] :
      ( k11_relat_1(sK0,X0) = k9_relat_1(sK0,k6_subset_1(k1_tarski(X0),k1_tarski(sK1(sK0))))
      | sK2(sK0) = X0 ) ),
    inference(forward_demodulation,[],[f94,f42])).

fof(f42,plain,(
    ! [X0] : k11_relat_1(sK0,X0) = k9_relat_1(sK0,k1_tarski(X0)) ),
    inference(resolution,[],[f28,f23])).

fof(f23,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

% (3382)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
fof(f17,plain,
    ( ~ v2_funct_1(sK0)
    & ! [X1,X2] : k9_relat_1(sK0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(sK0,X1),k9_relat_1(sK0,X2))
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ~ v2_funct_1(X0)
        & ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v2_funct_1(sK0)
      & ! [X2,X1] : k9_relat_1(sK0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(sK0,X1),k9_relat_1(sK0,X2))
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
         => v2_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_funct_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f94,plain,(
    ! [X0] :
      ( k9_relat_1(sK0,k1_tarski(X0)) = k9_relat_1(sK0,k6_subset_1(k1_tarski(X0),k1_tarski(sK1(sK0))))
      | sK2(sK0) = X0 ) ),
    inference(superposition,[],[f80,f52])).

fof(f52,plain,(
    ! [X2,X3] :
      ( k1_tarski(X2) = k6_subset_1(k1_tarski(X2),k1_tarski(X3))
      | X2 = X3 ) ),
    inference(superposition,[],[f37,f34])).

fof(f34,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f80,plain,(
    ! [X0] : k9_relat_1(sK0,k6_subset_1(X0,k1_tarski(sK2(sK0)))) = k9_relat_1(sK0,k6_subset_1(X0,k1_tarski(sK1(sK0)))) ),
    inference(forward_demodulation,[],[f79,f68])).

fof(f68,plain,(
    ! [X0,X1] : k9_relat_1(sK0,k6_subset_1(X1,k1_tarski(X0))) = k6_subset_1(k9_relat_1(sK0,X1),k11_relat_1(sK0,X0)) ),
    inference(superposition,[],[f25,f42])).

fof(f25,plain,(
    ! [X2,X1] : k9_relat_1(sK0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(sK0,X1),k9_relat_1(sK0,X2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f79,plain,(
    ! [X0] : k9_relat_1(sK0,k6_subset_1(X0,k1_tarski(sK2(sK0)))) = k6_subset_1(k9_relat_1(sK0,X0),k11_relat_1(sK0,sK1(sK0))) ),
    inference(superposition,[],[f68,f67])).

fof(f67,plain,(
    k11_relat_1(sK0,sK1(sK0)) = k11_relat_1(sK0,sK2(sK0)) ),
    inference(forward_demodulation,[],[f66,f60])).

fof(f60,plain,(
    k11_relat_1(sK0,sK1(sK0)) = k1_tarski(k1_funct_1(sK0,sK1(sK0))) ),
    inference(subsumption_resolution,[],[f59,f23])).

fof(f59,plain,
    ( k11_relat_1(sK0,sK1(sK0)) = k1_tarski(k1_funct_1(sK0,sK1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f58,f24])).

fof(f24,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,
    ( k11_relat_1(sK0,sK1(sK0)) = k1_tarski(k1_funct_1(sK0,sK1(sK0)))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f35,f45])).

fof(f45,plain,(
    r2_hidden(sK1(sK0),k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f44,f23])).

fof(f44,plain,
    ( r2_hidden(sK1(sK0),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f43,f26])).

fof(f26,plain,(
    ~ v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,
    ( r2_hidden(sK1(sK0),k1_relat_1(sK0))
    | v2_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f30,f24])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK1(X0) != sK2(X0)
            & k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
            & r2_hidden(sK2(X0),k1_relat_1(X0))
            & r2_hidden(sK1(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f19,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK1(X0) != sK2(X0)
        & k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
        & r2_hidden(sK2(X0),k1_relat_1(X0))
        & r2_hidden(sK1(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

fof(f66,plain,(
    k1_tarski(k1_funct_1(sK0,sK1(sK0))) = k11_relat_1(sK0,sK2(sK0)) ),
    inference(forward_demodulation,[],[f65,f57])).

fof(f57,plain,(
    k1_funct_1(sK0,sK1(sK0)) = k1_funct_1(sK0,sK2(sK0)) ),
    inference(subsumption_resolution,[],[f56,f23])).

fof(f56,plain,
    ( k1_funct_1(sK0,sK1(sK0)) = k1_funct_1(sK0,sK2(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f55,f26])).

fof(f55,plain,
    ( k1_funct_1(sK0,sK1(sK0)) = k1_funct_1(sK0,sK2(sK0))
    | v2_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f32,f24])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    k11_relat_1(sK0,sK2(sK0)) = k1_tarski(k1_funct_1(sK0,sK2(sK0))) ),
    inference(subsumption_resolution,[],[f64,f23])).

fof(f64,plain,
    ( k11_relat_1(sK0,sK2(sK0)) = k1_tarski(k1_funct_1(sK0,sK2(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f63,f24])).

fof(f63,plain,
    ( k11_relat_1(sK0,sK2(sK0)) = k1_tarski(k1_funct_1(sK0,sK2(sK0)))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f48,f35])).

fof(f48,plain,(
    r2_hidden(sK2(sK0),k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f47,f23])).

fof(f47,plain,
    ( r2_hidden(sK2(sK0),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f46,f26])).

fof(f46,plain,
    ( r2_hidden(sK2(sK0),k1_relat_1(sK0))
    | v2_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f31,f24])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK2(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f91,plain,(
    k11_relat_1(sK0,sK1(sK0)) != k9_relat_1(sK0,k6_subset_1(k1_tarski(sK1(sK0)),k1_tarski(sK1(sK0)))) ),
    inference(superposition,[],[f74,f78])).

fof(f78,plain,(
    ! [X0,X1] : k9_relat_1(sK0,k6_subset_1(k1_tarski(X0),k1_tarski(X1))) = k6_subset_1(k11_relat_1(sK0,X0),k11_relat_1(sK0,X1)) ),
    inference(superposition,[],[f68,f42])).

fof(f74,plain,(
    k11_relat_1(sK0,sK1(sK0)) != k6_subset_1(k11_relat_1(sK0,sK1(sK0)),k11_relat_1(sK0,sK1(sK0))) ),
    inference(superposition,[],[f41,f60])).

fof(f41,plain,(
    ! [X0] : k1_tarski(X0) != k6_subset_1(k1_tarski(X0),k1_tarski(X0)) ),
    inference(superposition,[],[f38,f34])).

fof(f38,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,(
    sK1(sK0) != sK2(sK0) ),
    inference(subsumption_resolution,[],[f50,f23])).

fof(f50,plain,
    ( sK1(sK0) != sK2(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f49,f26])).

fof(f49,plain,
    ( sK1(sK0) != sK2(sK0)
    | v2_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f33,f24])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | sK1(X0) != sK2(X0)
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

%------------------------------------------------------------------------------
