%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 433 expanded)
%              Number of leaves         :   14 ( 129 expanded)
%              Depth                    :   19
%              Number of atoms          :  205 ( 970 expanded)
%              Number of equality atoms :   55 ( 386 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f163,plain,(
    $false ),
    inference(subsumption_resolution,[],[f162,f58])).

fof(f58,plain,(
    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) ),
    inference(backward_demodulation,[],[f31,f56])).

fof(f56,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2) ),
    inference(resolution,[],[f39,f28])).

fof(f28,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0)
    & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
        & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0)
      & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
         => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f31,plain,(
    k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f162,plain,(
    k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0) ),
    inference(forward_demodulation,[],[f161,f56])).

fof(f161,plain,(
    k1_funct_1(sK2,sK0) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0) ),
    inference(subsumption_resolution,[],[f159,f28])).

fof(f159,plain,
    ( k1_funct_1(sK2,sK0) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f158,f29])).

fof(f29,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f158,plain,(
    ! [X2] :
      ( ~ v1_funct_1(X2)
      | k1_funct_1(k5_relat_1(k6_relat_1(sK1),X2),sK0) = k1_funct_1(X2,sK0)
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f155,f87])).

fof(f87,plain,(
    sK0 = k1_funct_1(k6_relat_1(sK1),sK0) ),
    inference(resolution,[],[f85,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_1)).

fof(f85,plain,(
    r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f83,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k7_relat_1(sK2,X0)))
      | r2_hidden(X1,X0) ) ),
    inference(forward_demodulation,[],[f64,f34])).

fof(f34,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k7_relat_1(sK2,X0)))
      | r2_hidden(X1,k1_relat_1(k6_relat_1(X0))) ) ),
    inference(subsumption_resolution,[],[f63,f28])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k7_relat_1(sK2,X0)))
      | r2_hidden(X1,k1_relat_1(k6_relat_1(X0)))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f62,f29])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k7_relat_1(sK2,X0)))
      | r2_hidden(X1,k1_relat_1(k6_relat_1(X0)))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f61,f32])).

fof(f32,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k7_relat_1(sK2,X0)))
      | r2_hidden(X1,k1_relat_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f59,f33])).

fof(f33,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k7_relat_1(sK2,X0)))
      | r2_hidden(X1,k1_relat_1(k6_relat_1(X0)))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f43,f56])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

fof(f83,plain,(
    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(backward_demodulation,[],[f76,f81])).

fof(f81,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK2,X0)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK2))) ),
    inference(superposition,[],[f74,f71])).

fof(f71,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK2,X0)) = k1_setfam_1(k3_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),X0)) ),
    inference(resolution,[],[f53,f28])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k3_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f40,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f74,plain,(
    ! [X0,X1] : k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X0)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(backward_demodulation,[],[f52,f73])).

fof(f73,plain,(
    ! [X2,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(forward_demodulation,[],[f72,f34])).

fof(f72,plain,(
    ! [X2,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k3_enumset1(k1_relat_1(k6_relat_1(X1)),k1_relat_1(k6_relat_1(X1)),k1_relat_1(k6_relat_1(X1)),k1_relat_1(k6_relat_1(X1)),X2)) ),
    inference(resolution,[],[f53,f32])).

fof(f52,plain,(
    ! [X0,X1] : k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f36,f50,f50])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

% (15146)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
fof(f76,plain,(
    r2_hidden(sK0,k1_relat_1(k7_relat_1(k6_relat_1(sK1),k1_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f54,f73])).

fof(f54,plain,(
    r2_hidden(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,k1_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f51,f52])).

fof(f51,plain,(
    r2_hidden(sK0,k1_setfam_1(k3_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),sK1))) ),
    inference(definition_unfolding,[],[f30,f50])).

fof(f30,plain,(
    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f155,plain,(
    ! [X2] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(sK1),X2),sK0) = k1_funct_1(X2,k1_funct_1(k6_relat_1(sK1),sK0))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f144,f85])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k1_funct_1(k5_relat_1(k6_relat_1(X0),X2),X1) = k1_funct_1(X2,k1_funct_1(k6_relat_1(X0),X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f143,f32])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k1_funct_1(k5_relat_1(k6_relat_1(X0),X2),X1) = k1_funct_1(X2,k1_funct_1(k6_relat_1(X0),X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f136,f33])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k1_funct_1(k5_relat_1(k6_relat_1(X0),X2),X1) = k1_funct_1(X2,k1_funct_1(k6_relat_1(X0),X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f42,f34])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:06:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.45  % (15141)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (15149)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.47  % (15149)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f163,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(subsumption_resolution,[],[f162,f58])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)),
% 0.20/0.47    inference(backward_demodulation,[],[f31,f56])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X0] : (k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)) )),
% 0.20/0.47    inference(resolution,[],[f39,f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    v1_relat_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0) & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0) & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.47    inference(flattening,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ? [X0,X1,X2] : ((k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)))),
% 0.20/0.47    inference(negated_conjecture,[],[f13])).
% 0.20/0.47  fof(f13,conjecture,(
% 0.20/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_1)).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f162,plain,(
% 0.20/0.47    k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0)),
% 0.20/0.47    inference(forward_demodulation,[],[f161,f56])).
% 0.20/0.47  fof(f161,plain,(
% 0.20/0.47    k1_funct_1(sK2,sK0) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f159,f28])).
% 0.20/0.47  fof(f159,plain,(
% 0.20/0.47    k1_funct_1(sK2,sK0) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0) | ~v1_relat_1(sK2)),
% 0.20/0.47    inference(resolution,[],[f158,f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    v1_funct_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f158,plain,(
% 0.20/0.47    ( ! [X2] : (~v1_funct_1(X2) | k1_funct_1(k5_relat_1(k6_relat_1(sK1),X2),sK0) = k1_funct_1(X2,sK0) | ~v1_relat_1(X2)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f155,f87])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    sK0 = k1_funct_1(k6_relat_1(sK1),sK0)),
% 0.20/0.47    inference(resolution,[],[f85,f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_funct_1(k6_relat_1(X1),X0) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1] : (k1_funct_1(k6_relat_1(X1),X0) = X0 | ~r2_hidden(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,axiom,(
% 0.20/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => k1_funct_1(k6_relat_1(X1),X0) = X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_1)).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    r2_hidden(sK0,sK1)),
% 0.20/0.47    inference(resolution,[],[f83,f65])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(k7_relat_1(sK2,X0))) | r2_hidden(X1,X0)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f64,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(k7_relat_1(sK2,X0))) | r2_hidden(X1,k1_relat_1(k6_relat_1(X0)))) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f63,f28])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(k7_relat_1(sK2,X0))) | r2_hidden(X1,k1_relat_1(k6_relat_1(X0))) | ~v1_relat_1(sK2)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f62,f29])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(k7_relat_1(sK2,X0))) | r2_hidden(X1,k1_relat_1(k6_relat_1(X0))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f61,f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(k7_relat_1(sK2,X0))) | r2_hidden(X1,k1_relat_1(k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f59,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(k7_relat_1(sK2,X0))) | r2_hidden(X1,k1_relat_1(k6_relat_1(X0))) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.20/0.47    inference(superposition,[],[f43,f56])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | (~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(nnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))),
% 0.20/0.47    inference(backward_demodulation,[],[f76,f81])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    ( ! [X0] : (k1_relat_1(k7_relat_1(sK2,X0)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK2)))) )),
% 0.20/0.47    inference(superposition,[],[f74,f71])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    ( ! [X0] : (k1_relat_1(k7_relat_1(sK2,X0)) = k1_setfam_1(k3_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),X0))) )),
% 0.20/0.47    inference(resolution,[],[f53,f28])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k3_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f40,f50])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f37,f49])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f38,f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f46,f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X0)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 0.20/0.47    inference(backward_demodulation,[],[f52,f73])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    ( ! [X2,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))) )),
% 0.20/0.47    inference(forward_demodulation,[],[f72,f34])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    ( ! [X2,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k3_enumset1(k1_relat_1(k6_relat_1(X1)),k1_relat_1(k6_relat_1(X1)),k1_relat_1(k6_relat_1(X1)),k1_relat_1(k6_relat_1(X1)),X2))) )),
% 0.20/0.47    inference(resolution,[],[f53,f32])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f36,f50,f50])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.47  % (15146)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    r2_hidden(sK0,k1_relat_1(k7_relat_1(k6_relat_1(sK1),k1_relat_1(sK2))))),
% 0.20/0.47    inference(backward_demodulation,[],[f54,f73])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    r2_hidden(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,k1_relat_1(sK2))))),
% 0.20/0.47    inference(backward_demodulation,[],[f51,f52])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    r2_hidden(sK0,k1_setfam_1(k3_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),sK1)))),
% 0.20/0.47    inference(definition_unfolding,[],[f30,f50])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f155,plain,(
% 0.20/0.47    ( ! [X2] : (k1_funct_1(k5_relat_1(k6_relat_1(sK1),X2),sK0) = k1_funct_1(X2,k1_funct_1(k6_relat_1(sK1),sK0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.47    inference(resolution,[],[f144,f85])).
% 0.20/0.47  fof(f144,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X1,X0) | k1_funct_1(k5_relat_1(k6_relat_1(X0),X2),X1) = k1_funct_1(X2,k1_funct_1(k6_relat_1(X0),X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f143,f32])).
% 0.20/0.47  fof(f143,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X1,X0) | k1_funct_1(k5_relat_1(k6_relat_1(X0),X2),X1) = k1_funct_1(X2,k1_funct_1(k6_relat_1(X0),X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f136,f33])).
% 0.20/0.47  fof(f136,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X1,X0) | k1_funct_1(k5_relat_1(k6_relat_1(X0),X2),X1) = k1_funct_1(X2,k1_funct_1(k6_relat_1(X0),X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.47    inference(superposition,[],[f42,f34])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (15149)------------------------------
% 0.20/0.47  % (15149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (15149)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (15149)Memory used [KB]: 1791
% 0.20/0.47  % (15149)Time elapsed: 0.018 s
% 0.20/0.47  % (15149)------------------------------
% 0.20/0.47  % (15149)------------------------------
% 0.20/0.48  % (15133)Success in time 0.117 s
%------------------------------------------------------------------------------
