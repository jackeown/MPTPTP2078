%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:14 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   65 (  97 expanded)
%              Number of leaves         :   13 (  26 expanded)
%              Depth                    :   16
%              Number of atoms          :  273 ( 374 expanded)
%              Number of equality atoms :   86 ( 116 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f120,plain,(
    $false ),
    inference(resolution,[],[f118,f72])).

fof(f72,plain,(
    r2_hidden(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,k1_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f55,f56])).

fof(f56,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f39,f41,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f55,plain,(
    r2_hidden(sK0,k1_setfam_1(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),sK1))) ),
    inference(definition_unfolding,[],[f33,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f33,plain,(
    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0)
    & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
        & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0)
      & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
         => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_funct_1)).

fof(f118,plain,(
    ! [X0] : ~ r2_hidden(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,X0))) ),
    inference(resolution,[],[f117,f69])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k1_setfam_1(k1_enumset1(X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k1_enumset1(X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f48,f54])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f117,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f116])).

fof(f116,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(sK2,sK0)
    | ~ r2_hidden(sK0,sK1) ),
    inference(superposition,[],[f34,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k7_relat_1(sK2,X0),X1) = k1_funct_1(sK2,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k7_relat_1(sK2,X0),X1) = k1_funct_1(sK2,X1)
      | ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f99,f70])).

fof(f70,plain,(
    ! [X0,X3] :
      ( k1_funct_1(k6_relat_1(X0),X3) = X3
      | ~ r2_hidden(X3,X0) ) ),
    inference(global_subsumption,[],[f36,f35,f65])).

fof(f65,plain,(
    ! [X0,X3] :
      ( k1_funct_1(k6_relat_1(X0),X3) = X3
      | ~ r2_hidden(X3,X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X1,X3) = X3
      | ~ r2_hidden(X3,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1))
            & r2_hidden(sK3(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f35,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f36,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k1_funct_1(sK2,k1_funct_1(k6_relat_1(X0),X1)) = k1_funct_1(k7_relat_1(sK2,X0),X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f97,f31])).

fof(f31,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k1_funct_1(sK2,k1_funct_1(k6_relat_1(X0),X1)) = k1_funct_1(k7_relat_1(sK2,X0),X1)
      | ~ r2_hidden(X1,X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f96,f32])).

fof(f32,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2)) = k1_funct_1(k7_relat_1(X1,X0),X2)
      | ~ r2_hidden(X2,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f95,f37])).

fof(f37,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2)) = k1_funct_1(k7_relat_1(X1,X0),X2)
      | ~ r2_hidden(X2,k1_relat_1(k6_relat_1(X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f94,f35])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2)) = k1_funct_1(k7_relat_1(X1,X0),X2)
      | ~ r2_hidden(X2,k1_relat_1(k6_relat_1(X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f93,f36])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2)) = k1_funct_1(k7_relat_1(X1,X0),X2)
      | ~ r2_hidden(X2,k1_relat_1(k6_relat_1(X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2)) = k1_funct_1(k7_relat_1(X1,X0),X2)
      | ~ r2_hidden(X2,k1_relat_1(k6_relat_1(X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f47,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(f34,plain,(
    k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:51:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (28045)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.49  % (28045)Refutation not found, incomplete strategy% (28045)------------------------------
% 0.21/0.49  % (28045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (28060)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.50  % (28045)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (28045)Memory used [KB]: 10746
% 0.21/0.50  % (28045)Time elapsed: 0.086 s
% 0.21/0.50  % (28045)------------------------------
% 0.21/0.50  % (28045)------------------------------
% 0.21/0.50  % (28068)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.50  % (28060)Refutation not found, incomplete strategy% (28060)------------------------------
% 0.21/0.50  % (28060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (28060)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (28060)Memory used [KB]: 10618
% 0.21/0.50  % (28060)Time elapsed: 0.099 s
% 0.21/0.50  % (28060)------------------------------
% 0.21/0.50  % (28060)------------------------------
% 0.21/0.51  % (28044)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (28048)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (28052)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.27/0.52  % (28043)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.27/0.52  % (28056)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.27/0.52  % (28059)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.27/0.52  % (28047)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.27/0.52  % (28055)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.27/0.53  % (28049)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.27/0.53  % (28072)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.27/0.53  % (28070)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.27/0.53  % (28065)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.27/0.53  % (28050)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.27/0.53  % (28063)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.27/0.53  % (28071)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.27/0.53  % (28057)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.27/0.53  % (28069)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.27/0.54  % (28046)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.27/0.54  % (28065)Refutation not found, incomplete strategy% (28065)------------------------------
% 1.27/0.54  % (28065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (28046)Refutation found. Thanks to Tanya!
% 1.27/0.54  % SZS status Theorem for theBenchmark
% 1.43/0.54  % (28062)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.43/0.54  % (28053)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.43/0.54  % (28066)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.43/0.54  % (28054)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.43/0.55  % (28067)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.43/0.55  % (28058)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.43/0.55  % (28058)Refutation not found, incomplete strategy% (28058)------------------------------
% 1.43/0.55  % (28058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (28058)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (28058)Memory used [KB]: 6140
% 1.43/0.55  % (28058)Time elapsed: 0.146 s
% 1.43/0.55  % (28058)------------------------------
% 1.43/0.55  % (28058)------------------------------
% 1.43/0.55  % (28065)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (28065)Memory used [KB]: 10746
% 1.43/0.55  % (28065)Time elapsed: 0.106 s
% 1.43/0.55  % (28065)------------------------------
% 1.43/0.55  % (28065)------------------------------
% 1.43/0.55  % SZS output start Proof for theBenchmark
% 1.43/0.55  fof(f120,plain,(
% 1.43/0.55    $false),
% 1.43/0.55    inference(resolution,[],[f118,f72])).
% 1.43/0.55  fof(f72,plain,(
% 1.43/0.55    r2_hidden(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,k1_relat_1(sK2))))),
% 1.43/0.55    inference(backward_demodulation,[],[f55,f56])).
% 1.43/0.55  fof(f56,plain,(
% 1.43/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 1.43/0.55    inference(definition_unfolding,[],[f39,f41,f41])).
% 1.43/0.55  fof(f41,plain,(
% 1.43/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.43/0.55    inference(cnf_transformation,[],[f3])).
% 1.43/0.55  fof(f3,axiom,(
% 1.43/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.43/0.55  fof(f39,plain,(
% 1.43/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.43/0.55    inference(cnf_transformation,[],[f2])).
% 1.43/0.55  fof(f2,axiom,(
% 1.43/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.43/0.55  fof(f55,plain,(
% 1.43/0.55    r2_hidden(sK0,k1_setfam_1(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),sK1)))),
% 1.43/0.55    inference(definition_unfolding,[],[f33,f54])).
% 1.43/0.55  fof(f54,plain,(
% 1.43/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.43/0.55    inference(definition_unfolding,[],[f40,f41])).
% 1.43/0.55  fof(f40,plain,(
% 1.43/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.43/0.55    inference(cnf_transformation,[],[f4])).
% 1.43/0.55  fof(f4,axiom,(
% 1.43/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.43/0.55  fof(f33,plain,(
% 1.43/0.55    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))),
% 1.43/0.55    inference(cnf_transformation,[],[f20])).
% 1.43/0.55  fof(f20,plain,(
% 1.43/0.55    k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0) & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.43/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f19])).
% 1.43/0.55  fof(f19,plain,(
% 1.43/0.55    ? [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0) & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.43/0.55    introduced(choice_axiom,[])).
% 1.43/0.55  fof(f13,plain,(
% 1.43/0.55    ? [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.43/0.55    inference(flattening,[],[f12])).
% 1.43/0.55  fof(f12,plain,(
% 1.43/0.55    ? [X0,X1,X2] : ((k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.43/0.55    inference(ennf_transformation,[],[f11])).
% 1.43/0.55  fof(f11,negated_conjecture,(
% 1.43/0.55    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 1.43/0.55    inference(negated_conjecture,[],[f10])).
% 1.43/0.55  fof(f10,conjecture,(
% 1.43/0.55    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_funct_1)).
% 1.43/0.55  fof(f118,plain,(
% 1.43/0.55    ( ! [X0] : (~r2_hidden(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,X0)))) )),
% 1.43/0.55    inference(resolution,[],[f117,f69])).
% 1.43/0.55  fof(f69,plain,(
% 1.43/0.55    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 1.43/0.55    inference(equality_resolution,[],[f62])).
% 1.43/0.55  fof(f62,plain,(
% 1.43/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k1_setfam_1(k1_enumset1(X0,X0,X1)) != X2) )),
% 1.43/0.55    inference(definition_unfolding,[],[f48,f54])).
% 1.43/0.55  fof(f48,plain,(
% 1.43/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.43/0.55    inference(cnf_transformation,[],[f30])).
% 1.43/0.55  fof(f30,plain,(
% 1.43/0.55    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.43/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).
% 1.43/0.55  fof(f29,plain,(
% 1.43/0.55    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.43/0.55    introduced(choice_axiom,[])).
% 1.43/0.55  fof(f28,plain,(
% 1.43/0.55    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.43/0.55    inference(rectify,[],[f27])).
% 1.43/0.55  fof(f27,plain,(
% 1.43/0.55    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.43/0.55    inference(flattening,[],[f26])).
% 1.43/0.55  fof(f26,plain,(
% 1.43/0.55    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.43/0.55    inference(nnf_transformation,[],[f1])).
% 1.43/0.55  fof(f1,axiom,(
% 1.43/0.55    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.43/0.55  fof(f117,plain,(
% 1.43/0.55    ~r2_hidden(sK0,sK1)),
% 1.43/0.55    inference(trivial_inequality_removal,[],[f116])).
% 1.43/0.55  fof(f116,plain,(
% 1.43/0.55    k1_funct_1(sK2,sK0) != k1_funct_1(sK2,sK0) | ~r2_hidden(sK0,sK1)),
% 1.43/0.55    inference(superposition,[],[f34,f102])).
% 1.43/0.55  fof(f102,plain,(
% 1.43/0.55    ( ! [X0,X1] : (k1_funct_1(k7_relat_1(sK2,X0),X1) = k1_funct_1(sK2,X1) | ~r2_hidden(X1,X0)) )),
% 1.43/0.55    inference(duplicate_literal_removal,[],[f101])).
% 1.43/0.55  fof(f101,plain,(
% 1.43/0.55    ( ! [X0,X1] : (k1_funct_1(k7_relat_1(sK2,X0),X1) = k1_funct_1(sK2,X1) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X0)) )),
% 1.43/0.55    inference(superposition,[],[f99,f70])).
% 1.43/0.55  fof(f70,plain,(
% 1.43/0.55    ( ! [X0,X3] : (k1_funct_1(k6_relat_1(X0),X3) = X3 | ~r2_hidden(X3,X0)) )),
% 1.43/0.55    inference(global_subsumption,[],[f36,f35,f65])).
% 1.43/0.55  fof(f65,plain,(
% 1.43/0.55    ( ! [X0,X3] : (k1_funct_1(k6_relat_1(X0),X3) = X3 | ~r2_hidden(X3,X0) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.43/0.55    inference(equality_resolution,[],[f44])).
% 1.43/0.55  fof(f44,plain,(
% 1.43/0.55    ( ! [X0,X3,X1] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0) | k6_relat_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.43/0.55    inference(cnf_transformation,[],[f25])).
% 1.43/0.55  fof(f25,plain,(
% 1.43/0.55    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.43/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).
% 1.43/0.55  fof(f24,plain,(
% 1.43/0.55    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 1.43/0.55    introduced(choice_axiom,[])).
% 1.43/0.55  fof(f23,plain,(
% 1.43/0.55    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.43/0.55    inference(rectify,[],[f22])).
% 1.43/0.55  fof(f22,plain,(
% 1.43/0.55    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.43/0.55    inference(flattening,[],[f21])).
% 1.43/0.55  fof(f21,plain,(
% 1.43/0.55    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.43/0.55    inference(nnf_transformation,[],[f16])).
% 1.43/0.55  fof(f16,plain,(
% 1.43/0.55    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.43/0.55    inference(flattening,[],[f15])).
% 1.43/0.56  fof(f15,plain,(
% 1.43/0.56    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.43/0.56    inference(ennf_transformation,[],[f9])).
% 1.43/0.56  fof(f9,axiom,(
% 1.43/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).
% 1.43/0.56  fof(f35,plain,(
% 1.43/0.56    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f7])).
% 1.43/0.56  fof(f7,axiom,(
% 1.43/0.56    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.43/0.56  fof(f36,plain,(
% 1.43/0.56    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f7])).
% 1.43/0.56  fof(f99,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k1_funct_1(sK2,k1_funct_1(k6_relat_1(X0),X1)) = k1_funct_1(k7_relat_1(sK2,X0),X1) | ~r2_hidden(X1,X0)) )),
% 1.43/0.56    inference(subsumption_resolution,[],[f97,f31])).
% 1.43/0.56  fof(f31,plain,(
% 1.43/0.56    v1_relat_1(sK2)),
% 1.43/0.56    inference(cnf_transformation,[],[f20])).
% 1.43/0.56  fof(f97,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k1_funct_1(sK2,k1_funct_1(k6_relat_1(X0),X1)) = k1_funct_1(k7_relat_1(sK2,X0),X1) | ~r2_hidden(X1,X0) | ~v1_relat_1(sK2)) )),
% 1.43/0.56    inference(resolution,[],[f96,f32])).
% 1.43/0.56  fof(f32,plain,(
% 1.43/0.56    v1_funct_1(sK2)),
% 1.43/0.56    inference(cnf_transformation,[],[f20])).
% 1.43/0.56  fof(f96,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2)) = k1_funct_1(k7_relat_1(X1,X0),X2) | ~r2_hidden(X2,X0) | ~v1_relat_1(X1)) )),
% 1.43/0.56    inference(forward_demodulation,[],[f95,f37])).
% 1.43/0.56  fof(f37,plain,(
% 1.43/0.56    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.43/0.56    inference(cnf_transformation,[],[f5])).
% 1.43/0.56  fof(f5,axiom,(
% 1.43/0.56    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.43/0.56  fof(f95,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2)) = k1_funct_1(k7_relat_1(X1,X0),X2) | ~r2_hidden(X2,k1_relat_1(k6_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.43/0.56    inference(subsumption_resolution,[],[f94,f35])).
% 1.43/0.56  fof(f94,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2)) = k1_funct_1(k7_relat_1(X1,X0),X2) | ~r2_hidden(X2,k1_relat_1(k6_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.43/0.56    inference(subsumption_resolution,[],[f93,f36])).
% 1.43/0.56  fof(f93,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2)) = k1_funct_1(k7_relat_1(X1,X0),X2) | ~r2_hidden(X2,k1_relat_1(k6_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.43/0.56    inference(duplicate_literal_removal,[],[f92])).
% 1.43/0.56  fof(f92,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2)) = k1_funct_1(k7_relat_1(X1,X0),X2) | ~r2_hidden(X2,k1_relat_1(k6_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 1.43/0.56    inference(superposition,[],[f47,f42])).
% 1.43/0.56  fof(f42,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f14])).
% 1.43/0.56  fof(f14,plain,(
% 1.43/0.56    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.43/0.56    inference(ennf_transformation,[],[f6])).
% 1.43/0.56  fof(f6,axiom,(
% 1.43/0.56    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 1.43/0.56  fof(f47,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f18])).
% 1.43/0.56  fof(f18,plain,(
% 1.43/0.56    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.43/0.56    inference(flattening,[],[f17])).
% 1.43/0.56  fof(f17,plain,(
% 1.43/0.56    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.43/0.56    inference(ennf_transformation,[],[f8])).
% 1.43/0.56  fof(f8,axiom,(
% 1.43/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
% 1.43/0.56  fof(f34,plain,(
% 1.43/0.56    k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0)),
% 1.43/0.56    inference(cnf_transformation,[],[f20])).
% 1.43/0.56  % SZS output end Proof for theBenchmark
% 1.43/0.56  % (28046)------------------------------
% 1.43/0.56  % (28046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (28046)Termination reason: Refutation
% 1.43/0.56  
% 1.43/0.56  % (28046)Memory used [KB]: 10746
% 1.43/0.56  % (28046)Time elapsed: 0.139 s
% 1.43/0.56  % (28046)------------------------------
% 1.43/0.56  % (28046)------------------------------
% 1.43/0.56  % (28064)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.43/0.56  % (28041)Success in time 0.201 s
%------------------------------------------------------------------------------
