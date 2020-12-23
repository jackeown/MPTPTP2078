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
% DateTime   : Thu Dec  3 12:54:41 EST 2020

% Result     : Theorem 2.72s
% Output     : Refutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 758 expanded)
%              Number of leaves         :   13 ( 267 expanded)
%              Depth                    :   35
%              Number of atoms          :  351 (4449 expanded)
%              Number of equality atoms :  104 (1829 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1484,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1483,f186])).

fof(f186,plain,(
    ! [X3] : r1_tarski(k1_relat_1(k7_relat_1(sK0,X3)),k1_relat_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,(
    ! [X3] :
      ( r1_tarski(k1_relat_1(k7_relat_1(sK0,X3)),k1_relat_1(sK0))
      | r1_tarski(k1_relat_1(k7_relat_1(sK0,X3)),k1_relat_1(sK0)) ) ),
    inference(resolution,[],[f117,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f117,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(k1_relat_1(k7_relat_1(sK0,X0)),X1),k1_relat_1(sK0))
      | r1_tarski(k1_relat_1(k7_relat_1(sK0,X0)),X1) ) ),
    inference(resolution,[],[f92,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f92,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(k7_relat_1(sK0,X2)))
      | r2_hidden(X3,k1_relat_1(sK0)) ) ),
    inference(forward_demodulation,[],[f91,f42])).

fof(f42,plain,(
    k1_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
    & ! [X3] :
        ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
        | ~ r2_hidden(X3,sK2) )
    & k1_relat_1(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
                & ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) )
                & k1_relat_1(X1) = k1_relat_1(X0) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X1,X2) != k7_relat_1(sK0,X2)
              & ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(sK0,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X1) = k1_relat_1(sK0) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k7_relat_1(X1,X2) != k7_relat_1(sK0,X2)
            & ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(sK0,X3)
                | ~ r2_hidden(X3,X2) )
            & k1_relat_1(X1) = k1_relat_1(sK0) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2)
          & ! [X3] :
              ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
              | ~ r2_hidden(X3,X2) )
          & k1_relat_1(sK0) = k1_relat_1(sK1) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2)
        & ! [X3] :
            ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
            | ~ r2_hidden(X3,X2) )
        & k1_relat_1(sK0) = k1_relat_1(sK1) )
   => ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
      & ! [X3] :
          ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
          | ~ r2_hidden(X3,sK2) )
      & k1_relat_1(sK0) = k1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( ! [X3] :
                      ( r2_hidden(X3,X2)
                     => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) )
                  & k1_relat_1(X1) = k1_relat_1(X0) )
               => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( ! [X3] :
                    ( r2_hidden(X3,X2)
                   => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) )
                & k1_relat_1(X1) = k1_relat_1(X0) )
             => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_funct_1)).

fof(f91,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(k7_relat_1(sK0,X2)))
      | r2_hidden(X3,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f87,f40])).

fof(f40,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f87,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(k7_relat_1(sK0,X2)))
      | r2_hidden(X3,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f61,f77])).

fof(f77,plain,(
    ! [X1] : k1_relat_1(k7_relat_1(sK0,X1)) = k1_relat_1(k7_relat_1(sK1,X1)) ),
    inference(forward_demodulation,[],[f76,f68])).

fof(f68,plain,(
    ! [X1] : k1_relat_1(k7_relat_1(sK0,X1)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),X1)) ),
    inference(resolution,[],[f38,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f56,f63])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f38,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    ! [X1] : k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),X1)) = k1_relat_1(k7_relat_1(sK1,X1)) ),
    inference(forward_demodulation,[],[f72,f42])).

fof(f72,plain,(
    ! [X1] : k1_relat_1(k7_relat_1(sK1,X1)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X1)) ),
    inference(resolution,[],[f40,f65])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(f1483,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f1482,f42])).

fof(f1482,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f1481,f44])).

fof(f44,plain,(
    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f1481,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f1480,f75])).

fof(f75,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0))) ),
    inference(forward_demodulation,[],[f74,f68])).

fof(f74,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),X0))) ),
    inference(forward_demodulation,[],[f71,f42])).

fof(f71,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X0))) ),
    inference(resolution,[],[f40,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f57,f63])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

fof(f1480,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f1479,f70])).

fof(f70,plain,(
    ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0))) ),
    inference(backward_demodulation,[],[f67,f68])).

fof(f67,plain,(
    ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(sK0,k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),X0))) ),
    inference(resolution,[],[f38,f66])).

fof(f1479,plain,
    ( k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f1478,f38])).

fof(f1478,plain,
    ( k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f1477,f39])).

fof(f39,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f1477,plain,
    ( k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f1476,f40])).

fof(f1476,plain,
    ( k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f1475,f41])).

fof(f41,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f1475,plain,
    ( k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f1474,f186])).

fof(f1474,plain,
    ( k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(trivial_inequality_removal,[],[f1473])).

fof(f1473,plain,
    ( k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) != k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2))))
    | k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f48,f1220])).

fof(f1220,plain,(
    k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) ),
    inference(subsumption_resolution,[],[f1203,f44])).

fof(f1203,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) ),
    inference(resolution,[],[f1186,f43])).

fof(f43,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1186,plain,(
    ! [X3] :
      ( r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X3))),X3)
      | k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3) ) ),
    inference(resolution,[],[f1180,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k7_relat_1(sK0,X0)))
      | r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f86,f40])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k7_relat_1(sK0,X0)))
      | r2_hidden(X1,X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f60,f77])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1180,plain,(
    ! [X12] :
      ( r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X12))),k1_relat_1(k7_relat_1(sK0,X12)))
      | k7_relat_1(sK0,X12) = k7_relat_1(sK1,X12) ) ),
    inference(forward_demodulation,[],[f1179,f70])).

fof(f1179,plain,(
    ! [X12] :
      ( r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X12))),k1_relat_1(k7_relat_1(sK0,X12)))
      | k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X12))) = k7_relat_1(sK1,X12) ) ),
    inference(subsumption_resolution,[],[f1178,f38])).

fof(f1178,plain,(
    ! [X12] :
      ( r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X12))),k1_relat_1(k7_relat_1(sK0,X12)))
      | k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X12))) = k7_relat_1(sK1,X12)
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f1151,f39])).

fof(f1151,plain,(
    ! [X12] :
      ( r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X12))),k1_relat_1(k7_relat_1(sK0,X12)))
      | k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X12))) = k7_relat_1(sK1,X12)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f194,f186])).

fof(f194,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,X1)),k1_relat_1(X0))
      | r2_hidden(sK3(X0,sK1,k1_relat_1(k7_relat_1(sK0,X1))),k1_relat_1(k7_relat_1(sK0,X1)))
      | k7_relat_1(sK1,X1) = k7_relat_1(X0,k1_relat_1(k7_relat_1(sK0,X1)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f191,f75])).

fof(f191,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,sK1,k1_relat_1(k7_relat_1(sK0,X1))),k1_relat_1(k7_relat_1(sK0,X1)))
      | k7_relat_1(X0,k1_relat_1(k7_relat_1(sK0,X1))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X1)))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,X1)),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f186,f85])).

fof(f85,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k1_relat_1(sK0))
      | r2_hidden(sK3(X3,sK1,X2),X2)
      | k7_relat_1(sK1,X2) = k7_relat_1(X3,X2)
      | ~ r1_tarski(X2,k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f84,f40])).

fof(f84,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k1_relat_1(sK0))
      | r2_hidden(sK3(X3,sK1,X2),X2)
      | k7_relat_1(sK1,X2) = k7_relat_1(X3,X2)
      | ~ r1_tarski(X2,k1_relat_1(X3))
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f81,f41])).

fof(f81,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k1_relat_1(sK0))
      | r2_hidden(sK3(X3,sK1,X2),X2)
      | k7_relat_1(sK1,X2) = k7_relat_1(X3,X2)
      | ~ r1_tarski(X2,k1_relat_1(X3))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f47,f42])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k1_relat_1(X1))
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
      | ~ r1_tarski(X2,k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
                  | ( k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2))
                    & r2_hidden(sK3(X0,X1,X2),X2) ) )
                & ( ! [X4] :
                      ( k1_funct_1(X0,X4) = k1_funct_1(X1,X4)
                      | ~ r2_hidden(X4,X2) )
                  | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
          & r2_hidden(X3,X2) )
     => ( k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2))
        & r2_hidden(sK3(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
                  | ? [X3] :
                      ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                      & r2_hidden(X3,X2) ) )
                & ( ! [X4] :
                      ( k1_funct_1(X0,X4) = k1_funct_1(X1,X4)
                      | ~ r2_hidden(X4,X2) )
                  | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
                  | ? [X3] :
                      ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                      & r2_hidden(X3,X2) ) )
                & ( ! [X3] :
                      ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                      | ~ r2_hidden(X3,X2) )
                  | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <=> ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <=> ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( r1_tarski(X2,k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) )
             => ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <=> ! [X3] :
                    ( r2_hidden(X3,X2)
                   => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t165_funct_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2))
      | k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
      | ~ r1_tarski(X2,k1_relat_1(X1))
      | ~ r1_tarski(X2,k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:50:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (8557)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (8574)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.46  % (8565)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.50  % (8547)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (8550)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (8558)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (8566)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (8548)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (8568)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (8549)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (8546)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (8569)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (8573)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (8571)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (8561)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (8560)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (8564)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (8554)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (8563)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (8553)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (8555)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.45/0.55  % (8555)Refutation not found, incomplete strategy% (8555)------------------------------
% 1.45/0.55  % (8555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (8555)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (8555)Memory used [KB]: 10746
% 1.45/0.55  % (8555)Time elapsed: 0.152 s
% 1.45/0.55  % (8555)------------------------------
% 1.45/0.55  % (8555)------------------------------
% 1.45/0.55  % (8556)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.45/0.56  % (8562)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.45/0.57  % (8545)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.66/0.58  % (8567)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.66/0.58  % (8559)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.66/0.58  % (8570)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.66/0.58  % (8572)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.66/0.59  % (8551)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.66/0.59  % (8562)Refutation not found, incomplete strategy% (8562)------------------------------
% 1.66/0.59  % (8562)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.59  % (8562)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.59  
% 1.66/0.59  % (8562)Memory used [KB]: 10618
% 1.66/0.59  % (8562)Time elapsed: 0.191 s
% 1.66/0.59  % (8562)------------------------------
% 1.66/0.59  % (8562)------------------------------
% 1.66/0.59  % (8552)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 2.33/0.71  % (8594)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.72/0.73  % (8595)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.72/0.75  % (8553)Refutation found. Thanks to Tanya!
% 2.72/0.75  % SZS status Theorem for theBenchmark
% 2.72/0.75  % SZS output start Proof for theBenchmark
% 2.72/0.75  fof(f1484,plain,(
% 2.72/0.75    $false),
% 2.72/0.75    inference(subsumption_resolution,[],[f1483,f186])).
% 2.72/0.75  fof(f186,plain,(
% 2.72/0.75    ( ! [X3] : (r1_tarski(k1_relat_1(k7_relat_1(sK0,X3)),k1_relat_1(sK0))) )),
% 2.72/0.75    inference(duplicate_literal_removal,[],[f183])).
% 2.72/0.75  fof(f183,plain,(
% 2.72/0.75    ( ! [X3] : (r1_tarski(k1_relat_1(k7_relat_1(sK0,X3)),k1_relat_1(sK0)) | r1_tarski(k1_relat_1(k7_relat_1(sK0,X3)),k1_relat_1(sK0))) )),
% 2.72/0.75    inference(resolution,[],[f117,f59])).
% 2.72/0.75  fof(f59,plain,(
% 2.72/0.75    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.72/0.75    inference(cnf_transformation,[],[f35])).
% 2.72/0.75  fof(f35,plain,(
% 2.72/0.75    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 2.72/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f34])).
% 2.72/0.75  fof(f34,plain,(
% 2.72/0.75    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 2.72/0.75    introduced(choice_axiom,[])).
% 2.72/0.75  fof(f22,plain,(
% 2.72/0.75    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 2.72/0.75    inference(ennf_transformation,[],[f13])).
% 2.72/0.75  fof(f13,plain,(
% 2.72/0.75    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 2.72/0.75    inference(unused_predicate_definition_removal,[],[f2])).
% 2.72/0.75  fof(f2,axiom,(
% 2.72/0.75    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.72/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.72/0.75  fof(f117,plain,(
% 2.72/0.75    ( ! [X0,X1] : (r2_hidden(sK5(k1_relat_1(k7_relat_1(sK0,X0)),X1),k1_relat_1(sK0)) | r1_tarski(k1_relat_1(k7_relat_1(sK0,X0)),X1)) )),
% 2.72/0.75    inference(resolution,[],[f92,f58])).
% 2.72/0.75  fof(f58,plain,(
% 2.72/0.75    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.72/0.75    inference(cnf_transformation,[],[f35])).
% 2.72/0.75  fof(f92,plain,(
% 2.72/0.75    ( ! [X2,X3] : (~r2_hidden(X3,k1_relat_1(k7_relat_1(sK0,X2))) | r2_hidden(X3,k1_relat_1(sK0))) )),
% 2.72/0.75    inference(forward_demodulation,[],[f91,f42])).
% 2.72/0.75  fof(f42,plain,(
% 2.72/0.75    k1_relat_1(sK0) = k1_relat_1(sK1)),
% 2.72/0.75    inference(cnf_transformation,[],[f27])).
% 2.72/0.75  fof(f27,plain,(
% 2.72/0.75    ((k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,sK2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 2.72/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f26,f25,f24])).
% 2.72/0.75  fof(f24,plain,(
% 2.72/0.75    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (k7_relat_1(X1,X2) != k7_relat_1(sK0,X2) & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(sK0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 2.72/0.75    introduced(choice_axiom,[])).
% 2.72/0.75  fof(f25,plain,(
% 2.72/0.75    ? [X1] : (? [X2] : (k7_relat_1(X1,X2) != k7_relat_1(sK0,X2) & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(sK0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 2.72/0.75    introduced(choice_axiom,[])).
% 2.72/0.75  fof(f26,plain,(
% 2.72/0.75    ? [X2] : (k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) => (k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,sK2)) & k1_relat_1(sK0) = k1_relat_1(sK1))),
% 2.72/0.75    introduced(choice_axiom,[])).
% 2.72/0.75  fof(f15,plain,(
% 2.72/0.75    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.72/0.75    inference(flattening,[],[f14])).
% 2.72/0.75  fof(f14,plain,(
% 2.72/0.75    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.72/0.75    inference(ennf_transformation,[],[f12])).
% 2.72/0.75  fof(f12,negated_conjecture,(
% 2.72/0.75    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X1) = k1_relat_1(X0)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 2.72/0.75    inference(negated_conjecture,[],[f11])).
% 2.72/0.75  fof(f11,conjecture,(
% 2.72/0.75    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X1) = k1_relat_1(X0)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 2.72/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_funct_1)).
% 2.72/0.75  fof(f91,plain,(
% 2.72/0.75    ( ! [X2,X3] : (~r2_hidden(X3,k1_relat_1(k7_relat_1(sK0,X2))) | r2_hidden(X3,k1_relat_1(sK1))) )),
% 2.72/0.75    inference(subsumption_resolution,[],[f87,f40])).
% 2.72/0.75  fof(f40,plain,(
% 2.72/0.75    v1_relat_1(sK1)),
% 2.72/0.75    inference(cnf_transformation,[],[f27])).
% 2.72/0.75  fof(f87,plain,(
% 2.72/0.75    ( ! [X2,X3] : (~r2_hidden(X3,k1_relat_1(k7_relat_1(sK0,X2))) | r2_hidden(X3,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 2.72/0.75    inference(superposition,[],[f61,f77])).
% 2.72/0.75  fof(f77,plain,(
% 2.72/0.75    ( ! [X1] : (k1_relat_1(k7_relat_1(sK0,X1)) = k1_relat_1(k7_relat_1(sK1,X1))) )),
% 2.72/0.75    inference(forward_demodulation,[],[f76,f68])).
% 2.72/0.75  fof(f68,plain,(
% 2.72/0.75    ( ! [X1] : (k1_relat_1(k7_relat_1(sK0,X1)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),X1))) )),
% 2.72/0.75    inference(resolution,[],[f38,f65])).
% 2.72/0.75  fof(f65,plain,(
% 2.72/0.75    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))) )),
% 2.72/0.75    inference(definition_unfolding,[],[f56,f63])).
% 2.72/0.75  fof(f63,plain,(
% 2.72/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 2.72/0.75    inference(definition_unfolding,[],[f54,f55])).
% 2.72/0.75  fof(f55,plain,(
% 2.72/0.75    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.72/0.75    inference(cnf_transformation,[],[f3])).
% 2.72/0.75  fof(f3,axiom,(
% 2.72/0.75    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.72/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.72/0.75  fof(f54,plain,(
% 2.72/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.72/0.75    inference(cnf_transformation,[],[f4])).
% 2.72/0.75  fof(f4,axiom,(
% 2.72/0.75    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.72/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.72/0.75  fof(f56,plain,(
% 2.72/0.75    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.72/0.75    inference(cnf_transformation,[],[f20])).
% 2.72/0.75  fof(f20,plain,(
% 2.72/0.75    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.72/0.75    inference(ennf_transformation,[],[f8])).
% 2.72/0.75  fof(f8,axiom,(
% 2.72/0.75    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 2.72/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 2.72/0.75  fof(f38,plain,(
% 2.72/0.75    v1_relat_1(sK0)),
% 2.72/0.75    inference(cnf_transformation,[],[f27])).
% 2.72/0.75  fof(f76,plain,(
% 2.72/0.75    ( ! [X1] : (k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),X1)) = k1_relat_1(k7_relat_1(sK1,X1))) )),
% 2.72/0.75    inference(forward_demodulation,[],[f72,f42])).
% 2.72/0.75  fof(f72,plain,(
% 2.72/0.75    ( ! [X1] : (k1_relat_1(k7_relat_1(sK1,X1)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X1))) )),
% 2.72/0.75    inference(resolution,[],[f40,f65])).
% 2.72/0.75  fof(f61,plain,(
% 2.72/0.75    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 2.72/0.75    inference(cnf_transformation,[],[f37])).
% 2.72/0.75  fof(f37,plain,(
% 2.72/0.75    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 2.72/0.75    inference(flattening,[],[f36])).
% 2.72/0.75  fof(f36,plain,(
% 2.72/0.75    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 2.72/0.75    inference(nnf_transformation,[],[f23])).
% 2.72/0.75  fof(f23,plain,(
% 2.72/0.75    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 2.72/0.75    inference(ennf_transformation,[],[f7])).
% 2.72/0.75  fof(f7,axiom,(
% 2.72/0.75    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 2.72/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).
% 2.72/0.75  fof(f1483,plain,(
% 2.72/0.75    ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))),
% 2.72/0.75    inference(forward_demodulation,[],[f1482,f42])).
% 2.72/0.75  fof(f1482,plain,(
% 2.72/0.75    ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))),
% 2.72/0.75    inference(subsumption_resolution,[],[f1481,f44])).
% 2.72/0.75  fof(f44,plain,(
% 2.72/0.75    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)),
% 2.72/0.75    inference(cnf_transformation,[],[f27])).
% 2.72/0.75  fof(f1481,plain,(
% 2.72/0.75    k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))),
% 2.72/0.75    inference(forward_demodulation,[],[f1480,f75])).
% 2.72/0.75  fof(f75,plain,(
% 2.72/0.75    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0)))) )),
% 2.72/0.75    inference(forward_demodulation,[],[f74,f68])).
% 2.72/0.75  fof(f74,plain,(
% 2.72/0.75    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),X0)))) )),
% 2.72/0.75    inference(forward_demodulation,[],[f71,f42])).
% 2.72/0.75  fof(f71,plain,(
% 2.72/0.75    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X0)))) )),
% 2.72/0.75    inference(resolution,[],[f40,f66])).
% 2.72/0.75  fof(f66,plain,(
% 2.72/0.75    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)))) )),
% 2.72/0.75    inference(definition_unfolding,[],[f57,f63])).
% 2.72/0.75  fof(f57,plain,(
% 2.72/0.75    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 2.72/0.75    inference(cnf_transformation,[],[f21])).
% 2.72/0.75  fof(f21,plain,(
% 2.72/0.75    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.72/0.75    inference(ennf_transformation,[],[f6])).
% 2.72/0.75  fof(f6,axiom,(
% 2.72/0.75    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 2.72/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).
% 2.72/0.75  fof(f1480,plain,(
% 2.72/0.75    k7_relat_1(sK0,sK2) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))),
% 2.72/0.75    inference(forward_demodulation,[],[f1479,f70])).
% 2.72/0.75  fof(f70,plain,(
% 2.72/0.75    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0)))) )),
% 2.72/0.75    inference(backward_demodulation,[],[f67,f68])).
% 2.72/0.75  fof(f67,plain,(
% 2.72/0.75    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(sK0,k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),X0)))) )),
% 2.72/0.75    inference(resolution,[],[f38,f66])).
% 2.72/0.75  fof(f1479,plain,(
% 2.72/0.75    k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))),
% 2.72/0.75    inference(subsumption_resolution,[],[f1478,f38])).
% 2.72/0.75  fof(f1478,plain,(
% 2.72/0.75    k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~v1_relat_1(sK0)),
% 2.72/0.75    inference(subsumption_resolution,[],[f1477,f39])).
% 2.72/0.75  fof(f39,plain,(
% 2.72/0.75    v1_funct_1(sK0)),
% 2.72/0.75    inference(cnf_transformation,[],[f27])).
% 2.72/0.75  fof(f1477,plain,(
% 2.72/0.75    k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 2.72/0.75    inference(subsumption_resolution,[],[f1476,f40])).
% 2.72/0.75  fof(f1476,plain,(
% 2.72/0.75    k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 2.72/0.75    inference(subsumption_resolution,[],[f1475,f41])).
% 2.72/0.75  fof(f41,plain,(
% 2.72/0.75    v1_funct_1(sK1)),
% 2.72/0.75    inference(cnf_transformation,[],[f27])).
% 2.72/0.75  fof(f1475,plain,(
% 2.72/0.75    k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 2.72/0.75    inference(subsumption_resolution,[],[f1474,f186])).
% 2.72/0.75  fof(f1474,plain,(
% 2.72/0.75    k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 2.72/0.75    inference(trivial_inequality_removal,[],[f1473])).
% 2.72/0.75  fof(f1473,plain,(
% 2.72/0.75    k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) != k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) | k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 2.72/0.75    inference(superposition,[],[f48,f1220])).
% 2.72/0.75  fof(f1220,plain,(
% 2.72/0.75    k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2))))),
% 2.72/0.75    inference(subsumption_resolution,[],[f1203,f44])).
% 2.72/0.75  fof(f1203,plain,(
% 2.72/0.75    k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2))))),
% 2.72/0.75    inference(resolution,[],[f1186,f43])).
% 2.72/0.75  fof(f43,plain,(
% 2.72/0.75    ( ! [X3] : (~r2_hidden(X3,sK2) | k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)) )),
% 2.72/0.75    inference(cnf_transformation,[],[f27])).
% 2.72/0.75  fof(f1186,plain,(
% 2.72/0.75    ( ! [X3] : (r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X3))),X3) | k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3)) )),
% 2.72/0.75    inference(resolution,[],[f1180,f90])).
% 2.72/0.75  fof(f90,plain,(
% 2.72/0.75    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(k7_relat_1(sK0,X0))) | r2_hidden(X1,X0)) )),
% 2.72/0.75    inference(subsumption_resolution,[],[f86,f40])).
% 2.72/0.75  fof(f86,plain,(
% 2.72/0.75    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(k7_relat_1(sK0,X0))) | r2_hidden(X1,X0) | ~v1_relat_1(sK1)) )),
% 2.72/0.75    inference(superposition,[],[f60,f77])).
% 2.72/0.75  fof(f60,plain,(
% 2.72/0.75    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 2.72/0.75    inference(cnf_transformation,[],[f37])).
% 2.72/0.75  fof(f1180,plain,(
% 2.72/0.75    ( ! [X12] : (r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X12))),k1_relat_1(k7_relat_1(sK0,X12))) | k7_relat_1(sK0,X12) = k7_relat_1(sK1,X12)) )),
% 2.72/0.75    inference(forward_demodulation,[],[f1179,f70])).
% 2.72/0.75  fof(f1179,plain,(
% 2.72/0.75    ( ! [X12] : (r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X12))),k1_relat_1(k7_relat_1(sK0,X12))) | k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X12))) = k7_relat_1(sK1,X12)) )),
% 2.72/0.75    inference(subsumption_resolution,[],[f1178,f38])).
% 2.72/0.75  fof(f1178,plain,(
% 2.72/0.75    ( ! [X12] : (r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X12))),k1_relat_1(k7_relat_1(sK0,X12))) | k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X12))) = k7_relat_1(sK1,X12) | ~v1_relat_1(sK0)) )),
% 2.72/0.75    inference(subsumption_resolution,[],[f1151,f39])).
% 2.72/0.75  fof(f1151,plain,(
% 2.72/0.75    ( ! [X12] : (r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X12))),k1_relat_1(k7_relat_1(sK0,X12))) | k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X12))) = k7_relat_1(sK1,X12) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)) )),
% 2.72/0.75    inference(resolution,[],[f194,f186])).
% 2.72/0.75  fof(f194,plain,(
% 2.72/0.75    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(k7_relat_1(sK0,X1)),k1_relat_1(X0)) | r2_hidden(sK3(X0,sK1,k1_relat_1(k7_relat_1(sK0,X1))),k1_relat_1(k7_relat_1(sK0,X1))) | k7_relat_1(sK1,X1) = k7_relat_1(X0,k1_relat_1(k7_relat_1(sK0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.72/0.75    inference(forward_demodulation,[],[f191,f75])).
% 2.72/0.75  fof(f191,plain,(
% 2.72/0.75    ( ! [X0,X1] : (r2_hidden(sK3(X0,sK1,k1_relat_1(k7_relat_1(sK0,X1))),k1_relat_1(k7_relat_1(sK0,X1))) | k7_relat_1(X0,k1_relat_1(k7_relat_1(sK0,X1))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X1))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,X1)),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.72/0.75    inference(resolution,[],[f186,f85])).
% 2.72/0.75  fof(f85,plain,(
% 2.72/0.75    ( ! [X2,X3] : (~r1_tarski(X2,k1_relat_1(sK0)) | r2_hidden(sK3(X3,sK1,X2),X2) | k7_relat_1(sK1,X2) = k7_relat_1(X3,X2) | ~r1_tarski(X2,k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 2.72/0.75    inference(subsumption_resolution,[],[f84,f40])).
% 2.72/0.75  fof(f84,plain,(
% 2.72/0.75    ( ! [X2,X3] : (~r1_tarski(X2,k1_relat_1(sK0)) | r2_hidden(sK3(X3,sK1,X2),X2) | k7_relat_1(sK1,X2) = k7_relat_1(X3,X2) | ~r1_tarski(X2,k1_relat_1(X3)) | ~v1_relat_1(sK1) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 2.72/0.75    inference(subsumption_resolution,[],[f81,f41])).
% 2.72/0.75  fof(f81,plain,(
% 2.72/0.75    ( ! [X2,X3] : (~r1_tarski(X2,k1_relat_1(sK0)) | r2_hidden(sK3(X3,sK1,X2),X2) | k7_relat_1(sK1,X2) = k7_relat_1(X3,X2) | ~r1_tarski(X2,k1_relat_1(X3)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 2.72/0.75    inference(superposition,[],[f47,f42])).
% 2.72/0.75  fof(f47,plain,(
% 2.72/0.75    ( ! [X2,X0,X1] : (~r1_tarski(X2,k1_relat_1(X1)) | r2_hidden(sK3(X0,X1,X2),X2) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ~r1_tarski(X2,k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.72/0.75    inference(cnf_transformation,[],[f31])).
% 2.72/0.75  fof(f31,plain,(
% 2.72/0.75    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | (k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2)) & r2_hidden(sK3(X0,X1,X2),X2))) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.72/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 2.72/0.75  fof(f30,plain,(
% 2.72/0.75    ! [X2,X1,X0] : (? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) => (k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2)) & r2_hidden(sK3(X0,X1,X2),X2)))),
% 2.72/0.75    introduced(choice_axiom,[])).
% 2.72/0.75  fof(f29,plain,(
% 2.72/0.75    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2))) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.72/0.75    inference(rectify,[],[f28])).
% 2.72/0.75  fof(f28,plain,(
% 2.72/0.75    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.72/0.75    inference(nnf_transformation,[],[f18])).
% 2.72/0.75  fof(f18,plain,(
% 2.72/0.75    ! [X0] : (! [X1] : (! [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.72/0.75    inference(flattening,[],[f17])).
% 2.72/0.75  fof(f17,plain,(
% 2.72/0.75    ! [X0] : (! [X1] : (! [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) | (~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.72/0.75    inference(ennf_transformation,[],[f10])).
% 2.72/0.75  fof(f10,axiom,(
% 2.72/0.75    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) => (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3))))))),
% 2.72/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t165_funct_1)).
% 2.72/0.75  fof(f48,plain,(
% 2.72/0.75    ( ! [X2,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2)) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.72/0.75    inference(cnf_transformation,[],[f31])).
% 2.72/0.75  % SZS output end Proof for theBenchmark
% 2.72/0.75  % (8553)------------------------------
% 2.72/0.75  % (8553)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.72/0.75  % (8553)Termination reason: Refutation
% 2.72/0.75  
% 2.72/0.75  % (8553)Memory used [KB]: 12665
% 2.72/0.75  % (8553)Time elapsed: 0.353 s
% 2.72/0.75  % (8553)------------------------------
% 2.72/0.75  % (8553)------------------------------
% 2.72/0.75  % (8542)Success in time 0.389 s
%------------------------------------------------------------------------------
