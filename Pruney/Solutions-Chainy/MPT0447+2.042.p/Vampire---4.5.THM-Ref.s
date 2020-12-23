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
% DateTime   : Thu Dec  3 12:47:14 EST 2020

% Result     : Theorem 2.61s
% Output     : Refutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 468 expanded)
%              Number of leaves         :   30 ( 144 expanded)
%              Depth                    :   19
%              Number of atoms          :  361 (1307 expanded)
%              Number of equality atoms :   72 ( 309 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1708,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1703,f1363])).

fof(f1363,plain,(
    ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f1355,f59])).

fof(f59,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
          & r1_tarski(sK0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
        & r1_tarski(sK0,X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(f1355,plain,
    ( r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f236,f1334])).

fof(f1334,plain,(
    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f1313,f287])).

fof(f287,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k2_relat_1(sK1))
      | r1_tarski(X3,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f98,f192])).

fof(f192,plain,(
    k3_relat_1(sK1) = k3_tarski(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(resolution,[],[f92,f57])).

fof(f57,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f63,f90])).

fof(f90,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f70,f71])).

fof(f71,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f70,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f63,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f82,f90])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f1313,plain,(
    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(superposition,[],[f94,f590])).

fof(f590,plain,(
    k2_relat_1(sK1) = k3_tarski(k1_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f588,f433])).

fof(f433,plain,(
    sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(resolution,[],[f325,f58])).

fof(f58,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f325,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k1_enumset1(X0,X0,X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f324,f105])).

fof(f105,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f324,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X1
      | ~ r1_tarski(X1,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f322])).

fof(f322,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X1
      | ~ r1_tarski(X1,X1)
      | ~ r1_tarski(X0,X1)
      | k3_tarski(k1_enumset1(X0,X0,X1)) = X1
      | ~ r1_tarski(X1,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f103,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,sK7(X0,X1,X2))
      | k3_tarski(k1_enumset1(X0,X0,X2)) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f88,f90])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X2) = X1
      | ~ r1_tarski(X1,sK7(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ( ~ r1_tarski(X1,sK7(X0,X1,X2))
        & r1_tarski(X2,sK7(X0,X1,X2))
        & r1_tarski(X0,sK7(X0,X1,X2)) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f38,f54])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
     => ( ~ r1_tarski(X1,sK7(X0,X1,X2))
        & r1_tarski(X2,sK7(X0,X1,X2))
        & r1_tarski(X0,sK7(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X2,X3)
              & r1_tarski(X0,X3) )
           => r1_tarski(X1,X3) )
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => k2_xboole_0(X0,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,sK7(X0,X1,X2))
      | k3_tarski(k1_enumset1(X0,X0,X2)) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f87,f90])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X2) = X1
      | r1_tarski(X2,sK7(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f588,plain,(
    k2_relat_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))) = k3_tarski(k1_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(resolution,[],[f290,f56])).

fof(f56,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f290,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k3_tarski(k1_enumset1(X1,X1,sK1))) = k3_tarski(k1_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(sK1))) ) ),
    inference(resolution,[],[f93,f57])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f64,f90,f90])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_relat_1)).

fof(f94,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f67,f90])).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f236,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK0),X0)
      | r1_tarski(k3_relat_1(sK0),X0)
      | ~ r1_tarski(k1_relat_1(sK0),X0) ) ),
    inference(superposition,[],[f101,f191])).

fof(f191,plain,(
    k3_relat_1(sK0) = k3_tarski(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(resolution,[],[f92,f56])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f85,f90])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f1703,plain,(
    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f1693,f961])).

fof(f961,plain,(
    ! [X6] :
      ( ~ r1_tarski(X6,k1_relat_1(sK1))
      | r1_tarski(X6,k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f852,f285])).

fof(f285,plain,(
    ! [X1] :
      ( ~ r1_tarski(k6_subset_1(X1,k1_relat_1(sK1)),k2_relat_1(sK1))
      | r1_tarski(X1,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f100,f192])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f84,f90,f68])).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f852,plain,(
    ! [X2,X3,X1] :
      ( r1_tarski(k6_subset_1(X1,X2),X3)
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f710,f709])).

fof(f709,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,k1_xboole_0)
      | r1_tarski(X2,X1) ) ),
    inference(superposition,[],[f98,f457])).

fof(f457,plain,(
    ! [X15] : k3_tarski(k1_enumset1(X15,X15,k1_xboole_0)) = X15 ),
    inference(resolution,[],[f340,f61])).

fof(f61,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f340,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_tarski(k1_enumset1(X0,X0,X1)) = X0 ) ),
    inference(subsumption_resolution,[],[f339,f105])).

fof(f339,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f337])).

fof(f337,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0)
      | k3_tarski(k1_enumset1(X0,X0,X1)) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f104,f102])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,sK7(X0,X1,X2))
      | k3_tarski(k1_enumset1(X0,X0,X2)) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f86,f90])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X2) = X1
      | r1_tarski(X0,sK7(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f710,plain,(
    ! [X4,X3] :
      ( r1_tarski(k6_subset_1(X4,X3),k1_xboole_0)
      | ~ r1_tarski(X4,X3) ) ),
    inference(superposition,[],[f99,f457])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
      | r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f83,f68,f90])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f1693,plain,(
    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f1097,f711])).

fof(f711,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(k6_subset_1(X6,X5),k1_xboole_0)
      | r1_tarski(X6,X5) ) ),
    inference(superposition,[],[f100,f457])).

fof(f1097,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1096,f137])).

fof(f137,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f136,f66])).

fof(f66,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f136,plain,(
    ! [X7] : ~ r2_hidden(X7,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f108,f131])).

fof(f131,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f129,f91])).

fof(f91,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f62,f68])).

fof(f62,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f129,plain,(
    ! [X0,X1] : ~ r2_hidden(X1,k6_subset_1(X0,X0)) ),
    inference(subsumption_resolution,[],[f128,f60])).

fof(f60,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k6_subset_1(X0,X0))
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f126,f91])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k6_subset_1(X0,k6_subset_1(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(backward_demodulation,[],[f96,f95])).

fof(f95,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f72,f89,f68,f68])).

fof(f89,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f69,f71])).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f74,f89])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f108,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f49,f52,f51,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f1096,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f1095,f56])).

fof(f1095,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f1074,f57])).

fof(f1074,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f65,f1067])).

fof(f1067,plain,(
    k1_xboole_0 = k6_subset_1(sK0,sK1) ),
    inference(resolution,[],[f855,f58])).

fof(f855,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(X10,X11)
      | k1_xboole_0 = k6_subset_1(X10,X11) ) ),
    inference(resolution,[],[f710,f110])).

fof(f110,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f77,f61])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:18:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.55  % (16341)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.55  % (16339)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.55  % (16338)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.56  % (16343)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.56  % (16340)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.58/0.57  % (16342)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.58/0.58  % (16349)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.58/0.59  % (16348)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.58/0.59  % (16348)Refutation not found, incomplete strategy% (16348)------------------------------
% 1.58/0.59  % (16348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.59  % (16348)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.59  
% 1.58/0.59  % (16348)Memory used [KB]: 10746
% 1.58/0.59  % (16348)Time elapsed: 0.163 s
% 1.58/0.59  % (16348)------------------------------
% 1.58/0.59  % (16348)------------------------------
% 1.58/0.59  % (16355)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.77/0.59  % (16344)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.77/0.59  % (16353)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.77/0.59  % (16361)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.77/0.59  % (16354)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.77/0.60  % (16347)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.77/0.60  % (16365)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.77/0.60  % (16367)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.77/0.60  % (16364)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.77/0.60  % (16346)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.77/0.60  % (16359)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.77/0.61  % (16363)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.77/0.61  % (16357)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.77/0.61  % (16352)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.77/0.61  % (16350)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.77/0.61  % (16351)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.77/0.62  % (16362)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.77/0.62  % (16354)Refutation not found, incomplete strategy% (16354)------------------------------
% 1.77/0.62  % (16354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.62  % (16354)Termination reason: Refutation not found, incomplete strategy
% 1.77/0.62  
% 1.77/0.62  % (16354)Memory used [KB]: 10618
% 1.77/0.62  % (16354)Time elapsed: 0.169 s
% 1.77/0.62  % (16354)------------------------------
% 1.77/0.62  % (16354)------------------------------
% 1.77/0.62  % (16345)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.77/0.62  % (16358)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.77/0.62  % (16356)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.77/0.63  % (16367)Refutation not found, incomplete strategy% (16367)------------------------------
% 1.77/0.63  % (16367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.63  % (16367)Termination reason: Refutation not found, incomplete strategy
% 1.77/0.63  
% 1.77/0.63  % (16367)Memory used [KB]: 1663
% 1.77/0.63  % (16367)Time elapsed: 0.201 s
% 1.77/0.63  % (16367)------------------------------
% 1.77/0.63  % (16367)------------------------------
% 1.77/0.63  % (16366)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.77/0.63  % (16366)Refutation not found, incomplete strategy% (16366)------------------------------
% 1.77/0.63  % (16366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.63  % (16366)Termination reason: Refutation not found, incomplete strategy
% 1.77/0.63  
% 1.77/0.63  % (16366)Memory used [KB]: 10746
% 1.77/0.63  % (16366)Time elapsed: 0.200 s
% 1.77/0.63  % (16366)------------------------------
% 1.77/0.63  % (16366)------------------------------
% 2.22/0.65  % (16360)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 2.61/0.71  % (16344)Refutation found. Thanks to Tanya!
% 2.61/0.71  % SZS status Theorem for theBenchmark
% 2.61/0.71  % SZS output start Proof for theBenchmark
% 2.61/0.71  fof(f1708,plain,(
% 2.61/0.71    $false),
% 2.61/0.71    inference(subsumption_resolution,[],[f1703,f1363])).
% 2.61/0.71  fof(f1363,plain,(
% 2.61/0.71    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 2.61/0.71    inference(subsumption_resolution,[],[f1355,f59])).
% 2.61/0.71  fof(f59,plain,(
% 2.61/0.71    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 2.61/0.71    inference(cnf_transformation,[],[f41])).
% 2.61/0.71  fof(f41,plain,(
% 2.61/0.71    (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 2.61/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f40,f39])).
% 2.61/0.71  fof(f39,plain,(
% 2.61/0.71    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 2.61/0.71    introduced(choice_axiom,[])).
% 2.61/0.71  fof(f40,plain,(
% 2.61/0.71    ? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1))),
% 2.61/0.71    introduced(choice_axiom,[])).
% 2.61/0.71  fof(f26,plain,(
% 2.61/0.71    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.61/0.71    inference(flattening,[],[f25])).
% 2.61/0.71  fof(f25,plain,(
% 2.61/0.71    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.61/0.71    inference(ennf_transformation,[],[f23])).
% 2.61/0.71  fof(f23,negated_conjecture,(
% 2.61/0.71    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.61/0.71    inference(negated_conjecture,[],[f22])).
% 2.61/0.71  fof(f22,conjecture,(
% 2.61/0.71    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.61/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).
% 2.61/0.71  fof(f1355,plain,(
% 2.61/0.71    r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 2.61/0.71    inference(resolution,[],[f236,f1334])).
% 2.61/0.71  fof(f1334,plain,(
% 2.61/0.71    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))),
% 2.61/0.71    inference(resolution,[],[f1313,f287])).
% 2.61/0.71  fof(f287,plain,(
% 2.61/0.71    ( ! [X3] : (~r1_tarski(X3,k2_relat_1(sK1)) | r1_tarski(X3,k3_relat_1(sK1))) )),
% 2.61/0.71    inference(superposition,[],[f98,f192])).
% 2.61/0.71  fof(f192,plain,(
% 2.61/0.71    k3_relat_1(sK1) = k3_tarski(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k2_relat_1(sK1)))),
% 2.61/0.71    inference(resolution,[],[f92,f57])).
% 2.61/0.71  fof(f57,plain,(
% 2.61/0.71    v1_relat_1(sK1)),
% 2.61/0.71    inference(cnf_transformation,[],[f41])).
% 2.61/0.71  fof(f92,plain,(
% 2.61/0.71    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))) )),
% 2.61/0.71    inference(definition_unfolding,[],[f63,f90])).
% 2.61/0.71  fof(f90,plain,(
% 2.61/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 2.61/0.71    inference(definition_unfolding,[],[f70,f71])).
% 2.61/0.71  fof(f71,plain,(
% 2.61/0.71    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.61/0.71    inference(cnf_transformation,[],[f14])).
% 2.61/0.71  fof(f14,axiom,(
% 2.61/0.71    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.61/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.61/0.71  fof(f70,plain,(
% 2.61/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.61/0.71    inference(cnf_transformation,[],[f15])).
% 2.61/0.71  fof(f15,axiom,(
% 2.61/0.71    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.61/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.61/0.71  fof(f63,plain,(
% 2.61/0.71    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.61/0.71    inference(cnf_transformation,[],[f27])).
% 2.61/0.71  fof(f27,plain,(
% 2.61/0.71    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.61/0.71    inference(ennf_transformation,[],[f19])).
% 2.61/0.71  fof(f19,axiom,(
% 2.61/0.71    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 2.61/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 2.61/0.71  fof(f98,plain,(
% 2.61/0.71    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 2.61/0.71    inference(definition_unfolding,[],[f82,f90])).
% 2.61/0.71  fof(f82,plain,(
% 2.61/0.71    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.61/0.71    inference(cnf_transformation,[],[f32])).
% 2.61/0.71  fof(f32,plain,(
% 2.61/0.71    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.61/0.71    inference(ennf_transformation,[],[f4])).
% 2.61/0.71  fof(f4,axiom,(
% 2.61/0.71    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.61/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 2.61/0.71  fof(f1313,plain,(
% 2.61/0.71    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 2.61/0.71    inference(superposition,[],[f94,f590])).
% 2.61/0.71  fof(f590,plain,(
% 2.61/0.71    k2_relat_1(sK1) = k3_tarski(k1_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1)))),
% 2.61/0.71    inference(forward_demodulation,[],[f588,f433])).
% 2.61/0.71  fof(f433,plain,(
% 2.61/0.71    sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 2.61/0.71    inference(resolution,[],[f325,f58])).
% 2.61/0.71  fof(f58,plain,(
% 2.61/0.71    r1_tarski(sK0,sK1)),
% 2.61/0.71    inference(cnf_transformation,[],[f41])).
% 2.61/0.71  fof(f325,plain,(
% 2.61/0.71    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k1_enumset1(X0,X0,X1)) = X1) )),
% 2.61/0.71    inference(subsumption_resolution,[],[f324,f105])).
% 2.61/0.71  fof(f105,plain,(
% 2.61/0.71    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.61/0.71    inference(equality_resolution,[],[f76])).
% 2.61/0.71  fof(f76,plain,(
% 2.61/0.71    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.61/0.71    inference(cnf_transformation,[],[f47])).
% 2.61/0.71  fof(f47,plain,(
% 2.61/0.71    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.61/0.71    inference(flattening,[],[f46])).
% 2.61/0.71  fof(f46,plain,(
% 2.61/0.71    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.61/0.71    inference(nnf_transformation,[],[f3])).
% 2.61/0.71  fof(f3,axiom,(
% 2.61/0.71    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.61/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.61/0.71  fof(f324,plain,(
% 2.61/0.71    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X1 | ~r1_tarski(X1,X1) | ~r1_tarski(X0,X1)) )),
% 2.61/0.71    inference(duplicate_literal_removal,[],[f322])).
% 2.61/0.71  fof(f322,plain,(
% 2.61/0.71    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X1 | ~r1_tarski(X1,X1) | ~r1_tarski(X0,X1) | k3_tarski(k1_enumset1(X0,X0,X1)) = X1 | ~r1_tarski(X1,X1) | ~r1_tarski(X0,X1)) )),
% 2.61/0.71    inference(resolution,[],[f103,f102])).
% 2.61/0.71  fof(f102,plain,(
% 2.61/0.71    ( ! [X2,X0,X1] : (~r1_tarski(X1,sK7(X0,X1,X2)) | k3_tarski(k1_enumset1(X0,X0,X2)) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.61/0.71    inference(definition_unfolding,[],[f88,f90])).
% 2.61/0.71  fof(f88,plain,(
% 2.61/0.71    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X1,sK7(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.61/0.71    inference(cnf_transformation,[],[f55])).
% 2.61/0.71  fof(f55,plain,(
% 2.61/0.71    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (~r1_tarski(X1,sK7(X0,X1,X2)) & r1_tarski(X2,sK7(X0,X1,X2)) & r1_tarski(X0,sK7(X0,X1,X2))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.61/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f38,f54])).
% 2.61/0.71  fof(f54,plain,(
% 2.61/0.71    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) => (~r1_tarski(X1,sK7(X0,X1,X2)) & r1_tarski(X2,sK7(X0,X1,X2)) & r1_tarski(X0,sK7(X0,X1,X2))))),
% 2.61/0.71    introduced(choice_axiom,[])).
% 2.61/0.71  fof(f38,plain,(
% 2.61/0.71    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | ? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.61/0.71    inference(flattening,[],[f37])).
% 2.61/0.71  fof(f37,plain,(
% 2.61/0.71    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (? [X3] : (~r1_tarski(X1,X3) & (r1_tarski(X2,X3) & r1_tarski(X0,X3))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.61/0.71    inference(ennf_transformation,[],[f5])).
% 2.61/0.71  fof(f5,axiom,(
% 2.61/0.71    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X3)) => r1_tarski(X1,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => k2_xboole_0(X0,X2) = X1)),
% 2.61/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).
% 2.61/0.71  fof(f103,plain,(
% 2.61/0.71    ( ! [X2,X0,X1] : (r1_tarski(X2,sK7(X0,X1,X2)) | k3_tarski(k1_enumset1(X0,X0,X2)) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.61/0.71    inference(definition_unfolding,[],[f87,f90])).
% 2.61/0.71  fof(f87,plain,(
% 2.61/0.71    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X2) = X1 | r1_tarski(X2,sK7(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.61/0.71    inference(cnf_transformation,[],[f55])).
% 2.61/0.71  fof(f588,plain,(
% 2.61/0.71    k2_relat_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))) = k3_tarski(k1_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1)))),
% 2.61/0.71    inference(resolution,[],[f290,f56])).
% 2.61/0.71  fof(f56,plain,(
% 2.61/0.71    v1_relat_1(sK0)),
% 2.61/0.71    inference(cnf_transformation,[],[f41])).
% 2.61/0.71  fof(f290,plain,(
% 2.61/0.71    ( ! [X1] : (~v1_relat_1(X1) | k2_relat_1(k3_tarski(k1_enumset1(X1,X1,sK1))) = k3_tarski(k1_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(sK1)))) )),
% 2.61/0.71    inference(resolution,[],[f93,f57])).
% 2.61/0.71  fof(f93,plain,(
% 2.61/0.71    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X0)) )),
% 2.61/0.71    inference(definition_unfolding,[],[f64,f90,f90])).
% 2.61/0.71  fof(f64,plain,(
% 2.61/0.71    ( ! [X0,X1] : (k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.61/0.71    inference(cnf_transformation,[],[f28])).
% 2.61/0.71  fof(f28,plain,(
% 2.61/0.71    ! [X0] : (! [X1] : (k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.61/0.71    inference(ennf_transformation,[],[f21])).
% 2.61/0.71  fof(f21,axiom,(
% 2.61/0.71    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))))),
% 2.61/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_relat_1)).
% 2.61/0.71  fof(f94,plain,(
% 2.61/0.71    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 2.61/0.71    inference(definition_unfolding,[],[f67,f90])).
% 2.61/0.71  fof(f67,plain,(
% 2.61/0.71    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.61/0.71    inference(cnf_transformation,[],[f12])).
% 2.61/0.71  fof(f12,axiom,(
% 2.61/0.71    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.61/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.61/0.71  fof(f236,plain,(
% 2.61/0.71    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),X0) | r1_tarski(k3_relat_1(sK0),X0) | ~r1_tarski(k1_relat_1(sK0),X0)) )),
% 2.61/0.71    inference(superposition,[],[f101,f191])).
% 2.61/0.71  fof(f191,plain,(
% 2.61/0.71    k3_relat_1(sK0) = k3_tarski(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k2_relat_1(sK0)))),
% 2.61/0.71    inference(resolution,[],[f92,f56])).
% 2.61/0.71  fof(f101,plain,(
% 2.61/0.71    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.61/0.71    inference(definition_unfolding,[],[f85,f90])).
% 2.61/0.71  fof(f85,plain,(
% 2.61/0.71    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.61/0.71    inference(cnf_transformation,[],[f36])).
% 2.61/0.71  fof(f36,plain,(
% 2.61/0.71    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.61/0.71    inference(flattening,[],[f35])).
% 2.61/0.71  fof(f35,plain,(
% 2.61/0.71    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.61/0.71    inference(ennf_transformation,[],[f13])).
% 2.61/0.71  fof(f13,axiom,(
% 2.61/0.71    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 2.61/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 2.61/0.71  fof(f1703,plain,(
% 2.61/0.71    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 2.61/0.71    inference(resolution,[],[f1693,f961])).
% 2.61/0.71  fof(f961,plain,(
% 2.61/0.71    ( ! [X6] : (~r1_tarski(X6,k1_relat_1(sK1)) | r1_tarski(X6,k3_relat_1(sK1))) )),
% 2.61/0.71    inference(resolution,[],[f852,f285])).
% 2.61/0.71  fof(f285,plain,(
% 2.61/0.71    ( ! [X1] : (~r1_tarski(k6_subset_1(X1,k1_relat_1(sK1)),k2_relat_1(sK1)) | r1_tarski(X1,k3_relat_1(sK1))) )),
% 2.61/0.71    inference(superposition,[],[f100,f192])).
% 2.61/0.71  fof(f100,plain,(
% 2.61/0.71    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | ~r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 2.61/0.71    inference(definition_unfolding,[],[f84,f90,f68])).
% 2.61/0.71  fof(f68,plain,(
% 2.61/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.61/0.71    inference(cnf_transformation,[],[f16])).
% 2.61/0.71  fof(f16,axiom,(
% 2.61/0.71    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.61/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.61/0.71  fof(f84,plain,(
% 2.61/0.71    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.61/0.71    inference(cnf_transformation,[],[f34])).
% 2.61/0.71  fof(f34,plain,(
% 2.61/0.71    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.61/0.71    inference(ennf_transformation,[],[f9])).
% 2.61/0.71  fof(f9,axiom,(
% 2.61/0.71    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.61/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.61/0.71  fof(f852,plain,(
% 2.61/0.71    ( ! [X2,X3,X1] : (r1_tarski(k6_subset_1(X1,X2),X3) | ~r1_tarski(X1,X2)) )),
% 2.61/0.71    inference(resolution,[],[f710,f709])).
% 2.61/0.71  fof(f709,plain,(
% 2.61/0.71    ( ! [X2,X1] : (~r1_tarski(X2,k1_xboole_0) | r1_tarski(X2,X1)) )),
% 2.61/0.71    inference(superposition,[],[f98,f457])).
% 2.61/0.71  fof(f457,plain,(
% 2.61/0.71    ( ! [X15] : (k3_tarski(k1_enumset1(X15,X15,k1_xboole_0)) = X15) )),
% 2.61/0.71    inference(resolution,[],[f340,f61])).
% 2.61/0.71  fof(f61,plain,(
% 2.61/0.71    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.61/0.71    inference(cnf_transformation,[],[f6])).
% 2.61/0.71  fof(f6,axiom,(
% 2.61/0.71    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.61/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.61/0.71  fof(f340,plain,(
% 2.61/0.71    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_tarski(k1_enumset1(X0,X0,X1)) = X0) )),
% 2.61/0.71    inference(subsumption_resolution,[],[f339,f105])).
% 2.61/0.71  fof(f339,plain,(
% 2.61/0.71    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0)) )),
% 2.61/0.71    inference(duplicate_literal_removal,[],[f337])).
% 2.61/0.71  fof(f337,plain,(
% 2.61/0.71    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0) | k3_tarski(k1_enumset1(X0,X0,X1)) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0)) )),
% 2.61/0.71    inference(resolution,[],[f104,f102])).
% 2.61/0.71  fof(f104,plain,(
% 2.61/0.71    ( ! [X2,X0,X1] : (r1_tarski(X0,sK7(X0,X1,X2)) | k3_tarski(k1_enumset1(X0,X0,X2)) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.61/0.71    inference(definition_unfolding,[],[f86,f90])).
% 2.61/0.71  fof(f86,plain,(
% 2.61/0.71    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X2) = X1 | r1_tarski(X0,sK7(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.61/0.71    inference(cnf_transformation,[],[f55])).
% 2.61/0.71  fof(f710,plain,(
% 2.61/0.71    ( ! [X4,X3] : (r1_tarski(k6_subset_1(X4,X3),k1_xboole_0) | ~r1_tarski(X4,X3)) )),
% 2.61/0.71    inference(superposition,[],[f99,f457])).
% 2.61/0.71  fof(f99,plain,(
% 2.61/0.71    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 2.61/0.71    inference(definition_unfolding,[],[f83,f68,f90])).
% 2.61/0.71  fof(f83,plain,(
% 2.61/0.71    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.61/0.71    inference(cnf_transformation,[],[f33])).
% 2.61/0.71  fof(f33,plain,(
% 2.61/0.71    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.61/0.71    inference(ennf_transformation,[],[f8])).
% 2.61/0.71  fof(f8,axiom,(
% 2.61/0.71    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.61/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 2.61/0.71  fof(f1693,plain,(
% 2.61/0.71    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))),
% 2.61/0.71    inference(resolution,[],[f1097,f711])).
% 2.61/0.71  fof(f711,plain,(
% 2.61/0.71    ( ! [X6,X5] : (~r1_tarski(k6_subset_1(X6,X5),k1_xboole_0) | r1_tarski(X6,X5)) )),
% 2.61/0.71    inference(superposition,[],[f100,f457])).
% 2.61/0.71  fof(f1097,plain,(
% 2.61/0.71    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_xboole_0)),
% 2.61/0.71    inference(forward_demodulation,[],[f1096,f137])).
% 2.61/0.71  fof(f137,plain,(
% 2.61/0.71    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.61/0.71    inference(resolution,[],[f136,f66])).
% 2.61/0.71  fof(f66,plain,(
% 2.61/0.71    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 2.61/0.71    inference(cnf_transformation,[],[f43])).
% 2.61/0.71  fof(f43,plain,(
% 2.61/0.71    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 2.61/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f42])).
% 2.61/0.71  fof(f42,plain,(
% 2.61/0.71    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 2.61/0.71    introduced(choice_axiom,[])).
% 2.61/0.71  fof(f30,plain,(
% 2.61/0.71    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.61/0.71    inference(ennf_transformation,[],[f2])).
% 2.61/0.71  fof(f2,axiom,(
% 2.61/0.71    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.61/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.61/0.71  fof(f136,plain,(
% 2.61/0.71    ( ! [X7] : (~r2_hidden(X7,k1_relat_1(k1_xboole_0))) )),
% 2.61/0.71    inference(resolution,[],[f108,f131])).
% 2.61/0.71  fof(f131,plain,(
% 2.61/0.71    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.61/0.71    inference(superposition,[],[f129,f91])).
% 2.61/0.71  fof(f91,plain,(
% 2.61/0.71    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 2.61/0.71    inference(definition_unfolding,[],[f62,f68])).
% 2.61/0.71  fof(f62,plain,(
% 2.61/0.71    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.61/0.71    inference(cnf_transformation,[],[f7])).
% 2.61/0.71  fof(f7,axiom,(
% 2.61/0.71    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.61/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.61/0.71  fof(f129,plain,(
% 2.61/0.71    ( ! [X0,X1] : (~r2_hidden(X1,k6_subset_1(X0,X0))) )),
% 2.61/0.71    inference(subsumption_resolution,[],[f128,f60])).
% 2.61/0.71  fof(f60,plain,(
% 2.61/0.71    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.61/0.71    inference(cnf_transformation,[],[f11])).
% 2.61/0.71  fof(f11,axiom,(
% 2.61/0.71    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.61/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.61/0.71  fof(f128,plain,(
% 2.61/0.71    ( ! [X0,X1] : (~r2_hidden(X1,k6_subset_1(X0,X0)) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 2.61/0.71    inference(superposition,[],[f126,f91])).
% 2.61/0.71  fof(f126,plain,(
% 2.61/0.71    ( ! [X2,X0,X1] : (~r2_hidden(X2,k6_subset_1(X0,k6_subset_1(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 2.61/0.71    inference(backward_demodulation,[],[f96,f95])).
% 2.61/0.71  fof(f95,plain,(
% 2.61/0.71    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 2.61/0.71    inference(definition_unfolding,[],[f72,f89,f68,f68])).
% 2.61/0.71  fof(f89,plain,(
% 2.61/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 2.61/0.71    inference(definition_unfolding,[],[f69,f71])).
% 2.61/0.71  fof(f69,plain,(
% 2.61/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.61/0.71    inference(cnf_transformation,[],[f17])).
% 2.61/0.71  fof(f17,axiom,(
% 2.61/0.71    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.61/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.61/0.71  fof(f72,plain,(
% 2.61/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.61/0.71    inference(cnf_transformation,[],[f10])).
% 2.61/0.71  fof(f10,axiom,(
% 2.61/0.71    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.61/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.61/0.71  fof(f96,plain,(
% 2.61/0.71    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 2.61/0.71    inference(definition_unfolding,[],[f74,f89])).
% 2.61/0.71  fof(f74,plain,(
% 2.61/0.71    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.61/0.71    inference(cnf_transformation,[],[f45])).
% 2.61/0.71  fof(f45,plain,(
% 2.61/0.71    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.61/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f44])).
% 2.61/0.71  fof(f44,plain,(
% 2.61/0.71    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 2.61/0.71    introduced(choice_axiom,[])).
% 2.61/0.71  fof(f31,plain,(
% 2.61/0.71    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.61/0.71    inference(ennf_transformation,[],[f24])).
% 2.61/0.71  fof(f24,plain,(
% 2.61/0.71    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.61/0.71    inference(rectify,[],[f1])).
% 2.61/0.71  fof(f1,axiom,(
% 2.61/0.71    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.61/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.61/0.71  fof(f108,plain,(
% 2.61/0.71    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 2.61/0.71    inference(equality_resolution,[],[f78])).
% 2.61/0.71  fof(f78,plain,(
% 2.61/0.71    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 2.61/0.71    inference(cnf_transformation,[],[f53])).
% 2.61/0.71  fof(f53,plain,(
% 2.61/0.71    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK4(X0,X1),X3),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.61/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f49,f52,f51,f50])).
% 2.61/0.71  fof(f50,plain,(
% 2.61/0.71    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK4(X0,X1),X3),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 2.61/0.71    introduced(choice_axiom,[])).
% 2.61/0.71  fof(f51,plain,(
% 2.61/0.71    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0))),
% 2.61/0.71    introduced(choice_axiom,[])).
% 2.61/0.71  fof(f52,plain,(
% 2.61/0.71    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0))),
% 2.61/0.71    introduced(choice_axiom,[])).
% 2.61/0.71  fof(f49,plain,(
% 2.61/0.71    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.61/0.71    inference(rectify,[],[f48])).
% 2.61/0.71  fof(f48,plain,(
% 2.61/0.71    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.61/0.71    inference(nnf_transformation,[],[f18])).
% 2.61/0.71  fof(f18,axiom,(
% 2.61/0.71    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.61/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 2.61/0.71  fof(f1096,plain,(
% 2.61/0.71    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0))),
% 2.61/0.71    inference(subsumption_resolution,[],[f1095,f56])).
% 2.61/0.71  fof(f1095,plain,(
% 2.61/0.71    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(sK0)),
% 2.61/0.71    inference(subsumption_resolution,[],[f1074,f57])).
% 2.61/0.71  fof(f1074,plain,(
% 2.61/0.71    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 2.61/0.71    inference(superposition,[],[f65,f1067])).
% 2.61/0.71  fof(f1067,plain,(
% 2.61/0.71    k1_xboole_0 = k6_subset_1(sK0,sK1)),
% 2.61/0.71    inference(resolution,[],[f855,f58])).
% 2.61/0.71  fof(f855,plain,(
% 2.61/0.71    ( ! [X10,X11] : (~r1_tarski(X10,X11) | k1_xboole_0 = k6_subset_1(X10,X11)) )),
% 2.61/0.71    inference(resolution,[],[f710,f110])).
% 2.61/0.71  fof(f110,plain,(
% 2.61/0.71    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.61/0.71    inference(resolution,[],[f77,f61])).
% 2.61/0.71  fof(f77,plain,(
% 2.61/0.71    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.61/0.71    inference(cnf_transformation,[],[f47])).
% 2.61/0.71  fof(f65,plain,(
% 2.61/0.71    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.61/0.71    inference(cnf_transformation,[],[f29])).
% 2.61/0.71  fof(f29,plain,(
% 2.61/0.71    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.61/0.71    inference(ennf_transformation,[],[f20])).
% 2.61/0.71  fof(f20,axiom,(
% 2.61/0.71    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 2.61/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).
% 2.61/0.71  % SZS output end Proof for theBenchmark
% 2.61/0.71  % (16344)------------------------------
% 2.61/0.71  % (16344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.61/0.71  % (16344)Termination reason: Refutation
% 2.61/0.71  
% 2.61/0.71  % (16344)Memory used [KB]: 11641
% 2.61/0.71  % (16344)Time elapsed: 0.271 s
% 2.61/0.71  % (16344)------------------------------
% 2.61/0.71  % (16344)------------------------------
% 2.61/0.73  % (16337)Success in time 0.359 s
%------------------------------------------------------------------------------
