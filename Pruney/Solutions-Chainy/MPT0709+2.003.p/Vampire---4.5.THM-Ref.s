%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:36 EST 2020

% Result     : Theorem 2.54s
% Output     : Refutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :  131 (1669 expanded)
%              Number of leaves         :   20 ( 409 expanded)
%              Depth                    :   35
%              Number of atoms          :  318 (5935 expanded)
%              Number of equality atoms :   80 (1247 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3334,plain,(
    $false ),
    inference(resolution,[],[f3263,f336])).

fof(f336,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(subsumption_resolution,[],[f335,f66])).

fof(f66,plain,(
    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
    & v2_funct_1(sK1)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f48])).

fof(f48,plain,
    ( ? [X0,X1] :
        ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
        & v2_funct_1(X1)
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
      & v2_funct_1(sK1)
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f335,plain,
    ( sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0))
    | ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(resolution,[],[f332,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
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

fof(f332,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(resolution,[],[f323,f64])).

fof(f64,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f49])).

fof(f323,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK1))
      | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) ) ),
    inference(resolution,[],[f83,f62])).

fof(f62,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f3263,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ),
    inference(resolution,[],[f3250,f1865])).

fof(f1865,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k10_relat_1(k6_relat_1(k2_relat_1(sK1)),X4),k9_relat_1(sK1,X5))
      | r1_tarski(k10_relat_1(sK1,X4),X5) ) ),
    inference(subsumption_resolution,[],[f1858,f425])).

fof(f425,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f169,f395])).

fof(f395,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f374,f109])).

fof(f109,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f374,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(superposition,[],[f182,f366])).

fof(f366,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1))) ),
    inference(global_subsumption,[],[f339])).

fof(f339,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1))) ),
    inference(resolution,[],[f326,f265])).

fof(f265,plain,(
    ! [X6] :
      ( ~ r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,X6))
      | k1_relat_1(sK1) = k10_relat_1(sK1,X6) ) ),
    inference(subsumption_resolution,[],[f263,f89])).

fof(f263,plain,(
    ! [X6] :
      ( r1_tarski(k10_relat_1(sK1,X6),k1_relat_1(sK1))
      | ~ r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,X6))
      | k1_relat_1(sK1) = k10_relat_1(sK1,X6) ) ),
    inference(resolution,[],[f259,f114])).

fof(f114,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(sK3(X2,X1),X1)
      | ~ r1_tarski(X1,X2)
      | X1 = X2 ) ),
    inference(resolution,[],[f89,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f55,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f259,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(k10_relat_1(sK1,X0),X1),k1_relat_1(sK1))
      | r1_tarski(k10_relat_1(sK1,X0),X1) ) ),
    inference(subsumption_resolution,[],[f254,f62])).

fof(f254,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(k10_relat_1(sK1,X0),X1),k1_relat_1(sK1))
      | r1_tarski(k10_relat_1(sK1,X0),X1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f249,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f249,plain,(
    ! [X8,X7,X9] :
      ( ~ r1_tarski(k10_relat_1(sK1,k2_relat_1(sK1)),X9)
      | r2_hidden(sK3(k10_relat_1(sK1,X7),X8),X9)
      | r1_tarski(k10_relat_1(sK1,X7),X8) ) ),
    inference(resolution,[],[f236,f90])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f236,plain,(
    ! [X21,X20] :
      ( r2_hidden(sK3(k10_relat_1(sK1,X20),X21),k10_relat_1(sK1,k2_relat_1(sK1)))
      | r1_tarski(k10_relat_1(sK1,X20),X21) ) ),
    inference(resolution,[],[f136,f169])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r2_hidden(sK3(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f90,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f326,plain,(
    r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1)))) ),
    inference(resolution,[],[f323,f109])).

fof(f182,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,X0))
      | k10_relat_1(sK1,X0) = k10_relat_1(sK1,k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f177,f62])).

fof(f177,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,X0))
      | k10_relat_1(sK1,X0) = k10_relat_1(sK1,k2_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f175,f81])).

fof(f175,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(sK1,k2_relat_1(sK1)),X1)
      | ~ r1_tarski(X1,k10_relat_1(sK1,X0))
      | k10_relat_1(sK1,X0) = k10_relat_1(sK1,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f172,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f172,plain,(
    ! [X0] :
      ( ~ r1_tarski(k10_relat_1(sK1,k2_relat_1(sK1)),k10_relat_1(sK1,X0))
      | k10_relat_1(sK1,X0) = k10_relat_1(sK1,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f169,f89])).

fof(f169,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,k2_relat_1(sK1))) ),
    inference(resolution,[],[f82,f62])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).

fof(f1858,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k10_relat_1(k6_relat_1(k2_relat_1(sK1)),X4),k9_relat_1(sK1,X5))
      | ~ r1_tarski(k10_relat_1(sK1,X4),k1_relat_1(sK1))
      | r1_tarski(k10_relat_1(sK1,X4),X5) ) ),
    inference(superposition,[],[f1699,f1658])).

fof(f1658,plain,(
    ! [X1] : k9_relat_1(sK1,k10_relat_1(sK1,X1)) = k10_relat_1(k6_relat_1(k2_relat_1(sK1)),X1) ),
    inference(forward_demodulation,[],[f1657,f72])).

fof(f72,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1657,plain,(
    ! [X1] : k9_relat_1(sK1,k10_relat_1(sK1,X1)) = k10_relat_1(k6_relat_1(k2_relat_1(sK1)),k1_relat_1(k6_relat_1(X1))) ),
    inference(subsumption_resolution,[],[f1656,f70])).

fof(f70,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f1656,plain,(
    ! [X1] :
      ( k9_relat_1(sK1,k10_relat_1(sK1,X1)) = k10_relat_1(k6_relat_1(k2_relat_1(sK1)),k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(sK1))) ) ),
    inference(subsumption_resolution,[],[f1649,f70])).

fof(f1649,plain,(
    ! [X1] :
      ( k9_relat_1(sK1,k10_relat_1(sK1,X1)) = k10_relat_1(k6_relat_1(k2_relat_1(sK1)),k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(sK1))) ) ),
    inference(superposition,[],[f1560,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f1560,plain,(
    ! [X2] : k9_relat_1(sK1,k10_relat_1(sK1,X2)) = k1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK1)),k6_relat_1(X2))) ),
    inference(superposition,[],[f72,f1547])).

fof(f1547,plain,(
    ! [X0] : k5_relat_1(k6_relat_1(k2_relat_1(sK1)),k6_relat_1(X0)) = k6_relat_1(k9_relat_1(sK1,k10_relat_1(sK1,X0))) ),
    inference(superposition,[],[f105,f1488])).

fof(f1488,plain,(
    ! [X0] : k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f1487,f825])).

fof(f825,plain,(
    k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1) ),
    inference(forward_demodulation,[],[f820,f395])).

fof(f820,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k10_relat_1(sK1,k2_relat_1(sK1))) ),
    inference(resolution,[],[f819,f109])).

fof(f819,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK1))
      | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f818,f62])).

fof(f818,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK1))
      | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f86,f63])).

fof(f63,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f1487,plain,(
    ! [X0] : k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k1_setfam_1(k2_enumset1(X0,X0,X0,k9_relat_1(sK1,k1_relat_1(sK1)))) ),
    inference(subsumption_resolution,[],[f1486,f62])).

fof(f1486,plain,(
    ! [X0] :
      ( k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k1_setfam_1(k2_enumset1(X0,X0,X0,k9_relat_1(sK1,k1_relat_1(sK1))))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f108,f63])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k2_enumset1(X0,X0,X0,k9_relat_1(X1,k1_relat_1(X1))))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f85,f102])).

fof(f102,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f77,f101])).

fof(f101,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f76,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f85,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f105,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f78,f102])).

fof(f78,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f1699,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | ~ r1_tarski(X0,k1_relat_1(sK1))
      | r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f1698,f62])).

fof(f1698,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(sK1))
      | ~ r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f1697,f65])).

fof(f65,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f1697,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(sK1)
      | ~ r1_tarski(X0,k1_relat_1(sK1))
      | ~ r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f99,f63])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

fof(f3250,plain,(
    ! [X14] : r1_tarski(k10_relat_1(k6_relat_1(k2_relat_1(sK1)),X14),X14) ),
    inference(superposition,[],[f112,f3222])).

fof(f3222,plain,(
    ! [X80] : k10_relat_1(k6_relat_1(k2_relat_1(sK1)),X80) = k10_relat_1(k6_relat_1(X80),k2_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f3221,f72])).

fof(f3221,plain,(
    ! [X80] : k10_relat_1(k6_relat_1(X80),k1_relat_1(k6_relat_1(k2_relat_1(sK1)))) = k10_relat_1(k6_relat_1(k2_relat_1(sK1)),X80) ),
    inference(forward_demodulation,[],[f3220,f1672])).

fof(f1672,plain,(
    ! [X2] : k10_relat_1(k6_relat_1(k2_relat_1(sK1)),X2) = k1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK1)),k6_relat_1(X2))) ),
    inference(backward_demodulation,[],[f1560,f1658])).

fof(f3220,plain,(
    ! [X80] : k10_relat_1(k6_relat_1(X80),k1_relat_1(k6_relat_1(k2_relat_1(sK1)))) = k1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK1)),k6_relat_1(X80))) ),
    inference(subsumption_resolution,[],[f3219,f70])).

fof(f3219,plain,(
    ! [X80] :
      ( k10_relat_1(k6_relat_1(X80),k1_relat_1(k6_relat_1(k2_relat_1(sK1)))) = k1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK1)),k6_relat_1(X80)))
      | ~ v1_relat_1(k6_relat_1(X80)) ) ),
    inference(subsumption_resolution,[],[f3215,f70])).

fof(f3215,plain,(
    ! [X80] :
      ( k10_relat_1(k6_relat_1(X80),k1_relat_1(k6_relat_1(k2_relat_1(sK1)))) = k1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK1)),k6_relat_1(X80)))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(sK1)))
      | ~ v1_relat_1(k6_relat_1(X80)) ) ),
    inference(superposition,[],[f74,f2934])).

fof(f2934,plain,(
    ! [X1] : k5_relat_1(k6_relat_1(k2_relat_1(sK1)),k6_relat_1(X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(k2_relat_1(sK1))) ),
    inference(superposition,[],[f2815,f1671])).

fof(f1671,plain,(
    ! [X0] : k6_relat_1(k10_relat_1(k6_relat_1(k2_relat_1(sK1)),X0)) = k5_relat_1(k6_relat_1(k2_relat_1(sK1)),k6_relat_1(X0)) ),
    inference(backward_demodulation,[],[f1547,f1658])).

fof(f2815,plain,(
    ! [X1] : k6_relat_1(k10_relat_1(k6_relat_1(k2_relat_1(sK1)),X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(k2_relat_1(sK1))) ),
    inference(superposition,[],[f544,f1670])).

fof(f1670,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(k2_relat_1(sK1)),X0) = k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK1))) ),
    inference(backward_demodulation,[],[f1488,f1658])).

fof(f544,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
    inference(superposition,[],[f105,f104])).

fof(f104,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f75,f101,f101])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f112,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(subsumption_resolution,[],[f111,f70])).

fof(f111,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f81,f72])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 17:52:06 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.53  % (7856)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (7855)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (7851)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (7850)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (7877)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (7854)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (7870)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (7868)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (7867)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (7858)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (7861)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (7852)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (7865)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (7859)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (7849)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (7853)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (7869)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (7847)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (7848)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (7860)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (7875)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (7866)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (7857)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (7864)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (7873)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.57  % (7872)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.57  % (7874)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.57  % (7862)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.55/0.58  % (7871)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.55/0.58  % (7863)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 2.54/0.76  % (7850)Refutation found. Thanks to Tanya!
% 2.54/0.76  % SZS status Theorem for theBenchmark
% 3.04/0.78  % SZS output start Proof for theBenchmark
% 3.04/0.78  fof(f3334,plain,(
% 3.04/0.78    $false),
% 3.04/0.78    inference(resolution,[],[f3263,f336])).
% 3.04/0.78  fof(f336,plain,(
% 3.04/0.78    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 3.04/0.78    inference(subsumption_resolution,[],[f335,f66])).
% 3.04/0.78  fof(f66,plain,(
% 3.04/0.78    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 3.04/0.78    inference(cnf_transformation,[],[f49])).
% 3.04/0.78  fof(f49,plain,(
% 3.04/0.78    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 3.04/0.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f48])).
% 3.04/0.78  fof(f48,plain,(
% 3.04/0.78    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 3.04/0.78    introduced(choice_axiom,[])).
% 3.04/0.78  fof(f29,plain,(
% 3.04/0.78    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.04/0.78    inference(flattening,[],[f28])).
% 3.04/0.78  fof(f28,plain,(
% 3.04/0.78    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 3.04/0.78    inference(ennf_transformation,[],[f26])).
% 3.04/0.78  fof(f26,negated_conjecture,(
% 3.04/0.78    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 3.04/0.78    inference(negated_conjecture,[],[f25])).
% 3.04/0.78  fof(f25,conjecture,(
% 3.04/0.78    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 3.04/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 3.04/0.78  fof(f335,plain,(
% 3.04/0.78    sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0)) | ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 3.04/0.78    inference(resolution,[],[f332,f89])).
% 3.04/0.78  fof(f89,plain,(
% 3.04/0.78    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.04/0.78    inference(cnf_transformation,[],[f53])).
% 3.04/0.78  fof(f53,plain,(
% 3.04/0.78    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.04/0.78    inference(flattening,[],[f52])).
% 3.04/0.78  fof(f52,plain,(
% 3.04/0.78    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.04/0.78    inference(nnf_transformation,[],[f3])).
% 3.04/0.78  fof(f3,axiom,(
% 3.04/0.78    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.04/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.04/0.78  fof(f332,plain,(
% 3.04/0.78    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 3.04/0.78    inference(resolution,[],[f323,f64])).
% 3.04/0.78  fof(f64,plain,(
% 3.04/0.78    r1_tarski(sK0,k1_relat_1(sK1))),
% 3.04/0.78    inference(cnf_transformation,[],[f49])).
% 3.04/0.78  fof(f323,plain,(
% 3.04/0.78    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))) )),
% 3.04/0.78    inference(resolution,[],[f83,f62])).
% 3.04/0.78  fof(f62,plain,(
% 3.04/0.78    v1_relat_1(sK1)),
% 3.04/0.78    inference(cnf_transformation,[],[f49])).
% 3.04/0.78  fof(f83,plain,(
% 3.04/0.78    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 3.04/0.78    inference(cnf_transformation,[],[f35])).
% 3.04/0.78  fof(f35,plain,(
% 3.04/0.78    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.04/0.78    inference(flattening,[],[f34])).
% 3.04/0.78  fof(f34,plain,(
% 3.04/0.78    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.04/0.78    inference(ennf_transformation,[],[f20])).
% 3.04/0.78  fof(f20,axiom,(
% 3.04/0.78    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 3.04/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 3.04/0.78  fof(f3263,plain,(
% 3.04/0.78    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) )),
% 3.04/0.78    inference(resolution,[],[f3250,f1865])).
% 3.04/0.78  fof(f1865,plain,(
% 3.04/0.78    ( ! [X4,X5] : (~r1_tarski(k10_relat_1(k6_relat_1(k2_relat_1(sK1)),X4),k9_relat_1(sK1,X5)) | r1_tarski(k10_relat_1(sK1,X4),X5)) )),
% 3.04/0.78    inference(subsumption_resolution,[],[f1858,f425])).
% 3.04/0.78  fof(f425,plain,(
% 3.04/0.78    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 3.04/0.78    inference(backward_demodulation,[],[f169,f395])).
% 3.04/0.78  fof(f395,plain,(
% 3.04/0.78    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 3.04/0.78    inference(subsumption_resolution,[],[f374,f109])).
% 3.04/0.78  fof(f109,plain,(
% 3.04/0.78    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.04/0.78    inference(equality_resolution,[],[f88])).
% 3.04/0.78  fof(f88,plain,(
% 3.04/0.78    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.04/0.78    inference(cnf_transformation,[],[f53])).
% 3.04/0.78  fof(f374,plain,(
% 3.04/0.78    ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) | k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 3.04/0.78    inference(superposition,[],[f182,f366])).
% 3.04/0.78  fof(f366,plain,(
% 3.04/0.78    k1_relat_1(sK1) = k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1)))),
% 3.04/0.78    inference(global_subsumption,[],[f339])).
% 3.04/0.78  fof(f339,plain,(
% 3.04/0.78    k1_relat_1(sK1) = k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1)))),
% 3.04/0.78    inference(resolution,[],[f326,f265])).
% 3.04/0.78  fof(f265,plain,(
% 3.04/0.78    ( ! [X6] : (~r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,X6)) | k1_relat_1(sK1) = k10_relat_1(sK1,X6)) )),
% 3.04/0.78    inference(subsumption_resolution,[],[f263,f89])).
% 3.04/0.78  fof(f263,plain,(
% 3.04/0.78    ( ! [X6] : (r1_tarski(k10_relat_1(sK1,X6),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,X6)) | k1_relat_1(sK1) = k10_relat_1(sK1,X6)) )),
% 3.04/0.78    inference(resolution,[],[f259,f114])).
% 3.04/0.78  fof(f114,plain,(
% 3.04/0.78    ( ! [X2,X1] : (~r2_hidden(sK3(X2,X1),X1) | ~r1_tarski(X1,X2) | X1 = X2) )),
% 3.04/0.78    inference(resolution,[],[f89,f92])).
% 3.04/0.78  fof(f92,plain,(
% 3.04/0.78    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 3.04/0.78    inference(cnf_transformation,[],[f57])).
% 3.04/0.78  fof(f57,plain,(
% 3.04/0.78    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.04/0.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f55,f56])).
% 3.04/0.78  fof(f56,plain,(
% 3.04/0.78    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 3.04/0.78    introduced(choice_axiom,[])).
% 3.04/0.78  fof(f55,plain,(
% 3.04/0.78    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.04/0.78    inference(rectify,[],[f54])).
% 3.04/0.78  fof(f54,plain,(
% 3.04/0.78    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.04/0.78    inference(nnf_transformation,[],[f41])).
% 3.04/0.78  fof(f41,plain,(
% 3.04/0.78    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.04/0.78    inference(ennf_transformation,[],[f1])).
% 3.04/0.78  fof(f1,axiom,(
% 3.04/0.78    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.04/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 3.04/0.78  fof(f259,plain,(
% 3.04/0.78    ( ! [X0,X1] : (r2_hidden(sK3(k10_relat_1(sK1,X0),X1),k1_relat_1(sK1)) | r1_tarski(k10_relat_1(sK1,X0),X1)) )),
% 3.04/0.78    inference(subsumption_resolution,[],[f254,f62])).
% 3.04/0.78  fof(f254,plain,(
% 3.04/0.78    ( ! [X0,X1] : (r2_hidden(sK3(k10_relat_1(sK1,X0),X1),k1_relat_1(sK1)) | r1_tarski(k10_relat_1(sK1,X0),X1) | ~v1_relat_1(sK1)) )),
% 3.04/0.78    inference(resolution,[],[f249,f81])).
% 3.04/0.78  fof(f81,plain,(
% 3.04/0.78    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.04/0.78    inference(cnf_transformation,[],[f32])).
% 3.04/0.78  fof(f32,plain,(
% 3.04/0.78    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.04/0.78    inference(ennf_transformation,[],[f14])).
% 3.04/0.78  fof(f14,axiom,(
% 3.04/0.78    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 3.04/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 3.04/0.78  fof(f249,plain,(
% 3.04/0.78    ( ! [X8,X7,X9] : (~r1_tarski(k10_relat_1(sK1,k2_relat_1(sK1)),X9) | r2_hidden(sK3(k10_relat_1(sK1,X7),X8),X9) | r1_tarski(k10_relat_1(sK1,X7),X8)) )),
% 3.04/0.78    inference(resolution,[],[f236,f90])).
% 3.04/0.78  fof(f90,plain,(
% 3.04/0.78    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 3.04/0.78    inference(cnf_transformation,[],[f57])).
% 3.04/0.78  fof(f236,plain,(
% 3.04/0.78    ( ! [X21,X20] : (r2_hidden(sK3(k10_relat_1(sK1,X20),X21),k10_relat_1(sK1,k2_relat_1(sK1))) | r1_tarski(k10_relat_1(sK1,X20),X21)) )),
% 3.04/0.78    inference(resolution,[],[f136,f169])).
% 3.04/0.78  fof(f136,plain,(
% 3.04/0.78    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | r2_hidden(sK3(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 3.04/0.78    inference(resolution,[],[f90,f91])).
% 3.04/0.78  fof(f91,plain,(
% 3.04/0.78    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 3.04/0.78    inference(cnf_transformation,[],[f57])).
% 3.04/0.78  fof(f326,plain,(
% 3.04/0.78    r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1))))),
% 3.04/0.78    inference(resolution,[],[f323,f109])).
% 3.04/0.78  fof(f182,plain,(
% 3.04/0.78    ( ! [X0] : (~r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,X0)) | k10_relat_1(sK1,X0) = k10_relat_1(sK1,k2_relat_1(sK1))) )),
% 3.04/0.78    inference(subsumption_resolution,[],[f177,f62])).
% 3.04/0.78  fof(f177,plain,(
% 3.04/0.78    ( ! [X0] : (~r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,X0)) | k10_relat_1(sK1,X0) = k10_relat_1(sK1,k2_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 3.04/0.78    inference(resolution,[],[f175,f81])).
% 3.04/0.78  fof(f175,plain,(
% 3.04/0.78    ( ! [X0,X1] : (~r1_tarski(k10_relat_1(sK1,k2_relat_1(sK1)),X1) | ~r1_tarski(X1,k10_relat_1(sK1,X0)) | k10_relat_1(sK1,X0) = k10_relat_1(sK1,k2_relat_1(sK1))) )),
% 3.04/0.78    inference(resolution,[],[f172,f100])).
% 3.04/0.78  fof(f100,plain,(
% 3.04/0.78    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.04/0.78    inference(cnf_transformation,[],[f47])).
% 3.04/0.78  fof(f47,plain,(
% 3.04/0.78    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.04/0.78    inference(flattening,[],[f46])).
% 3.04/0.78  fof(f46,plain,(
% 3.04/0.78    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.04/0.78    inference(ennf_transformation,[],[f5])).
% 3.04/0.78  fof(f5,axiom,(
% 3.04/0.78    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.04/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 3.04/0.78  fof(f172,plain,(
% 3.04/0.78    ( ! [X0] : (~r1_tarski(k10_relat_1(sK1,k2_relat_1(sK1)),k10_relat_1(sK1,X0)) | k10_relat_1(sK1,X0) = k10_relat_1(sK1,k2_relat_1(sK1))) )),
% 3.04/0.78    inference(resolution,[],[f169,f89])).
% 3.04/0.78  fof(f169,plain,(
% 3.04/0.78    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,k2_relat_1(sK1)))) )),
% 3.04/0.78    inference(resolution,[],[f82,f62])).
% 3.04/0.78  fof(f82,plain,(
% 3.04/0.78    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))) )),
% 3.04/0.78    inference(cnf_transformation,[],[f33])).
% 3.04/0.78  fof(f33,plain,(
% 3.04/0.78    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.04/0.78    inference(ennf_transformation,[],[f15])).
% 3.04/0.78  fof(f15,axiom,(
% 3.04/0.78    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))))),
% 3.04/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).
% 3.04/0.78  fof(f1858,plain,(
% 3.04/0.78    ( ! [X4,X5] : (~r1_tarski(k10_relat_1(k6_relat_1(k2_relat_1(sK1)),X4),k9_relat_1(sK1,X5)) | ~r1_tarski(k10_relat_1(sK1,X4),k1_relat_1(sK1)) | r1_tarski(k10_relat_1(sK1,X4),X5)) )),
% 3.04/0.78    inference(superposition,[],[f1699,f1658])).
% 3.04/0.78  fof(f1658,plain,(
% 3.04/0.78    ( ! [X1] : (k9_relat_1(sK1,k10_relat_1(sK1,X1)) = k10_relat_1(k6_relat_1(k2_relat_1(sK1)),X1)) )),
% 3.04/0.78    inference(forward_demodulation,[],[f1657,f72])).
% 3.04/0.78  fof(f72,plain,(
% 3.04/0.78    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.04/0.78    inference(cnf_transformation,[],[f18])).
% 3.04/0.78  fof(f18,axiom,(
% 3.04/0.78    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.04/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 3.04/0.78  fof(f1657,plain,(
% 3.04/0.78    ( ! [X1] : (k9_relat_1(sK1,k10_relat_1(sK1,X1)) = k10_relat_1(k6_relat_1(k2_relat_1(sK1)),k1_relat_1(k6_relat_1(X1)))) )),
% 3.04/0.78    inference(subsumption_resolution,[],[f1656,f70])).
% 3.04/0.78  fof(f70,plain,(
% 3.04/0.78    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.04/0.78    inference(cnf_transformation,[],[f19])).
% 3.04/0.78  fof(f19,axiom,(
% 3.04/0.78    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.04/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 3.04/0.78  fof(f1656,plain,(
% 3.04/0.78    ( ! [X1] : (k9_relat_1(sK1,k10_relat_1(sK1,X1)) = k10_relat_1(k6_relat_1(k2_relat_1(sK1)),k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(k2_relat_1(sK1)))) )),
% 3.04/0.78    inference(subsumption_resolution,[],[f1649,f70])).
% 3.04/0.78  fof(f1649,plain,(
% 3.04/0.78    ( ! [X1] : (k9_relat_1(sK1,k10_relat_1(sK1,X1)) = k10_relat_1(k6_relat_1(k2_relat_1(sK1)),k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(k2_relat_1(sK1)))) )),
% 3.04/0.78    inference(superposition,[],[f1560,f74])).
% 3.04/0.78  fof(f74,plain,(
% 3.04/0.78    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.04/0.78    inference(cnf_transformation,[],[f30])).
% 3.04/0.78  fof(f30,plain,(
% 3.04/0.78    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.04/0.78    inference(ennf_transformation,[],[f17])).
% 3.04/0.78  fof(f17,axiom,(
% 3.04/0.78    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 3.04/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 3.04/0.78  fof(f1560,plain,(
% 3.04/0.78    ( ! [X2] : (k9_relat_1(sK1,k10_relat_1(sK1,X2)) = k1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK1)),k6_relat_1(X2)))) )),
% 3.04/0.78    inference(superposition,[],[f72,f1547])).
% 3.04/0.78  fof(f1547,plain,(
% 3.04/0.78    ( ! [X0] : (k5_relat_1(k6_relat_1(k2_relat_1(sK1)),k6_relat_1(X0)) = k6_relat_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)))) )),
% 3.04/0.78    inference(superposition,[],[f105,f1488])).
% 3.04/0.78  fof(f1488,plain,(
% 3.04/0.78    ( ! [X0] : (k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK1)))) )),
% 3.04/0.78    inference(forward_demodulation,[],[f1487,f825])).
% 3.04/0.78  fof(f825,plain,(
% 3.04/0.78    k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1)),
% 3.04/0.78    inference(forward_demodulation,[],[f820,f395])).
% 3.04/0.78  fof(f820,plain,(
% 3.04/0.78    k2_relat_1(sK1) = k9_relat_1(sK1,k10_relat_1(sK1,k2_relat_1(sK1)))),
% 3.04/0.78    inference(resolution,[],[f819,f109])).
% 3.04/0.78  fof(f819,plain,(
% 3.04/0.78    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK1)) | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0) )),
% 3.04/0.78    inference(subsumption_resolution,[],[f818,f62])).
% 3.04/0.78  fof(f818,plain,(
% 3.04/0.78    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK1)) | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0 | ~v1_relat_1(sK1)) )),
% 3.04/0.78    inference(resolution,[],[f86,f63])).
% 3.04/0.78  fof(f63,plain,(
% 3.04/0.78    v1_funct_1(sK1)),
% 3.04/0.78    inference(cnf_transformation,[],[f49])).
% 3.04/0.78  fof(f86,plain,(
% 3.04/0.78    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 3.04/0.78    inference(cnf_transformation,[],[f40])).
% 3.04/0.78  fof(f40,plain,(
% 3.04/0.78    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.04/0.78    inference(flattening,[],[f39])).
% 3.04/0.78  fof(f39,plain,(
% 3.04/0.78    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.04/0.78    inference(ennf_transformation,[],[f21])).
% 3.04/0.78  fof(f21,axiom,(
% 3.04/0.78    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 3.04/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 3.04/0.78  fof(f1487,plain,(
% 3.04/0.78    ( ! [X0] : (k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k1_setfam_1(k2_enumset1(X0,X0,X0,k9_relat_1(sK1,k1_relat_1(sK1))))) )),
% 3.04/0.78    inference(subsumption_resolution,[],[f1486,f62])).
% 3.04/0.78  fof(f1486,plain,(
% 3.04/0.78    ( ! [X0] : (k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k1_setfam_1(k2_enumset1(X0,X0,X0,k9_relat_1(sK1,k1_relat_1(sK1)))) | ~v1_relat_1(sK1)) )),
% 3.04/0.78    inference(resolution,[],[f108,f63])).
% 3.04/0.78  fof(f108,plain,(
% 3.04/0.78    ( ! [X0,X1] : (~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k2_enumset1(X0,X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) | ~v1_relat_1(X1)) )),
% 3.04/0.78    inference(definition_unfolding,[],[f85,f102])).
% 3.04/0.78  fof(f102,plain,(
% 3.04/0.78    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 3.04/0.78    inference(definition_unfolding,[],[f77,f101])).
% 3.04/0.78  fof(f101,plain,(
% 3.04/0.78    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.04/0.78    inference(definition_unfolding,[],[f76,f93])).
% 3.04/0.78  fof(f93,plain,(
% 3.04/0.78    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.04/0.78    inference(cnf_transformation,[],[f11])).
% 3.04/0.78  fof(f11,axiom,(
% 3.04/0.78    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.04/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 3.04/0.78  fof(f76,plain,(
% 3.04/0.78    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.04/0.78    inference(cnf_transformation,[],[f10])).
% 3.04/0.78  fof(f10,axiom,(
% 3.04/0.78    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.04/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 3.04/0.78  fof(f77,plain,(
% 3.04/0.78    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.04/0.78    inference(cnf_transformation,[],[f12])).
% 3.04/0.78  fof(f12,axiom,(
% 3.04/0.78    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.04/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 3.04/0.78  fof(f85,plain,(
% 3.04/0.78    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.04/0.78    inference(cnf_transformation,[],[f38])).
% 3.04/0.78  fof(f38,plain,(
% 3.04/0.78    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.04/0.78    inference(flattening,[],[f37])).
% 3.04/0.78  fof(f37,plain,(
% 3.04/0.78    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.04/0.78    inference(ennf_transformation,[],[f22])).
% 3.04/0.78  fof(f22,axiom,(
% 3.04/0.78    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 3.04/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 3.04/0.78  fof(f105,plain,(
% 3.04/0.78    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 3.04/0.78    inference(definition_unfolding,[],[f78,f102])).
% 3.04/0.78  fof(f78,plain,(
% 3.04/0.78    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 3.04/0.78    inference(cnf_transformation,[],[f24])).
% 3.04/0.78  fof(f24,axiom,(
% 3.04/0.78    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.04/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 3.04/0.78  fof(f1699,plain,(
% 3.04/0.78    ( ! [X0,X1] : (~r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~r1_tarski(X0,k1_relat_1(sK1)) | r1_tarski(X0,X1)) )),
% 3.04/0.78    inference(subsumption_resolution,[],[f1698,f62])).
% 3.04/0.78  fof(f1698,plain,(
% 3.04/0.78    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(sK1)) | ~r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | r1_tarski(X0,X1) | ~v1_relat_1(sK1)) )),
% 3.04/0.78    inference(subsumption_resolution,[],[f1697,f65])).
% 3.04/0.78  fof(f65,plain,(
% 3.04/0.78    v2_funct_1(sK1)),
% 3.04/0.78    inference(cnf_transformation,[],[f49])).
% 3.04/0.78  fof(f1697,plain,(
% 3.04/0.78    ( ! [X0,X1] : (~v2_funct_1(sK1) | ~r1_tarski(X0,k1_relat_1(sK1)) | ~r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | r1_tarski(X0,X1) | ~v1_relat_1(sK1)) )),
% 3.04/0.78    inference(resolution,[],[f99,f63])).
% 3.04/0.78  fof(f99,plain,(
% 3.04/0.78    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 3.04/0.78    inference(cnf_transformation,[],[f45])).
% 3.04/0.78  fof(f45,plain,(
% 3.04/0.78    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.04/0.78    inference(flattening,[],[f44])).
% 3.04/0.78  fof(f44,plain,(
% 3.04/0.78    ! [X0,X1,X2] : ((r1_tarski(X0,X1) | (~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.04/0.78    inference(ennf_transformation,[],[f23])).
% 3.04/0.78  fof(f23,axiom,(
% 3.04/0.78    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 3.04/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).
% 3.04/0.78  fof(f3250,plain,(
% 3.04/0.78    ( ! [X14] : (r1_tarski(k10_relat_1(k6_relat_1(k2_relat_1(sK1)),X14),X14)) )),
% 3.04/0.78    inference(superposition,[],[f112,f3222])).
% 3.04/0.78  fof(f3222,plain,(
% 3.04/0.78    ( ! [X80] : (k10_relat_1(k6_relat_1(k2_relat_1(sK1)),X80) = k10_relat_1(k6_relat_1(X80),k2_relat_1(sK1))) )),
% 3.04/0.78    inference(forward_demodulation,[],[f3221,f72])).
% 3.04/0.78  fof(f3221,plain,(
% 3.04/0.78    ( ! [X80] : (k10_relat_1(k6_relat_1(X80),k1_relat_1(k6_relat_1(k2_relat_1(sK1)))) = k10_relat_1(k6_relat_1(k2_relat_1(sK1)),X80)) )),
% 3.04/0.78    inference(forward_demodulation,[],[f3220,f1672])).
% 3.04/0.78  fof(f1672,plain,(
% 3.04/0.78    ( ! [X2] : (k10_relat_1(k6_relat_1(k2_relat_1(sK1)),X2) = k1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK1)),k6_relat_1(X2)))) )),
% 3.04/0.78    inference(backward_demodulation,[],[f1560,f1658])).
% 3.04/0.78  fof(f3220,plain,(
% 3.04/0.78    ( ! [X80] : (k10_relat_1(k6_relat_1(X80),k1_relat_1(k6_relat_1(k2_relat_1(sK1)))) = k1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK1)),k6_relat_1(X80)))) )),
% 3.04/0.78    inference(subsumption_resolution,[],[f3219,f70])).
% 3.04/0.78  fof(f3219,plain,(
% 3.04/0.78    ( ! [X80] : (k10_relat_1(k6_relat_1(X80),k1_relat_1(k6_relat_1(k2_relat_1(sK1)))) = k1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK1)),k6_relat_1(X80))) | ~v1_relat_1(k6_relat_1(X80))) )),
% 3.04/0.78    inference(subsumption_resolution,[],[f3215,f70])).
% 3.04/0.78  fof(f3215,plain,(
% 3.04/0.78    ( ! [X80] : (k10_relat_1(k6_relat_1(X80),k1_relat_1(k6_relat_1(k2_relat_1(sK1)))) = k1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK1)),k6_relat_1(X80))) | ~v1_relat_1(k6_relat_1(k2_relat_1(sK1))) | ~v1_relat_1(k6_relat_1(X80))) )),
% 3.04/0.78    inference(superposition,[],[f74,f2934])).
% 3.04/0.78  fof(f2934,plain,(
% 3.04/0.78    ( ! [X1] : (k5_relat_1(k6_relat_1(k2_relat_1(sK1)),k6_relat_1(X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(k2_relat_1(sK1)))) )),
% 3.04/0.78    inference(superposition,[],[f2815,f1671])).
% 3.04/0.78  fof(f1671,plain,(
% 3.04/0.78    ( ! [X0] : (k6_relat_1(k10_relat_1(k6_relat_1(k2_relat_1(sK1)),X0)) = k5_relat_1(k6_relat_1(k2_relat_1(sK1)),k6_relat_1(X0))) )),
% 3.04/0.78    inference(backward_demodulation,[],[f1547,f1658])).
% 3.04/0.78  fof(f2815,plain,(
% 3.04/0.78    ( ! [X1] : (k6_relat_1(k10_relat_1(k6_relat_1(k2_relat_1(sK1)),X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(k2_relat_1(sK1)))) )),
% 3.04/0.78    inference(superposition,[],[f544,f1670])).
% 3.04/0.78  fof(f1670,plain,(
% 3.04/0.78    ( ! [X0] : (k10_relat_1(k6_relat_1(k2_relat_1(sK1)),X0) = k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK1)))) )),
% 3.04/0.78    inference(backward_demodulation,[],[f1488,f1658])).
% 3.04/0.78  fof(f544,plain,(
% 3.04/0.78    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))) )),
% 3.04/0.78    inference(superposition,[],[f105,f104])).
% 3.04/0.78  fof(f104,plain,(
% 3.04/0.78    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 3.04/0.78    inference(definition_unfolding,[],[f75,f101,f101])).
% 3.04/0.78  fof(f75,plain,(
% 3.04/0.78    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.04/0.78    inference(cnf_transformation,[],[f9])).
% 3.04/0.78  fof(f9,axiom,(
% 3.04/0.78    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.04/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 3.04/0.78  fof(f112,plain,(
% 3.04/0.78    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 3.04/0.78    inference(subsumption_resolution,[],[f111,f70])).
% 3.04/0.78  fof(f111,plain,(
% 3.04/0.78    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 3.04/0.78    inference(superposition,[],[f81,f72])).
% 3.04/0.78  % SZS output end Proof for theBenchmark
% 3.04/0.78  % (7850)------------------------------
% 3.04/0.78  % (7850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.04/0.78  % (7850)Termination reason: Refutation
% 3.04/0.78  
% 3.04/0.78  % (7850)Memory used [KB]: 13304
% 3.04/0.78  % (7850)Time elapsed: 0.309 s
% 3.04/0.78  % (7850)------------------------------
% 3.04/0.78  % (7850)------------------------------
% 3.04/0.78  % (7841)Success in time 0.408 s
%------------------------------------------------------------------------------
