%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:56 EST 2020

% Result     : Theorem 17.73s
% Output     : Refutation 17.73s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 367 expanded)
%              Number of leaves         :   15 (  92 expanded)
%              Depth                    :   19
%              Number of atoms          :  311 (1236 expanded)
%              Number of equality atoms :   61 ( 342 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28865,plain,(
    $false ),
    inference(subsumption_resolution,[],[f28864,f103])).

fof(f103,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f80,f93])).

fof(f93,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0) ),
    inference(unit_resulting_resolution,[],[f88,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f75,f61])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f80,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f59,f61])).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f28864,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f28863,f6854])).

fof(f6854,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f6837,f93])).

fof(f6837,plain,(
    ! [X2] : k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,X2)) ),
    inference(superposition,[],[f2237,f93])).

fof(f2237,plain,(
    ! [X0,X1] : k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) ),
    inference(unit_resulting_resolution,[],[f48,f49,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(f49,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0))
    & r1_tarski(sK0,k2_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f34])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
        & r1_tarski(X0,k2_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0))
      & r1_tarski(sK0,k2_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(X0,k2_relat_1(X1))
         => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f48,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f28863,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f28855,f93])).

fof(f28855,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k6_subset_1(sK0,sK0)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f5040,f28847])).

fof(f28847,plain,(
    ! [X21,X20] : k10_relat_1(sK1,k6_subset_1(X21,k9_relat_1(sK1,k10_relat_1(sK1,X20)))) = k10_relat_1(sK1,k6_subset_1(X21,X20)) ),
    inference(forward_demodulation,[],[f28682,f2237])).

fof(f28682,plain,(
    ! [X21,X20] : k10_relat_1(sK1,k6_subset_1(X21,k9_relat_1(sK1,k10_relat_1(sK1,X20)))) = k6_subset_1(k10_relat_1(sK1,X21),k10_relat_1(sK1,X20)) ),
    inference(superposition,[],[f2237,f27968])).

fof(f27968,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f48,f21484,f23371,f1420])).

fof(f1420,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(k10_relat_1(X6,k9_relat_1(X6,X5)),X5)
      | ~ v1_relat_1(X6)
      | k10_relat_1(X6,k9_relat_1(X6,X5)) = X5
      | ~ r1_tarski(X5,k1_relat_1(X6)) ) ),
    inference(resolution,[],[f65,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f23371,plain,(
    ! [X42] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X42))),k10_relat_1(sK1,X42)) ),
    inference(subsumption_resolution,[],[f23350,f6854])).

fof(f23350,plain,(
    ! [X42] :
      ( k1_xboole_0 != k10_relat_1(sK1,k1_xboole_0)
      | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X42))),k10_relat_1(sK1,X42)) ) ),
    inference(superposition,[],[f6841,f447])).

fof(f447,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f413,f83])).

fof(f413,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f48,f49,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f6841,plain,(
    ! [X6,X5] :
      ( k1_xboole_0 != k10_relat_1(sK1,k6_subset_1(X5,X6))
      | r1_tarski(k10_relat_1(sK1,X5),k10_relat_1(sK1,X6)) ) ),
    inference(superposition,[],[f84,f2237])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f74,f61])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f21484,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f49,f48,f12153])).

fof(f12153,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f12150])).

fof(f12150,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
      | r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) ) ),
    inference(resolution,[],[f1650,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f1650,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(k10_relat_1(X0,X1),X2),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(k10_relat_1(X0,X1),X2) ) ),
    inference(resolution,[],[f87,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | r2_hidden(X4,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ~ r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1)
                | ~ r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))
                | ~ r2_hidden(sK2(X0,X1,X2),X2) )
              & ( ( r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1)
                  & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
            | ~ r2_hidden(X3,k1_relat_1(X0))
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
              & r2_hidden(X3,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1)
            & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

fof(f5040,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f103,f1896,f70])).

fof(f1896,plain,(
    k1_xboole_0 != k10_relat_1(sK1,k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))) ),
    inference(unit_resulting_resolution,[],[f48,f477,f282,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

fof(f282,plain,(
    ! [X0] : r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f80,f50,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f50,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f477,plain,(
    k1_xboole_0 != k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f446,f84])).

fof(f446,plain,(
    ~ r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f51,f413,f70])).

fof(f51,plain,(
    sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:28:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (6849)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (6829)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (6838)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (6825)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (6827)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (6839)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (6822)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (6842)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (6826)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (6833)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (6830)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (6836)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (6837)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (6854)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (6847)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (6828)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (6841)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (6834)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (6824)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (6831)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (6843)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (6844)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (6846)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (6845)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (6848)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (6832)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (6840)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (6850)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (6852)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (6853)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 3.27/0.84  % (6828)Time limit reached!
% 3.27/0.84  % (6828)------------------------------
% 3.27/0.84  % (6828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.27/0.84  % (6828)Termination reason: Time limit
% 3.27/0.84  
% 3.27/0.84  % (6828)Memory used [KB]: 8699
% 3.27/0.84  % (6828)Time elapsed: 0.429 s
% 3.27/0.84  % (6828)------------------------------
% 3.27/0.84  % (6828)------------------------------
% 4.22/0.92  % (6841)Time limit reached!
% 4.22/0.92  % (6841)------------------------------
% 4.22/0.92  % (6841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.22/0.92  % (6841)Termination reason: Time limit
% 4.22/0.92  
% 4.22/0.92  % (6841)Memory used [KB]: 13048
% 4.22/0.92  % (6841)Time elapsed: 0.509 s
% 4.22/0.92  % (6841)------------------------------
% 4.22/0.92  % (6841)------------------------------
% 4.22/0.92  % (6836)Time limit reached!
% 4.22/0.92  % (6836)------------------------------
% 4.22/0.92  % (6836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.22/0.92  % (6836)Termination reason: Time limit
% 4.22/0.92  
% 4.22/0.92  % (6836)Memory used [KB]: 9594
% 4.22/0.92  % (6836)Time elapsed: 0.521 s
% 4.22/0.92  % (6836)------------------------------
% 4.22/0.92  % (6836)------------------------------
% 4.39/0.93  % (6824)Time limit reached!
% 4.39/0.93  % (6824)------------------------------
% 4.39/0.93  % (6824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.39/0.93  % (6824)Termination reason: Time limit
% 4.39/0.93  % (6824)Termination phase: Saturation
% 4.39/0.93  
% 4.39/0.93  % (6824)Memory used [KB]: 8571
% 4.39/0.93  % (6824)Time elapsed: 0.500 s
% 4.39/0.93  % (6824)------------------------------
% 4.39/0.93  % (6824)------------------------------
% 4.39/0.94  % (6822)Time limit reached!
% 4.39/0.94  % (6822)------------------------------
% 4.39/0.94  % (6822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.39/0.94  % (6822)Termination reason: Time limit
% 4.39/0.94  
% 4.39/0.94  % (6822)Memory used [KB]: 3070
% 4.39/0.94  % (6822)Time elapsed: 0.525 s
% 4.39/0.94  % (6822)------------------------------
% 4.39/0.94  % (6822)------------------------------
% 4.39/0.96  % (7048)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 4.39/1.01  % (6853)Time limit reached!
% 4.39/1.01  % (6853)------------------------------
% 4.39/1.01  % (6853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.39/1.01  % (6853)Termination reason: Time limit
% 4.39/1.01  % (6853)Termination phase: Saturation
% 4.39/1.01  
% 4.39/1.01  % (6853)Memory used [KB]: 9083
% 4.39/1.01  % (6853)Time elapsed: 0.600 s
% 4.39/1.01  % (6853)------------------------------
% 4.39/1.01  % (6853)------------------------------
% 5.01/1.02  % (7054)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 5.01/1.02  % (7055)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 5.01/1.03  % (6840)Time limit reached!
% 5.01/1.03  % (6840)------------------------------
% 5.01/1.03  % (6840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.01/1.03  % (6840)Termination reason: Time limit
% 5.01/1.03  
% 5.01/1.03  % (6840)Memory used [KB]: 16758
% 5.01/1.03  % (6840)Time elapsed: 0.611 s
% 5.01/1.03  % (6840)------------------------------
% 5.01/1.03  % (6840)------------------------------
% 5.01/1.04  % (7056)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.01/1.04  % (6830)Time limit reached!
% 5.01/1.04  % (6830)------------------------------
% 5.01/1.04  % (6830)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.01/1.04  % (6830)Termination reason: Time limit
% 5.01/1.04  
% 5.01/1.04  % (6830)Memory used [KB]: 10106
% 5.01/1.04  % (6830)Time elapsed: 0.602 s
% 5.01/1.04  % (6830)------------------------------
% 5.01/1.04  % (6830)------------------------------
% 5.01/1.06  % (7057)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.41/1.13  % (7058)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.41/1.14  % (7059)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.41/1.16  % (7060)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.41/1.17  % (6833)Time limit reached!
% 5.41/1.17  % (6833)------------------------------
% 5.41/1.17  % (6833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.41/1.17  % (6833)Termination reason: Time limit
% 5.41/1.17  
% 5.41/1.17  % (6833)Memory used [KB]: 22131
% 5.41/1.17  % (6833)Time elapsed: 0.763 s
% 5.41/1.17  % (6833)------------------------------
% 5.41/1.17  % (6833)------------------------------
% 6.47/1.21  % (6845)Time limit reached!
% 6.47/1.21  % (6845)------------------------------
% 6.47/1.21  % (6845)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.47/1.21  % (6845)Termination reason: Time limit
% 6.47/1.21  % (6845)Termination phase: Saturation
% 6.47/1.21  
% 6.47/1.21  % (6845)Memory used [KB]: 6012
% 6.47/1.21  % (6845)Time elapsed: 0.800 s
% 6.47/1.21  % (6845)------------------------------
% 6.47/1.21  % (6845)------------------------------
% 6.82/1.27  % (7061)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 7.40/1.32  % (7062)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 7.87/1.40  % (7056)Time limit reached!
% 7.87/1.40  % (7056)------------------------------
% 7.87/1.40  % (7056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.87/1.40  % (7056)Termination reason: Time limit
% 7.87/1.40  
% 7.87/1.40  % (7056)Memory used [KB]: 8059
% 7.87/1.40  % (7056)Time elapsed: 0.418 s
% 7.87/1.40  % (7056)------------------------------
% 7.87/1.40  % (7056)------------------------------
% 7.87/1.42  % (6825)Time limit reached!
% 7.87/1.42  % (6825)------------------------------
% 7.87/1.42  % (6825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.87/1.42  % (6825)Termination reason: Time limit
% 7.87/1.42  % (6825)Termination phase: Saturation
% 7.87/1.42  
% 7.87/1.42  % (6825)Memory used [KB]: 21875
% 7.87/1.42  % (6825)Time elapsed: 1.0000 s
% 7.87/1.42  % (6825)------------------------------
% 7.87/1.42  % (6825)------------------------------
% 8.99/1.54  % (7063)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 8.99/1.55  % (7064)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 9.55/1.65  % (6850)Time limit reached!
% 9.55/1.65  % (6850)------------------------------
% 9.55/1.65  % (6850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.55/1.65  % (6850)Termination reason: Time limit
% 9.55/1.65  
% 9.55/1.65  % (6850)Memory used [KB]: 20724
% 9.55/1.65  % (6850)Time elapsed: 1.225 s
% 9.55/1.65  % (6850)------------------------------
% 9.55/1.65  % (6850)------------------------------
% 10.44/1.73  % (6848)Time limit reached!
% 10.44/1.73  % (6848)------------------------------
% 10.44/1.73  % (6848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.44/1.73  % (6848)Termination reason: Time limit
% 10.44/1.73  
% 10.44/1.73  % (6848)Memory used [KB]: 14967
% 10.44/1.73  % (6848)Time elapsed: 1.329 s
% 10.44/1.73  % (6848)------------------------------
% 10.44/1.73  % (6848)------------------------------
% 10.44/1.75  % (6839)Time limit reached!
% 10.44/1.75  % (6839)------------------------------
% 10.44/1.75  % (6839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.44/1.75  % (6839)Termination reason: Time limit
% 10.44/1.75  % (6839)Termination phase: Saturation
% 10.44/1.75  
% 10.44/1.75  % (6839)Memory used [KB]: 12537
% 10.44/1.75  % (6839)Time elapsed: 1.300 s
% 10.44/1.75  % (6839)------------------------------
% 10.44/1.75  % (6839)------------------------------
% 10.44/1.77  % (7065)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 11.52/1.87  % (7066)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 11.52/1.90  % (7067)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 12.28/1.94  % (6827)Time limit reached!
% 12.28/1.94  % (6827)------------------------------
% 12.28/1.94  % (6827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.28/1.94  % (6852)Time limit reached!
% 12.28/1.94  % (6852)------------------------------
% 12.28/1.94  % (6852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.28/1.94  % (6852)Termination reason: Time limit
% 12.28/1.94  
% 12.28/1.94  % (6852)Memory used [KB]: 13176
% 12.28/1.94  % (6852)Time elapsed: 1.539 s
% 12.28/1.94  % (6852)------------------------------
% 12.28/1.94  % (6852)------------------------------
% 12.28/1.94  % (6827)Termination reason: Time limit
% 12.28/1.94  
% 12.28/1.94  % (6827)Memory used [KB]: 17654
% 12.28/1.94  % (6827)Time elapsed: 1.512 s
% 12.28/1.94  % (6827)------------------------------
% 12.28/1.94  % (6827)------------------------------
% 12.81/2.00  % (6846)Time limit reached!
% 12.81/2.00  % (6846)------------------------------
% 12.81/2.00  % (6846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.81/2.01  % (6846)Termination reason: Time limit
% 12.81/2.01  
% 12.81/2.01  % (6846)Memory used [KB]: 29423
% 12.81/2.01  % (6846)Time elapsed: 1.591 s
% 12.81/2.01  % (6846)------------------------------
% 12.81/2.01  % (6846)------------------------------
% 12.81/2.05  % (7057)Time limit reached!
% 12.81/2.05  % (7057)------------------------------
% 12.81/2.05  % (7057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.81/2.05  % (7057)Termination reason: Time limit
% 12.81/2.05  % (7057)Termination phase: Saturation
% 12.81/2.05  
% 12.81/2.05  % (7057)Memory used [KB]: 20084
% 12.81/2.05  % (7057)Time elapsed: 0.400 s
% 12.81/2.05  % (7057)------------------------------
% 12.81/2.05  % (7057)------------------------------
% 12.81/2.07  % (7068)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 13.36/2.08  % (7069)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 13.64/2.13  % (7070)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 13.64/2.18  % (7071)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 13.64/2.20  % (7065)Time limit reached!
% 13.64/2.20  % (7065)------------------------------
% 13.64/2.20  % (7065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.64/2.22  % (7065)Termination reason: Time limit
% 13.64/2.22  
% 13.64/2.22  % (7065)Memory used [KB]: 2814
% 13.64/2.22  % (7065)Time elapsed: 0.531 s
% 13.64/2.22  % (7065)------------------------------
% 13.64/2.22  % (7065)------------------------------
% 14.30/2.24  % (6838)Time limit reached!
% 14.30/2.24  % (6838)------------------------------
% 14.30/2.24  % (6838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.30/2.25  % (6838)Termination reason: Time limit
% 14.30/2.25  % (6838)Termination phase: Saturation
% 14.30/2.25  
% 14.30/2.25  % (6838)Memory used [KB]: 8315
% 14.30/2.25  % (6838)Time elapsed: 1.800 s
% 14.30/2.25  % (6838)------------------------------
% 14.30/2.25  % (6838)------------------------------
% 14.30/2.26  % (6834)Time limit reached!
% 14.30/2.26  % (6834)------------------------------
% 14.30/2.26  % (6834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.30/2.26  % (6834)Termination reason: Time limit
% 14.30/2.26  
% 14.30/2.26  % (6834)Memory used [KB]: 13944
% 14.30/2.26  % (6834)Time elapsed: 1.850 s
% 14.30/2.26  % (6834)------------------------------
% 14.30/2.26  % (6834)------------------------------
% 14.30/2.28  % (7059)Time limit reached!
% 14.30/2.28  % (7059)------------------------------
% 14.30/2.28  % (7059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.30/2.28  % (7059)Termination reason: Time limit
% 14.30/2.28  
% 14.30/2.28  % (7059)Memory used [KB]: 11001
% 14.30/2.28  % (7059)Time elapsed: 1.229 s
% 14.30/2.28  % (7059)------------------------------
% 14.30/2.28  % (7059)------------------------------
% 15.41/2.33  % (7072)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 15.41/2.36  % (7069)Time limit reached!
% 15.41/2.36  % (7069)------------------------------
% 15.41/2.36  % (7069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.41/2.36  % (7069)Termination reason: Time limit
% 15.41/2.36  % (7069)Termination phase: Saturation
% 15.41/2.36  
% 15.41/2.36  % (7069)Memory used [KB]: 3837
% 15.41/2.36  % (7069)Time elapsed: 0.400 s
% 15.41/2.36  % (7069)------------------------------
% 15.41/2.36  % (7069)------------------------------
% 15.41/2.37  % (7073)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 16.00/2.40  % (7074)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 16.00/2.42  % (7075)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 16.00/2.44  % (6829)Time limit reached!
% 16.00/2.44  % (6829)------------------------------
% 16.00/2.44  % (6829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.00/2.46  % (6829)Termination reason: Time limit
% 16.00/2.46  
% 16.00/2.46  % (6829)Memory used [KB]: 22771
% 16.00/2.46  % (6829)Time elapsed: 2.029 s
% 16.00/2.46  % (6829)------------------------------
% 16.00/2.46  % (6829)------------------------------
% 16.90/2.51  % (7076)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 16.97/2.60  % (7077)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 17.73/2.65  % (7072)Time limit reached!
% 17.73/2.65  % (7072)------------------------------
% 17.73/2.65  % (7072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.73/2.66  % (7060)Refutation found. Thanks to Tanya!
% 17.73/2.66  % SZS status Theorem for theBenchmark
% 17.73/2.66  % (7072)Termination reason: Time limit
% 17.73/2.66  % (7072)Termination phase: Saturation
% 17.73/2.66  
% 17.73/2.66  % (7072)Memory used [KB]: 3326
% 17.73/2.66  % (7072)Time elapsed: 0.400 s
% 17.73/2.66  % (7072)------------------------------
% 17.73/2.66  % (7072)------------------------------
% 17.73/2.67  % SZS output start Proof for theBenchmark
% 17.73/2.67  fof(f28865,plain,(
% 17.73/2.67    $false),
% 17.73/2.67    inference(subsumption_resolution,[],[f28864,f103])).
% 17.73/2.67  fof(f103,plain,(
% 17.73/2.67    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 17.73/2.67    inference(superposition,[],[f80,f93])).
% 17.73/2.67  fof(f93,plain,(
% 17.73/2.67    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) )),
% 17.73/2.67    inference(unit_resulting_resolution,[],[f88,f83])).
% 17.73/2.67  fof(f83,plain,(
% 17.73/2.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 17.73/2.67    inference(definition_unfolding,[],[f75,f61])).
% 17.73/2.67  fof(f61,plain,(
% 17.73/2.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 17.73/2.67    inference(cnf_transformation,[],[f10])).
% 17.73/2.67  fof(f10,axiom,(
% 17.73/2.67    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 17.73/2.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 17.73/2.67  fof(f75,plain,(
% 17.73/2.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 17.73/2.67    inference(cnf_transformation,[],[f47])).
% 17.73/2.67  fof(f47,plain,(
% 17.73/2.67    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 17.73/2.67    inference(nnf_transformation,[],[f4])).
% 17.73/2.67  fof(f4,axiom,(
% 17.73/2.67    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 17.73/2.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 17.73/2.67  fof(f88,plain,(
% 17.73/2.67    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 17.73/2.67    inference(equality_resolution,[],[f69])).
% 17.73/2.67  fof(f69,plain,(
% 17.73/2.67    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 17.73/2.67    inference(cnf_transformation,[],[f42])).
% 17.73/2.67  fof(f42,plain,(
% 17.73/2.67    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 17.73/2.67    inference(flattening,[],[f41])).
% 17.73/2.67  fof(f41,plain,(
% 17.73/2.67    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 17.73/2.67    inference(nnf_transformation,[],[f3])).
% 17.73/2.67  fof(f3,axiom,(
% 17.73/2.67    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 17.73/2.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 17.73/2.67  fof(f80,plain,(
% 17.73/2.67    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 17.73/2.67    inference(definition_unfolding,[],[f59,f61])).
% 17.73/2.67  fof(f59,plain,(
% 17.73/2.67    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 17.73/2.67    inference(cnf_transformation,[],[f6])).
% 17.73/2.67  fof(f6,axiom,(
% 17.73/2.67    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 17.73/2.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 17.73/2.67  fof(f28864,plain,(
% 17.73/2.67    ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 17.73/2.67    inference(forward_demodulation,[],[f28863,f6854])).
% 17.73/2.67  fof(f6854,plain,(
% 17.73/2.67    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 17.73/2.67    inference(forward_demodulation,[],[f6837,f93])).
% 17.73/2.67  fof(f6837,plain,(
% 17.73/2.67    ( ! [X2] : (k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,X2))) )),
% 17.73/2.67    inference(superposition,[],[f2237,f93])).
% 17.73/2.67  fof(f2237,plain,(
% 17.73/2.67    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) )),
% 17.73/2.67    inference(unit_resulting_resolution,[],[f48,f49,f76])).
% 17.73/2.67  fof(f76,plain,(
% 17.73/2.67    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 17.73/2.67    inference(cnf_transformation,[],[f31])).
% 17.73/2.67  fof(f31,plain,(
% 17.73/2.67    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 17.73/2.67    inference(flattening,[],[f30])).
% 17.73/2.67  fof(f30,plain,(
% 17.73/2.67    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 17.73/2.67    inference(ennf_transformation,[],[f14])).
% 17.73/2.67  fof(f14,axiom,(
% 17.73/2.67    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 17.73/2.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).
% 17.73/2.67  fof(f49,plain,(
% 17.73/2.67    v1_funct_1(sK1)),
% 17.73/2.67    inference(cnf_transformation,[],[f35])).
% 17.73/2.67  fof(f35,plain,(
% 17.73/2.67    sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0)) & r1_tarski(sK0,k2_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 17.73/2.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f34])).
% 17.73/2.67  fof(f34,plain,(
% 17.73/2.67    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0)) & r1_tarski(sK0,k2_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 17.73/2.67    introduced(choice_axiom,[])).
% 17.73/2.67  fof(f20,plain,(
% 17.73/2.67    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 17.73/2.67    inference(flattening,[],[f19])).
% 17.73/2.67  fof(f19,plain,(
% 17.73/2.67    ? [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 17.73/2.67    inference(ennf_transformation,[],[f18])).
% 17.73/2.67  fof(f18,negated_conjecture,(
% 17.73/2.67    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 17.73/2.67    inference(negated_conjecture,[],[f17])).
% 17.73/2.67  fof(f17,conjecture,(
% 17.73/2.67    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 17.73/2.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 17.73/2.67  fof(f48,plain,(
% 17.73/2.67    v1_relat_1(sK1)),
% 17.73/2.67    inference(cnf_transformation,[],[f35])).
% 17.73/2.67  fof(f28863,plain,(
% 17.73/2.67    ~r1_tarski(k10_relat_1(sK1,k1_xboole_0),k1_xboole_0)),
% 17.73/2.67    inference(forward_demodulation,[],[f28855,f93])).
% 17.73/2.67  fof(f28855,plain,(
% 17.73/2.67    ~r1_tarski(k10_relat_1(sK1,k6_subset_1(sK0,sK0)),k1_xboole_0)),
% 17.73/2.67    inference(backward_demodulation,[],[f5040,f28847])).
% 17.73/2.67  fof(f28847,plain,(
% 17.73/2.67    ( ! [X21,X20] : (k10_relat_1(sK1,k6_subset_1(X21,k9_relat_1(sK1,k10_relat_1(sK1,X20)))) = k10_relat_1(sK1,k6_subset_1(X21,X20))) )),
% 17.73/2.67    inference(forward_demodulation,[],[f28682,f2237])).
% 17.73/2.67  fof(f28682,plain,(
% 17.73/2.67    ( ! [X21,X20] : (k10_relat_1(sK1,k6_subset_1(X21,k9_relat_1(sK1,k10_relat_1(sK1,X20)))) = k6_subset_1(k10_relat_1(sK1,X21),k10_relat_1(sK1,X20))) )),
% 17.73/2.67    inference(superposition,[],[f2237,f27968])).
% 17.73/2.67  fof(f27968,plain,(
% 17.73/2.67    ( ! [X0] : (k10_relat_1(sK1,X0) = k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0)))) )),
% 17.73/2.67    inference(unit_resulting_resolution,[],[f48,f21484,f23371,f1420])).
% 17.73/2.67  fof(f1420,plain,(
% 17.73/2.67    ( ! [X6,X5] : (~r1_tarski(k10_relat_1(X6,k9_relat_1(X6,X5)),X5) | ~v1_relat_1(X6) | k10_relat_1(X6,k9_relat_1(X6,X5)) = X5 | ~r1_tarski(X5,k1_relat_1(X6))) )),
% 17.73/2.67    inference(resolution,[],[f65,f70])).
% 17.73/2.67  fof(f70,plain,(
% 17.73/2.67    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 17.73/2.67    inference(cnf_transformation,[],[f42])).
% 17.73/2.67  fof(f65,plain,(
% 17.73/2.67    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 17.73/2.67    inference(cnf_transformation,[],[f24])).
% 17.73/2.67  fof(f24,plain,(
% 17.73/2.67    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 17.73/2.67    inference(flattening,[],[f23])).
% 17.73/2.67  fof(f23,plain,(
% 17.73/2.67    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 17.73/2.67    inference(ennf_transformation,[],[f16])).
% 17.73/2.67  fof(f16,axiom,(
% 17.73/2.67    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 17.73/2.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 17.73/2.67  fof(f23371,plain,(
% 17.73/2.67    ( ! [X42] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X42))),k10_relat_1(sK1,X42))) )),
% 17.73/2.67    inference(subsumption_resolution,[],[f23350,f6854])).
% 17.73/2.67  fof(f23350,plain,(
% 17.73/2.67    ( ! [X42] : (k1_xboole_0 != k10_relat_1(sK1,k1_xboole_0) | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X42))),k10_relat_1(sK1,X42))) )),
% 17.73/2.67    inference(superposition,[],[f6841,f447])).
% 17.73/2.67  fof(f447,plain,(
% 17.73/2.67    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 17.73/2.67    inference(unit_resulting_resolution,[],[f413,f83])).
% 17.73/2.67  fof(f413,plain,(
% 17.73/2.67    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 17.73/2.67    inference(unit_resulting_resolution,[],[f48,f49,f67])).
% 17.73/2.67  fof(f67,plain,(
% 17.73/2.67    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 17.73/2.67    inference(cnf_transformation,[],[f28])).
% 17.73/2.67  fof(f28,plain,(
% 17.73/2.67    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 17.73/2.67    inference(flattening,[],[f27])).
% 17.73/2.67  fof(f27,plain,(
% 17.73/2.67    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 17.73/2.67    inference(ennf_transformation,[],[f15])).
% 17.73/2.67  fof(f15,axiom,(
% 17.73/2.67    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 17.73/2.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 17.73/2.67  fof(f6841,plain,(
% 17.73/2.67    ( ! [X6,X5] : (k1_xboole_0 != k10_relat_1(sK1,k6_subset_1(X5,X6)) | r1_tarski(k10_relat_1(sK1,X5),k10_relat_1(sK1,X6))) )),
% 17.73/2.67    inference(superposition,[],[f84,f2237])).
% 17.73/2.67  fof(f84,plain,(
% 17.73/2.67    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 17.73/2.67    inference(definition_unfolding,[],[f74,f61])).
% 17.73/2.67  fof(f74,plain,(
% 17.73/2.67    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 17.73/2.67    inference(cnf_transformation,[],[f47])).
% 17.73/2.67  fof(f21484,plain,(
% 17.73/2.67    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 17.73/2.67    inference(unit_resulting_resolution,[],[f49,f48,f12153])).
% 17.73/2.67  fof(f12153,plain,(
% 17.73/2.67    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0)) )),
% 17.73/2.67    inference(duplicate_literal_removal,[],[f12150])).
% 17.73/2.67  fof(f12150,plain,(
% 17.73/2.67    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))) )),
% 17.73/2.67    inference(resolution,[],[f1650,f73])).
% 17.73/2.67  fof(f73,plain,(
% 17.73/2.67    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 17.73/2.67    inference(cnf_transformation,[],[f46])).
% 17.73/2.67  fof(f46,plain,(
% 17.73/2.67    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 17.73/2.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).
% 17.73/2.67  fof(f45,plain,(
% 17.73/2.67    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 17.73/2.67    introduced(choice_axiom,[])).
% 17.73/2.67  fof(f44,plain,(
% 17.73/2.67    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 17.73/2.67    inference(rectify,[],[f43])).
% 17.73/2.67  fof(f43,plain,(
% 17.73/2.67    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 17.73/2.67    inference(nnf_transformation,[],[f29])).
% 17.73/2.67  fof(f29,plain,(
% 17.73/2.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 17.73/2.67    inference(ennf_transformation,[],[f2])).
% 17.73/2.67  fof(f2,axiom,(
% 17.73/2.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 17.73/2.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 17.73/2.67  fof(f1650,plain,(
% 17.73/2.67    ( ! [X2,X0,X1] : (r2_hidden(sK3(k10_relat_1(X0,X1),X2),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r1_tarski(k10_relat_1(X0,X1),X2)) )),
% 17.73/2.67    inference(resolution,[],[f87,f72])).
% 17.73/2.67  fof(f72,plain,(
% 17.73/2.67    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 17.73/2.67    inference(cnf_transformation,[],[f46])).
% 17.73/2.67  fof(f87,plain,(
% 17.73/2.67    ( ! [X4,X0,X1] : (~r2_hidden(X4,k10_relat_1(X0,X1)) | r2_hidden(X4,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 17.73/2.67    inference(equality_resolution,[],[f53])).
% 17.73/2.67  fof(f53,plain,(
% 17.73/2.67    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X4,X2) | k10_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 17.73/2.67    inference(cnf_transformation,[],[f40])).
% 17.73/2.67  fof(f40,plain,(
% 17.73/2.67    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((~r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1) | ~r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 17.73/2.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 17.73/2.67  fof(f39,plain,(
% 17.73/2.67    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((~r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1) | ~r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 17.73/2.67    introduced(choice_axiom,[])).
% 17.73/2.67  fof(f38,plain,(
% 17.73/2.67    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 17.73/2.67    inference(rectify,[],[f37])).
% 17.73/2.67  fof(f37,plain,(
% 17.73/2.67    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 17.73/2.67    inference(flattening,[],[f36])).
% 17.73/2.67  fof(f36,plain,(
% 17.73/2.67    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 17.73/2.67    inference(nnf_transformation,[],[f22])).
% 17.73/2.67  fof(f22,plain,(
% 17.73/2.67    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 17.73/2.67    inference(flattening,[],[f21])).
% 17.73/2.67  fof(f21,plain,(
% 17.73/2.67    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 17.73/2.67    inference(ennf_transformation,[],[f13])).
% 17.73/2.67  fof(f13,axiom,(
% 17.73/2.67    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 17.73/2.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).
% 17.73/2.67  fof(f5040,plain,(
% 17.73/2.67    ~r1_tarski(k10_relat_1(sK1,k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),k1_xboole_0)),
% 17.73/2.67    inference(unit_resulting_resolution,[],[f103,f1896,f70])).
% 17.73/2.67  fof(f1896,plain,(
% 17.73/2.67    k1_xboole_0 != k10_relat_1(sK1,k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))))),
% 17.73/2.67    inference(unit_resulting_resolution,[],[f48,f477,f282,f66])).
% 17.73/2.67  fof(f66,plain,(
% 17.73/2.67    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 17.73/2.67    inference(cnf_transformation,[],[f26])).
% 17.73/2.67  fof(f26,plain,(
% 17.73/2.67    ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 17.73/2.67    inference(flattening,[],[f25])).
% 17.73/2.67  fof(f25,plain,(
% 17.73/2.67    ! [X0,X1] : ((k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 17.73/2.67    inference(ennf_transformation,[],[f12])).
% 17.73/2.67  fof(f12,axiom,(
% 17.73/2.67    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 17.73/2.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).
% 17.73/2.67  fof(f282,plain,(
% 17.73/2.67    ( ! [X0] : (r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK1))) )),
% 17.73/2.67    inference(unit_resulting_resolution,[],[f80,f50,f77])).
% 17.73/2.67  fof(f77,plain,(
% 17.73/2.67    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 17.73/2.67    inference(cnf_transformation,[],[f33])).
% 17.73/2.67  fof(f33,plain,(
% 17.73/2.67    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 17.73/2.67    inference(flattening,[],[f32])).
% 17.73/2.67  fof(f32,plain,(
% 17.73/2.67    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 17.73/2.67    inference(ennf_transformation,[],[f5])).
% 17.73/2.67  fof(f5,axiom,(
% 17.73/2.67    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 17.73/2.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 17.73/2.67  fof(f50,plain,(
% 17.73/2.67    r1_tarski(sK0,k2_relat_1(sK1))),
% 17.73/2.67    inference(cnf_transformation,[],[f35])).
% 17.73/2.67  fof(f477,plain,(
% 17.73/2.67    k1_xboole_0 != k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),
% 17.73/2.67    inference(unit_resulting_resolution,[],[f446,f84])).
% 17.73/2.67  fof(f446,plain,(
% 17.73/2.67    ~r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),
% 17.73/2.67    inference(unit_resulting_resolution,[],[f51,f413,f70])).
% 17.73/2.67  fof(f51,plain,(
% 17.73/2.67    sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0))),
% 17.73/2.67    inference(cnf_transformation,[],[f35])).
% 17.73/2.67  % SZS output end Proof for theBenchmark
% 17.73/2.67  % (7060)------------------------------
% 17.73/2.67  % (7060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.73/2.67  % (7060)Termination reason: Refutation
% 17.73/2.67  
% 17.73/2.67  % (7060)Memory used [KB]: 22131
% 17.73/2.67  % (7060)Time elapsed: 1.570 s
% 17.73/2.67  % (7060)------------------------------
% 17.73/2.67  % (7060)------------------------------
% 17.73/2.68  % (6819)Success in time 2.321 s
%------------------------------------------------------------------------------
