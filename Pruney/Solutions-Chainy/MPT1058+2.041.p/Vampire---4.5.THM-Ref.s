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
% DateTime   : Thu Dec  3 13:07:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 183 expanded)
%              Number of leaves         :   17 (  52 expanded)
%              Depth                    :   17
%              Number of atoms          :  309 ( 542 expanded)
%              Number of equality atoms :   60 ( 137 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f543,plain,(
    $false ),
    inference(subsumption_resolution,[],[f542,f154])).

fof(f154,plain,(
    k10_relat_1(sK2,sK4) != k3_xboole_0(sK3,k10_relat_1(sK2,sK4)) ),
    inference(superposition,[],[f57,f152])).

fof(f152,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK2,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK2,X1)) ),
    inference(resolution,[],[f83,f54])).

fof(f54,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4)
    & r1_tarski(k10_relat_1(sK2,sK4),sK3)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK2,X2) != k10_relat_1(k7_relat_1(sK2,X1),X2)
          & r1_tarski(k10_relat_1(sK2,X2),X1) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2,X1] :
        ( k10_relat_1(sK2,X2) != k10_relat_1(k7_relat_1(sK2,X1),X2)
        & r1_tarski(k10_relat_1(sK2,X2),X1) )
   => ( k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4)
      & r1_tarski(k10_relat_1(sK2,sK4),sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f57,plain,(
    k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f542,plain,(
    k10_relat_1(sK2,sK4) = k3_xboole_0(sK3,k10_relat_1(sK2,sK4)) ),
    inference(forward_demodulation,[],[f540,f217])).

fof(f217,plain,(
    ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f206,f98])).

fof(f98,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f97,f60])).

fof(f60,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f97,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f96,f61])).

fof(f61,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f96,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f62,f58])).

fof(f58,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f206,plain,(
    ! [X0] : k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X0)) = X0 ),
    inference(resolution,[],[f203,f91])).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f203,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | k9_relat_1(k6_relat_1(X2),k10_relat_1(k6_relat_1(X2),X1)) = X1 ) ),
    inference(forward_demodulation,[],[f202,f61])).

fof(f202,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k2_relat_1(k6_relat_1(X2)))
      | k9_relat_1(k6_relat_1(X2),k10_relat_1(k6_relat_1(X2),X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f200,f58])).

fof(f200,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k2_relat_1(k6_relat_1(X2)))
      | k9_relat_1(k6_relat_1(X2),k10_relat_1(k6_relat_1(X2),X1)) = X1
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(resolution,[],[f75,f59])).

fof(f59,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f540,plain,(
    k3_xboole_0(sK3,k10_relat_1(sK2,sK4)) = k9_relat_1(k6_relat_1(k10_relat_1(sK2,sK4)),k10_relat_1(sK2,sK4)) ),
    inference(superposition,[],[f258,f450])).

fof(f450,plain,(
    k10_relat_1(sK2,sK4) = k10_relat_1(k6_relat_1(k10_relat_1(sK2,sK4)),sK3) ),
    inference(subsumption_resolution,[],[f139,f449])).

fof(f449,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(duplicate_literal_removal,[],[f444])).

fof(f444,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)
      | r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ) ),
    inference(resolution,[],[f378,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f51,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f378,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK6(k10_relat_1(k6_relat_1(X2),X3),X4),X2)
      | r1_tarski(k10_relat_1(k6_relat_1(X2),X3),X4) ) ),
    inference(forward_demodulation,[],[f377,f60])).

fof(f377,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK6(k10_relat_1(k6_relat_1(X2),X3),X4),k1_relat_1(k6_relat_1(X2)))
      | r1_tarski(k10_relat_1(k6_relat_1(X2),X3),X4) ) ),
    inference(subsumption_resolution,[],[f375,f58])).

fof(f375,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK6(k10_relat_1(k6_relat_1(X2),X3),X4),k1_relat_1(k6_relat_1(X2)))
      | r1_tarski(k10_relat_1(k6_relat_1(X2),X3),X4)
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(resolution,[],[f220,f59])).

fof(f220,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK6(k10_relat_1(X0,X1),X2),k1_relat_1(X0))
      | r1_tarski(k10_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f164,f71])).

fof(f71,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f25,f37,f36])).

fof(f36,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
            & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> sP0(X1,X0,X2) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0)
      | r1_tarski(k10_relat_1(X0,X1),X2)
      | r2_hidden(sK6(k10_relat_1(X0,X1),X2),k1_relat_1(X0)) ) ),
    inference(resolution,[],[f108,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0,k10_relat_1(X0,X1))
      | ~ sP1(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ~ sP0(X1,X0,X2) )
          & ( sP0(X1,X0,X2)
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X3,X2,X0)
      | r2_hidden(sK6(X0,X1),k1_relat_1(X2))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f65,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(X4,k1_relat_1(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(k1_funct_1(X1,sK5(X0,X1,X2)),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),k1_relat_1(X1))
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(k1_funct_1(X1,sK5(X0,X1,X2)),X0)
              & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X1)) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(k1_funct_1(X1,X4),X0)
              | ~ r2_hidden(X4,k1_relat_1(X1)) )
            & ( ( r2_hidden(k1_funct_1(X1,X4),X0)
                & r2_hidden(X4,k1_relat_1(X1)) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f45,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k1_funct_1(X1,X3),X0)
            | ~ r2_hidden(X3,k1_relat_1(X1))
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k1_funct_1(X1,X3),X0)
              & r2_hidden(X3,k1_relat_1(X1)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X1,sK5(X0,X1,X2)),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),k1_relat_1(X1))
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(k1_funct_1(X1,sK5(X0,X1,X2)),X0)
            & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X1)) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(k1_funct_1(X1,X3),X0)
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(k1_funct_1(X1,X3),X0)
                & r2_hidden(X3,k1_relat_1(X1)) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(k1_funct_1(X1,X4),X0)
              | ~ r2_hidden(X4,k1_relat_1(X1)) )
            & ( ( r2_hidden(k1_funct_1(X1,X4),X0)
                & r2_hidden(X4,k1_relat_1(X1)) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f139,plain,
    ( ~ r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(sK2,sK4)),sK3),k10_relat_1(sK2,sK4))
    | k10_relat_1(sK2,sK4) = k10_relat_1(k6_relat_1(k10_relat_1(sK2,sK4)),sK3) ),
    inference(resolution,[],[f128,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f128,plain,(
    r1_tarski(k10_relat_1(sK2,sK4),k10_relat_1(k6_relat_1(k10_relat_1(sK2,sK4)),sK3)) ),
    inference(superposition,[],[f121,f98])).

fof(f121,plain,(
    ! [X2] : r1_tarski(k10_relat_1(k6_relat_1(X2),k10_relat_1(sK2,sK4)),k10_relat_1(k6_relat_1(X2),sK3)) ),
    inference(resolution,[],[f113,f56])).

fof(f56,plain,(
    r1_tarski(k10_relat_1(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f113,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | r1_tarski(k10_relat_1(k6_relat_1(X4),X2),k10_relat_1(k6_relat_1(X4),X3)) ) ),
    inference(resolution,[],[f84,f58])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

fof(f258,plain,(
    ! [X2,X1] : k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k3_xboole_0(X2,X1) ),
    inference(forward_demodulation,[],[f257,f217])).

fof(f257,plain,(
    ! [X2,X1] : k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k3_xboole_0(X2,k9_relat_1(k6_relat_1(X1),X1)) ),
    inference(forward_demodulation,[],[f256,f60])).

fof(f256,plain,(
    ! [X2,X1] : k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k3_xboole_0(X2,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1)))) ),
    inference(subsumption_resolution,[],[f252,f58])).

fof(f252,plain,(
    ! [X2,X1] :
      ( k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k3_xboole_0(X2,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1))))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(resolution,[],[f74,f59])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:45:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (21796)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.48  % (21804)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.50  % (21796)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (21793)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f543,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(subsumption_resolution,[],[f542,f154])).
% 0.20/0.51  fof(f154,plain,(
% 0.20/0.51    k10_relat_1(sK2,sK4) != k3_xboole_0(sK3,k10_relat_1(sK2,sK4))),
% 0.20/0.51    inference(superposition,[],[f57,f152])).
% 0.20/0.51  fof(f152,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK2,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK2,X1))) )),
% 0.20/0.51    inference(resolution,[],[f83,f54])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    v1_relat_1(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    (k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) & r1_tarski(k10_relat_1(sK2,sK4),sK3)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f40,f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK2,X2) != k10_relat_1(k7_relat_1(sK2,X1),X2) & r1_tarski(k10_relat_1(sK2,X2),X1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ? [X2,X1] : (k10_relat_1(sK2,X2) != k10_relat_1(k7_relat_1(sK2,X1),X2) & r1_tarski(k10_relat_1(sK2,X2),X1)) => (k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) & r1_tarski(k10_relat_1(sK2,sK4),sK3))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 0.20/0.51    inference(negated_conjecture,[],[f19])).
% 0.20/0.51  fof(f19,conjecture,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4)),
% 0.20/0.51    inference(cnf_transformation,[],[f41])).
% 0.20/0.51  fof(f542,plain,(
% 0.20/0.51    k10_relat_1(sK2,sK4) = k3_xboole_0(sK3,k10_relat_1(sK2,sK4))),
% 0.20/0.51    inference(forward_demodulation,[],[f540,f217])).
% 0.20/0.51  fof(f217,plain,(
% 0.20/0.51    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),X0) = X0) )),
% 0.20/0.51    inference(forward_demodulation,[],[f206,f98])).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 0.20/0.51    inference(forward_demodulation,[],[f97,f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,axiom,(
% 0.20/0.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f96,f61])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0)))) )),
% 0.20/0.51    inference(resolution,[],[f62,f58])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,axiom,(
% 0.20/0.51    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.20/0.51  fof(f206,plain,(
% 0.20/0.51    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X0)) = X0) )),
% 0.20/0.51    inference(resolution,[],[f203,f91])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f77])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(flattening,[],[f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.51  fof(f203,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~r1_tarski(X1,X2) | k9_relat_1(k6_relat_1(X2),k10_relat_1(k6_relat_1(X2),X1)) = X1) )),
% 0.20/0.51    inference(forward_demodulation,[],[f202,f61])).
% 0.20/0.51  fof(f202,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~r1_tarski(X1,k2_relat_1(k6_relat_1(X2))) | k9_relat_1(k6_relat_1(X2),k10_relat_1(k6_relat_1(X2),X1)) = X1) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f200,f58])).
% 0.20/0.51  fof(f200,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~r1_tarski(X1,k2_relat_1(k6_relat_1(X2))) | k9_relat_1(k6_relat_1(X2),k10_relat_1(k6_relat_1(X2),X1)) = X1 | ~v1_relat_1(k6_relat_1(X2))) )),
% 0.20/0.51    inference(resolution,[],[f75,f59])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(flattening,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,axiom,(
% 0.20/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 0.20/0.51  fof(f540,plain,(
% 0.20/0.51    k3_xboole_0(sK3,k10_relat_1(sK2,sK4)) = k9_relat_1(k6_relat_1(k10_relat_1(sK2,sK4)),k10_relat_1(sK2,sK4))),
% 0.20/0.51    inference(superposition,[],[f258,f450])).
% 0.20/0.51  fof(f450,plain,(
% 0.20/0.51    k10_relat_1(sK2,sK4) = k10_relat_1(k6_relat_1(k10_relat_1(sK2,sK4)),sK3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f139,f449])).
% 0.20/0.51  fof(f449,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f444])).
% 0.20/0.51  fof(f444,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) | r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 0.20/0.51    inference(resolution,[],[f378,f81])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f51,f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(rectify,[],[f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(nnf_transformation,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.51  fof(f378,plain,(
% 0.20/0.51    ( ! [X4,X2,X3] : (r2_hidden(sK6(k10_relat_1(k6_relat_1(X2),X3),X4),X2) | r1_tarski(k10_relat_1(k6_relat_1(X2),X3),X4)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f377,f60])).
% 0.20/0.51  fof(f377,plain,(
% 0.20/0.51    ( ! [X4,X2,X3] : (r2_hidden(sK6(k10_relat_1(k6_relat_1(X2),X3),X4),k1_relat_1(k6_relat_1(X2))) | r1_tarski(k10_relat_1(k6_relat_1(X2),X3),X4)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f375,f58])).
% 0.20/0.51  fof(f375,plain,(
% 0.20/0.51    ( ! [X4,X2,X3] : (r2_hidden(sK6(k10_relat_1(k6_relat_1(X2),X3),X4),k1_relat_1(k6_relat_1(X2))) | r1_tarski(k10_relat_1(k6_relat_1(X2),X3),X4) | ~v1_relat_1(k6_relat_1(X2))) )),
% 0.20/0.51    inference(resolution,[],[f220,f59])).
% 0.20/0.51  fof(f220,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK6(k10_relat_1(X0,X1),X2),k1_relat_1(X0)) | r1_tarski(k10_relat_1(X0,X1),X2) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(resolution,[],[f164,f71])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ( ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(definition_folding,[],[f25,f37,f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0)))))),
% 0.20/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> sP0(X1,X0,X2)) | ~sP1(X0))),
% 0.20/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,axiom,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).
% 0.20/0.51  fof(f164,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~sP1(X0) | r1_tarski(k10_relat_1(X0,X1),X2) | r2_hidden(sK6(k10_relat_1(X0,X1),X2),k1_relat_1(X0))) )),
% 0.20/0.51    inference(resolution,[],[f108,f90])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    ( ! [X0,X1] : (sP0(X1,X0,k10_relat_1(X0,X1)) | ~sP1(X0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k10_relat_1(X0,X1) != X2 | ~sP1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k10_relat_1(X0,X1) != X2)) | ~sP1(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f37])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~sP0(X3,X2,X0) | r2_hidden(sK6(X0,X1),k1_relat_1(X2)) | r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(resolution,[],[f65,f80])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f53])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r2_hidden(X4,k1_relat_1(X1)) | ~sP0(X0,X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(k1_funct_1(X1,sK5(X0,X1,X2)),X0) | ~r2_hidden(sK5(X0,X1,X2),k1_relat_1(X1)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X1,sK5(X0,X1,X2)),X0) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X1))) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X1,X4),X0) | ~r2_hidden(X4,k1_relat_1(X1))) & ((r2_hidden(k1_funct_1(X1,X4),X0) & r2_hidden(X4,k1_relat_1(X1))) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f45,f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k1_funct_1(X1,X3),X0) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X1,X3),X0) & r2_hidden(X3,k1_relat_1(X1))) | r2_hidden(X3,X2))) => ((~r2_hidden(k1_funct_1(X1,sK5(X0,X1,X2)),X0) | ~r2_hidden(sK5(X0,X1,X2),k1_relat_1(X1)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X1,sK5(X0,X1,X2)),X0) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X1))) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(k1_funct_1(X1,X3),X0) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X1,X3),X0) & r2_hidden(X3,k1_relat_1(X1))) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X1,X4),X0) | ~r2_hidden(X4,k1_relat_1(X1))) & ((r2_hidden(k1_funct_1(X1,X4),X0) & r2_hidden(X4,k1_relat_1(X1))) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.20/0.51    inference(rectify,[],[f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.20/0.51    inference(flattening,[],[f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.20/0.51    inference(nnf_transformation,[],[f36])).
% 0.20/0.51  fof(f139,plain,(
% 0.20/0.51    ~r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(sK2,sK4)),sK3),k10_relat_1(sK2,sK4)) | k10_relat_1(sK2,sK4) = k10_relat_1(k6_relat_1(k10_relat_1(sK2,sK4)),sK3)),
% 0.20/0.51    inference(resolution,[],[f128,f78])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f49])).
% 0.20/0.51  fof(f128,plain,(
% 0.20/0.51    r1_tarski(k10_relat_1(sK2,sK4),k10_relat_1(k6_relat_1(k10_relat_1(sK2,sK4)),sK3))),
% 0.20/0.51    inference(superposition,[],[f121,f98])).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    ( ! [X2] : (r1_tarski(k10_relat_1(k6_relat_1(X2),k10_relat_1(sK2,sK4)),k10_relat_1(k6_relat_1(X2),sK3))) )),
% 0.20/0.51    inference(resolution,[],[f113,f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    r1_tarski(k10_relat_1(sK2,sK4),sK3)),
% 0.20/0.51    inference(cnf_transformation,[],[f41])).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    ( ! [X4,X2,X3] : (~r1_tarski(X2,X3) | r1_tarski(k10_relat_1(k6_relat_1(X4),X2),k10_relat_1(k6_relat_1(X4),X3))) )),
% 0.20/0.51    inference(resolution,[],[f84,f58])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(flattening,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).
% 0.20/0.51  fof(f258,plain,(
% 0.20/0.51    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k3_xboole_0(X2,X1)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f257,f217])).
% 0.20/0.51  fof(f257,plain,(
% 0.20/0.51    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k3_xboole_0(X2,k9_relat_1(k6_relat_1(X1),X1))) )),
% 0.20/0.51    inference(forward_demodulation,[],[f256,f60])).
% 0.20/0.51  fof(f256,plain,(
% 0.20/0.51    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k3_xboole_0(X2,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1))))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f252,f58])).
% 0.20/0.51  fof(f252,plain,(
% 0.20/0.51    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k3_xboole_0(X2,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1)))) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.20/0.51    inference(resolution,[],[f74,f59])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(flattening,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,axiom,(
% 0.20/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (21796)------------------------------
% 0.20/0.51  % (21796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (21796)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (21796)Memory used [KB]: 7036
% 0.20/0.51  % (21796)Time elapsed: 0.090 s
% 0.20/0.51  % (21796)------------------------------
% 0.20/0.51  % (21796)------------------------------
% 0.20/0.51  % (21788)Success in time 0.163 s
%------------------------------------------------------------------------------
