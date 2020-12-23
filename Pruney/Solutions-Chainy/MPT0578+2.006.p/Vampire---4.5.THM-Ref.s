%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:48 EST 2020

% Result     : Theorem 2.12s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 208 expanded)
%              Number of leaves         :   14 (  59 expanded)
%              Depth                    :   17
%              Number of atoms          :  271 ( 844 expanded)
%              Number of equality atoms :   25 (  53 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1550,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f43,f44,f45,f1533])).

fof(f1533,plain,(
    ! [X10,X11] :
      ( k1_relat_1(k5_relat_1(X10,X11)) = k10_relat_1(X10,k1_relat_1(X11))
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(X10) ) ),
    inference(subsumption_resolution,[],[f1520,f1035])).

fof(f1035,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k1_relat_1(X0)),k1_relat_1(k5_relat_1(X1,X0)))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f1016])).

fof(f1016,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k1_relat_1(X0)),k1_relat_1(k5_relat_1(X1,X0)))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f641,f46])).

fof(f46,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f641,plain,(
    ! [X10,X11,X9] :
      ( r1_tarski(k10_relat_1(X9,k10_relat_1(X10,X11)),k1_relat_1(k5_relat_1(X9,X10)))
      | ~ v1_relat_1(X10)
      | ~ v1_relat_1(X9) ) ),
    inference(subsumption_resolution,[],[f636,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f636,plain,(
    ! [X10,X11,X9] :
      ( r1_tarski(k10_relat_1(X9,k10_relat_1(X10,X11)),k1_relat_1(k5_relat_1(X9,X10)))
      | ~ v1_relat_1(k5_relat_1(X9,X10))
      | ~ v1_relat_1(X10)
      | ~ v1_relat_1(X9) ) ),
    inference(superposition,[],[f604,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

fof(f604,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f583])).

fof(f583,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) ) ),
    inference(resolution,[],[f252,f341])).

fof(f341,plain,(
    ! [X2,X3,X1] :
      ( ~ sP0(X3,X2,sK4(X1,k1_relat_1(X2)))
      | ~ v1_relat_1(X2)
      | r1_tarski(X1,k1_relat_1(X2)) ) ),
    inference(resolution,[],[f275,f136])).

fof(f136,plain,(
    ! [X17,X18,X16] :
      ( sP0(k2_relat_1(X16),X16,X17)
      | ~ sP0(X18,X16,X17) ) ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,(
    ! [X17,X18,X16] :
      ( sP0(k2_relat_1(X16),X16,X17)
      | ~ sP0(X18,X16,X17)
      | ~ sP0(X18,X16,X17) ) ),
    inference(resolution,[],[f114,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),k2_relat_1(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(X3,k2_relat_1(X1)) ) )
      & ( ( r2_hidden(sK5(X0,X1,X2),X0)
          & r2_hidden(k4_tarski(X2,sK5(X0,X1,X2)),X1)
          & r2_hidden(sK5(X0,X1,X2),k2_relat_1(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(k4_tarski(X2,X4),X1)
          & r2_hidden(X4,k2_relat_1(X1)) )
     => ( r2_hidden(sK5(X0,X1,X2),X0)
        & r2_hidden(k4_tarski(X2,sK5(X0,X1,X2)),X1)
        & r2_hidden(sK5(X0,X1,X2),k2_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(X3,k2_relat_1(X1)) ) )
      & ( ? [X4] :
            ( r2_hidden(X4,X0)
            & r2_hidden(k4_tarski(X2,X4),X1)
            & r2_hidden(X4,k2_relat_1(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X0,X3),X2)
            | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(k4_tarski(X0,X3),X2)
          & r2_hidden(X3,k2_relat_1(X2)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X3)
      | sP0(X3,X1,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f112,f60])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X3)
      | sP0(X3,X1,X2)
      | ~ r2_hidden(sK5(X0,X1,X2),k2_relat_1(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f63,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK5(X0,X1,X2)),X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X1)
      | ~ r2_hidden(X3,X0)
      | sP0(X0,X1,X2)
      | ~ r2_hidden(X3,k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f275,plain,(
    ! [X0,X1] :
      ( ~ sP0(k2_relat_1(X0),X0,sK4(X1,k1_relat_1(X0)))
      | r1_tarski(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f272,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f22,f26,f25])).

fof(f26,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f272,plain,(
    ! [X0,X1] :
      ( ~ sP1(sK4(X1,k1_relat_1(X0)),X0,k2_relat_1(X0))
      | ~ sP0(k2_relat_1(X0),X0,sK4(X1,k1_relat_1(X0)))
      | r1_tarski(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f94,f46])).

fof(f94,plain,(
    ! [X4,X5,X3] :
      ( ~ sP1(sK4(X5,k10_relat_1(X4,X3)),X4,X3)
      | ~ sP0(X3,X4,sK4(X5,k10_relat_1(X4,X3)))
      | r1_tarski(X5,k10_relat_1(X4,X3)) ) ),
    inference(resolution,[],[f59,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k10_relat_1(X1,X2))
      | ~ sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X1,X2))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X0,k10_relat_1(X1,X2)) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f252,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,sK4(k10_relat_1(X1,X0),X2))
      | r1_tarski(k10_relat_1(X1,X0),X2)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f87,f64])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(sK4(k10_relat_1(X1,X0),X2),X1,X0)
      | sP0(X0,X1,sK4(k10_relat_1(X1,X0),X2))
      | r1_tarski(k10_relat_1(X1,X0),X2) ) ),
    inference(resolution,[],[f58,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
      | sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1520,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ v1_relat_1(X11)
      | k1_relat_1(k5_relat_1(X10,X11)) = k10_relat_1(X10,k1_relat_1(X11))
      | ~ r1_tarski(k10_relat_1(X10,k1_relat_1(X11)),k1_relat_1(k5_relat_1(X10,X11))) ) ),
    inference(resolution,[],[f1484,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f1484,plain,(
    ! [X8,X7] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X7,X8)),k10_relat_1(X7,k1_relat_1(X8)))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X8) ) ),
    inference(duplicate_literal_removal,[],[f1466])).

fof(f1466,plain,(
    ! [X8,X7] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X7,X8)),k10_relat_1(X7,k1_relat_1(X8)))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(X8) ) ),
    inference(resolution,[],[f180,f604])).

fof(f180,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k10_relat_1(X4,k2_relat_1(k5_relat_1(X3,X4))),X5)
      | r1_tarski(k1_relat_1(k5_relat_1(X3,X4)),k10_relat_1(X3,X5))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f169])).

fof(f169,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X3,X4)),k10_relat_1(X3,X5))
      | ~ r1_tarski(k10_relat_1(X4,k2_relat_1(k5_relat_1(X3,X4))),X5)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f55,f108])).

fof(f108,plain,(
    ! [X4,X3] :
      ( k1_relat_1(k5_relat_1(X3,X4)) = k10_relat_1(X3,k10_relat_1(X4,k2_relat_1(k5_relat_1(X3,X4))))
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f102,f48])).

fof(f102,plain,(
    ! [X4,X3] :
      ( k1_relat_1(k5_relat_1(X3,X4)) = k10_relat_1(X3,k10_relat_1(X4,k2_relat_1(k5_relat_1(X3,X4))))
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k5_relat_1(X3,X4)) ) ),
    inference(superposition,[],[f47,f46])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

fof(f45,plain,(
    k1_relat_1(k5_relat_1(sK2,sK3)) != k10_relat_1(sK2,k1_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK3)) != k10_relat_1(sK2,k1_relat_1(sK3))
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f12,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k1_relat_1(k5_relat_1(sK2,X1)) != k10_relat_1(sK2,k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( k1_relat_1(k5_relat_1(sK2,X1)) != k10_relat_1(sK2,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( k1_relat_1(k5_relat_1(sK2,sK3)) != k10_relat_1(sK2,k1_relat_1(sK3))
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f44,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:39:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (23229)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.48  % (23256)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.49  % (23247)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.49  % (23251)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.49  % (23238)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.50  % (23242)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.50  % (23234)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (23232)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (23235)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (23231)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (23230)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (23227)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (23233)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (23240)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (23258)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (23228)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (23239)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (23250)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (23245)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (23250)Refutation not found, incomplete strategy% (23250)------------------------------
% 0.20/0.52  % (23250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (23250)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (23250)Memory used [KB]: 10618
% 0.20/0.52  % (23250)Time elapsed: 0.119 s
% 0.20/0.52  % (23250)------------------------------
% 0.20/0.52  % (23250)------------------------------
% 0.20/0.53  % (23243)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (23237)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (23257)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (23252)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (23241)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (23248)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (23236)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (23254)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (23246)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (23255)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (23249)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 2.12/0.63  % (23258)Refutation found. Thanks to Tanya!
% 2.12/0.63  % SZS status Theorem for theBenchmark
% 2.12/0.63  % SZS output start Proof for theBenchmark
% 2.12/0.63  fof(f1550,plain,(
% 2.12/0.63    $false),
% 2.12/0.63    inference(unit_resulting_resolution,[],[f43,f44,f45,f1533])).
% 2.12/0.63  fof(f1533,plain,(
% 2.12/0.63    ( ! [X10,X11] : (k1_relat_1(k5_relat_1(X10,X11)) = k10_relat_1(X10,k1_relat_1(X11)) | ~v1_relat_1(X11) | ~v1_relat_1(X10)) )),
% 2.12/0.63    inference(subsumption_resolution,[],[f1520,f1035])).
% 2.12/0.63  fof(f1035,plain,(
% 2.12/0.63    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k1_relat_1(X0)),k1_relat_1(k5_relat_1(X1,X0))) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 2.12/0.63    inference(duplicate_literal_removal,[],[f1016])).
% 2.12/0.63  fof(f1016,plain,(
% 2.12/0.63    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k1_relat_1(X0)),k1_relat_1(k5_relat_1(X1,X0))) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.12/0.63    inference(superposition,[],[f641,f46])).
% 2.12/0.63  fof(f46,plain,(
% 2.12/0.63    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.12/0.63    inference(cnf_transformation,[],[f13])).
% 2.12/0.63  fof(f13,plain,(
% 2.12/0.63    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 2.12/0.63    inference(ennf_transformation,[],[f6])).
% 2.12/0.63  fof(f6,axiom,(
% 2.12/0.63    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 2.12/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 2.12/0.63  fof(f641,plain,(
% 2.12/0.63    ( ! [X10,X11,X9] : (r1_tarski(k10_relat_1(X9,k10_relat_1(X10,X11)),k1_relat_1(k5_relat_1(X9,X10))) | ~v1_relat_1(X10) | ~v1_relat_1(X9)) )),
% 2.12/0.63    inference(subsumption_resolution,[],[f636,f48])).
% 2.12/0.63  fof(f48,plain,(
% 2.12/0.63    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.12/0.63    inference(cnf_transformation,[],[f16])).
% 2.12/0.63  fof(f16,plain,(
% 2.12/0.63    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 2.12/0.63    inference(flattening,[],[f15])).
% 2.12/0.63  fof(f15,plain,(
% 2.12/0.63    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 2.12/0.63    inference(ennf_transformation,[],[f4])).
% 2.12/0.63  fof(f4,axiom,(
% 2.12/0.63    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 2.12/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 2.12/0.63  fof(f636,plain,(
% 2.12/0.63    ( ! [X10,X11,X9] : (r1_tarski(k10_relat_1(X9,k10_relat_1(X10,X11)),k1_relat_1(k5_relat_1(X9,X10))) | ~v1_relat_1(k5_relat_1(X9,X10)) | ~v1_relat_1(X10) | ~v1_relat_1(X9)) )),
% 2.12/0.63    inference(superposition,[],[f604,f47])).
% 2.12/0.63  fof(f47,plain,(
% 2.12/0.63    ( ! [X2,X0,X1] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 2.12/0.63    inference(cnf_transformation,[],[f14])).
% 2.12/0.63  fof(f14,plain,(
% 2.12/0.63    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 2.12/0.63    inference(ennf_transformation,[],[f8])).
% 2.12/0.63  fof(f8,axiom,(
% 2.12/0.63    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 2.12/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).
% 2.12/0.63  fof(f604,plain,(
% 2.12/0.63    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.12/0.63    inference(duplicate_literal_removal,[],[f583])).
% 2.12/0.63  fof(f583,plain,(
% 2.12/0.63    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X0) | r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))) )),
% 2.12/0.63    inference(resolution,[],[f252,f341])).
% 2.12/0.63  fof(f341,plain,(
% 2.12/0.63    ( ! [X2,X3,X1] : (~sP0(X3,X2,sK4(X1,k1_relat_1(X2))) | ~v1_relat_1(X2) | r1_tarski(X1,k1_relat_1(X2))) )),
% 2.12/0.63    inference(resolution,[],[f275,f136])).
% 2.12/0.63  fof(f136,plain,(
% 2.12/0.63    ( ! [X17,X18,X16] : (sP0(k2_relat_1(X16),X16,X17) | ~sP0(X18,X16,X17)) )),
% 2.12/0.63    inference(duplicate_literal_removal,[],[f135])).
% 2.12/0.63  fof(f135,plain,(
% 2.12/0.63    ( ! [X17,X18,X16] : (sP0(k2_relat_1(X16),X16,X17) | ~sP0(X18,X16,X17) | ~sP0(X18,X16,X17)) )),
% 2.12/0.63    inference(resolution,[],[f114,f60])).
% 2.12/0.63  fof(f60,plain,(
% 2.12/0.63    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),k2_relat_1(X1)) | ~sP0(X0,X1,X2)) )),
% 2.12/0.63    inference(cnf_transformation,[],[f42])).
% 2.12/0.63  fof(f42,plain,(
% 2.12/0.63    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(X3,k2_relat_1(X1)))) & ((r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(k4_tarski(X2,sK5(X0,X1,X2)),X1) & r2_hidden(sK5(X0,X1,X2),k2_relat_1(X1))) | ~sP0(X0,X1,X2)))),
% 2.12/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).
% 2.12/0.63  fof(f41,plain,(
% 2.12/0.63    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(k4_tarski(X2,X4),X1) & r2_hidden(X4,k2_relat_1(X1))) => (r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(k4_tarski(X2,sK5(X0,X1,X2)),X1) & r2_hidden(sK5(X0,X1,X2),k2_relat_1(X1))))),
% 2.12/0.63    introduced(choice_axiom,[])).
% 2.12/0.63  fof(f40,plain,(
% 2.12/0.63    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(X3,k2_relat_1(X1)))) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(k4_tarski(X2,X4),X1) & r2_hidden(X4,k2_relat_1(X1))) | ~sP0(X0,X1,X2)))),
% 2.12/0.63    inference(rectify,[],[f39])).
% 2.12/0.63  fof(f39,plain,(
% 2.12/0.63    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~sP0(X1,X2,X0)))),
% 2.12/0.63    inference(nnf_transformation,[],[f25])).
% 2.12/0.63  fof(f25,plain,(
% 2.12/0.63    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))))),
% 2.12/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.12/0.63  fof(f114,plain,(
% 2.12/0.63    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK5(X0,X1,X2),X3) | sP0(X3,X1,X2) | ~sP0(X0,X1,X2)) )),
% 2.12/0.63    inference(subsumption_resolution,[],[f112,f60])).
% 2.12/0.63  fof(f112,plain,(
% 2.12/0.63    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK5(X0,X1,X2),X3) | sP0(X3,X1,X2) | ~r2_hidden(sK5(X0,X1,X2),k2_relat_1(X1)) | ~sP0(X0,X1,X2)) )),
% 2.12/0.63    inference(resolution,[],[f63,f61])).
% 2.12/0.63  fof(f61,plain,(
% 2.12/0.63    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK5(X0,X1,X2)),X1) | ~sP0(X0,X1,X2)) )),
% 2.12/0.63    inference(cnf_transformation,[],[f42])).
% 2.12/0.63  fof(f63,plain,(
% 2.12/0.63    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(X3,X0) | sP0(X0,X1,X2) | ~r2_hidden(X3,k2_relat_1(X1))) )),
% 2.12/0.63    inference(cnf_transformation,[],[f42])).
% 2.12/0.63  fof(f275,plain,(
% 2.12/0.63    ( ! [X0,X1] : (~sP0(k2_relat_1(X0),X0,sK4(X1,k1_relat_1(X0))) | r1_tarski(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.12/0.63    inference(subsumption_resolution,[],[f272,f64])).
% 2.12/0.63  fof(f64,plain,(
% 2.12/0.63    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | ~v1_relat_1(X2)) )),
% 2.12/0.63    inference(cnf_transformation,[],[f27])).
% 2.12/0.63  fof(f27,plain,(
% 2.12/0.63    ! [X0,X1,X2] : (sP1(X0,X2,X1) | ~v1_relat_1(X2))),
% 2.12/0.63    inference(definition_folding,[],[f22,f26,f25])).
% 2.12/0.63  fof(f26,plain,(
% 2.12/0.63    ! [X0,X2,X1] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 2.12/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.12/0.63  fof(f22,plain,(
% 2.12/0.63    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 2.12/0.63    inference(ennf_transformation,[],[f5])).
% 2.12/0.63  fof(f5,axiom,(
% 2.12/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 2.12/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 2.12/0.63  fof(f272,plain,(
% 2.12/0.63    ( ! [X0,X1] : (~sP1(sK4(X1,k1_relat_1(X0)),X0,k2_relat_1(X0)) | ~sP0(k2_relat_1(X0),X0,sK4(X1,k1_relat_1(X0))) | r1_tarski(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.12/0.63    inference(superposition,[],[f94,f46])).
% 2.12/0.63  fof(f94,plain,(
% 2.12/0.63    ( ! [X4,X5,X3] : (~sP1(sK4(X5,k10_relat_1(X4,X3)),X4,X3) | ~sP0(X3,X4,sK4(X5,k10_relat_1(X4,X3))) | r1_tarski(X5,k10_relat_1(X4,X3))) )),
% 2.12/0.63    inference(resolution,[],[f59,f54])).
% 2.12/0.63  fof(f54,plain,(
% 2.12/0.63    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.12/0.63    inference(cnf_transformation,[],[f36])).
% 2.12/0.63  fof(f36,plain,(
% 2.12/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.12/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).
% 2.12/0.63  fof(f35,plain,(
% 2.12/0.63    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.12/0.63    introduced(choice_axiom,[])).
% 2.12/0.63  fof(f34,plain,(
% 2.12/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.12/0.63    inference(rectify,[],[f33])).
% 2.12/0.63  fof(f33,plain,(
% 2.12/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.12/0.63    inference(nnf_transformation,[],[f17])).
% 2.12/0.63  fof(f17,plain,(
% 2.12/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.12/0.63    inference(ennf_transformation,[],[f1])).
% 2.12/0.63  fof(f1,axiom,(
% 2.12/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.12/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.12/0.63  fof(f59,plain,(
% 2.12/0.63    ( ! [X2,X0,X1] : (r2_hidden(X0,k10_relat_1(X1,X2)) | ~sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 2.12/0.63    inference(cnf_transformation,[],[f38])).
% 2.12/0.63  fof(f38,plain,(
% 2.12/0.63    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X1,X2)) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X0,k10_relat_1(X1,X2)))) | ~sP1(X0,X1,X2))),
% 2.12/0.63    inference(rectify,[],[f37])).
% 2.12/0.63  fof(f37,plain,(
% 2.12/0.63    ! [X0,X2,X1] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~sP1(X0,X2,X1))),
% 2.12/0.63    inference(nnf_transformation,[],[f26])).
% 2.12/0.63  fof(f252,plain,(
% 2.12/0.63    ( ! [X2,X0,X1] : (sP0(X0,X1,sK4(k10_relat_1(X1,X0),X2)) | r1_tarski(k10_relat_1(X1,X0),X2) | ~v1_relat_1(X1)) )),
% 2.12/0.63    inference(resolution,[],[f87,f64])).
% 2.12/0.63  fof(f87,plain,(
% 2.12/0.63    ( ! [X2,X0,X1] : (~sP1(sK4(k10_relat_1(X1,X0),X2),X1,X0) | sP0(X0,X1,sK4(k10_relat_1(X1,X0),X2)) | r1_tarski(k10_relat_1(X1,X0),X2)) )),
% 2.12/0.63    inference(resolution,[],[f58,f53])).
% 2.12/0.63  fof(f53,plain,(
% 2.12/0.63    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.12/0.63    inference(cnf_transformation,[],[f36])).
% 2.12/0.63  fof(f58,plain,(
% 2.12/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X1,X2)) | sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 2.12/0.63    inference(cnf_transformation,[],[f38])).
% 2.12/0.63  fof(f1520,plain,(
% 2.12/0.63    ( ! [X10,X11] : (~v1_relat_1(X10) | ~v1_relat_1(X11) | k1_relat_1(k5_relat_1(X10,X11)) = k10_relat_1(X10,k1_relat_1(X11)) | ~r1_tarski(k10_relat_1(X10,k1_relat_1(X11)),k1_relat_1(k5_relat_1(X10,X11)))) )),
% 2.12/0.63    inference(resolution,[],[f1484,f51])).
% 2.12/0.63  fof(f51,plain,(
% 2.12/0.63    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.12/0.63    inference(cnf_transformation,[],[f32])).
% 2.12/0.63  fof(f32,plain,(
% 2.12/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.12/0.63    inference(flattening,[],[f31])).
% 2.12/0.63  fof(f31,plain,(
% 2.12/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.12/0.63    inference(nnf_transformation,[],[f2])).
% 2.12/0.63  fof(f2,axiom,(
% 2.12/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.12/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.12/0.63  fof(f1484,plain,(
% 2.12/0.63    ( ! [X8,X7] : (r1_tarski(k1_relat_1(k5_relat_1(X7,X8)),k10_relat_1(X7,k1_relat_1(X8))) | ~v1_relat_1(X7) | ~v1_relat_1(X8)) )),
% 2.12/0.63    inference(duplicate_literal_removal,[],[f1466])).
% 2.12/0.63  fof(f1466,plain,(
% 2.12/0.63    ( ! [X8,X7] : (r1_tarski(k1_relat_1(k5_relat_1(X7,X8)),k10_relat_1(X7,k1_relat_1(X8))) | ~v1_relat_1(X7) | ~v1_relat_1(X8) | ~v1_relat_1(X8)) )),
% 2.12/0.63    inference(resolution,[],[f180,f604])).
% 2.12/0.63  fof(f180,plain,(
% 2.12/0.63    ( ! [X4,X5,X3] : (~r1_tarski(k10_relat_1(X4,k2_relat_1(k5_relat_1(X3,X4))),X5) | r1_tarski(k1_relat_1(k5_relat_1(X3,X4)),k10_relat_1(X3,X5)) | ~v1_relat_1(X3) | ~v1_relat_1(X4)) )),
% 2.12/0.63    inference(duplicate_literal_removal,[],[f169])).
% 2.12/0.63  fof(f169,plain,(
% 2.12/0.63    ( ! [X4,X5,X3] : (r1_tarski(k1_relat_1(k5_relat_1(X3,X4)),k10_relat_1(X3,X5)) | ~r1_tarski(k10_relat_1(X4,k2_relat_1(k5_relat_1(X3,X4))),X5) | ~v1_relat_1(X3) | ~v1_relat_1(X4) | ~v1_relat_1(X3)) )),
% 2.12/0.63    inference(superposition,[],[f55,f108])).
% 2.12/0.63  fof(f108,plain,(
% 2.12/0.63    ( ! [X4,X3] : (k1_relat_1(k5_relat_1(X3,X4)) = k10_relat_1(X3,k10_relat_1(X4,k2_relat_1(k5_relat_1(X3,X4)))) | ~v1_relat_1(X4) | ~v1_relat_1(X3)) )),
% 2.12/0.63    inference(subsumption_resolution,[],[f102,f48])).
% 2.12/0.63  fof(f102,plain,(
% 2.12/0.63    ( ! [X4,X3] : (k1_relat_1(k5_relat_1(X3,X4)) = k10_relat_1(X3,k10_relat_1(X4,k2_relat_1(k5_relat_1(X3,X4)))) | ~v1_relat_1(X4) | ~v1_relat_1(X3) | ~v1_relat_1(k5_relat_1(X3,X4))) )),
% 2.12/0.63    inference(superposition,[],[f47,f46])).
% 2.12/0.63  fof(f55,plain,(
% 2.12/0.63    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 2.12/0.63    inference(cnf_transformation,[],[f19])).
% 2.12/0.63  fof(f19,plain,(
% 2.12/0.63    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 2.12/0.63    inference(flattening,[],[f18])).
% 2.12/0.63  fof(f18,plain,(
% 2.12/0.63    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 2.12/0.63    inference(ennf_transformation,[],[f7])).
% 2.12/0.63  fof(f7,axiom,(
% 2.12/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 2.12/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).
% 2.12/0.63  fof(f45,plain,(
% 2.12/0.63    k1_relat_1(k5_relat_1(sK2,sK3)) != k10_relat_1(sK2,k1_relat_1(sK3))),
% 2.12/0.63    inference(cnf_transformation,[],[f30])).
% 2.12/0.63  fof(f30,plain,(
% 2.12/0.63    (k1_relat_1(k5_relat_1(sK2,sK3)) != k10_relat_1(sK2,k1_relat_1(sK3)) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 2.12/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f12,f29,f28])).
% 2.12/0.63  fof(f28,plain,(
% 2.12/0.63    ? [X0] : (? [X1] : (k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (k1_relat_1(k5_relat_1(sK2,X1)) != k10_relat_1(sK2,k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK2))),
% 2.12/0.63    introduced(choice_axiom,[])).
% 2.12/0.63  fof(f29,plain,(
% 2.12/0.63    ? [X1] : (k1_relat_1(k5_relat_1(sK2,X1)) != k10_relat_1(sK2,k1_relat_1(X1)) & v1_relat_1(X1)) => (k1_relat_1(k5_relat_1(sK2,sK3)) != k10_relat_1(sK2,k1_relat_1(sK3)) & v1_relat_1(sK3))),
% 2.12/0.63    introduced(choice_axiom,[])).
% 2.12/0.63  fof(f12,plain,(
% 2.12/0.63    ? [X0] : (? [X1] : (k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.12/0.63    inference(ennf_transformation,[],[f11])).
% 2.12/0.63  fof(f11,negated_conjecture,(
% 2.12/0.63    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.12/0.63    inference(negated_conjecture,[],[f10])).
% 2.12/0.63  fof(f10,conjecture,(
% 2.12/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.12/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 2.12/0.63  fof(f44,plain,(
% 2.12/0.63    v1_relat_1(sK3)),
% 2.12/0.63    inference(cnf_transformation,[],[f30])).
% 2.12/0.63  fof(f43,plain,(
% 2.12/0.63    v1_relat_1(sK2)),
% 2.12/0.63    inference(cnf_transformation,[],[f30])).
% 2.12/0.63  % SZS output end Proof for theBenchmark
% 2.12/0.63  % (23258)------------------------------
% 2.12/0.63  % (23258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.63  % (23258)Termination reason: Refutation
% 2.12/0.63  
% 2.12/0.63  % (23258)Memory used [KB]: 2686
% 2.12/0.63  % (23258)Time elapsed: 0.215 s
% 2.12/0.63  % (23258)------------------------------
% 2.12/0.63  % (23258)------------------------------
% 2.12/0.63  % (23223)Success in time 0.275 s
%------------------------------------------------------------------------------
