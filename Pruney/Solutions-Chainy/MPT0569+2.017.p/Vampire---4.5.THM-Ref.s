%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:28 EST 2020

% Result     : Theorem 1.69s
% Output     : Refutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 338 expanded)
%              Number of leaves         :   18 ( 104 expanded)
%              Depth                    :   19
%              Number of atoms          :  355 (1462 expanded)
%              Number of equality atoms :   61 ( 233 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f953,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f70,f743,f952])).

fof(f952,plain,
    ( ~ spl9_1
    | spl9_2 ),
    inference(avatar_contradiction_clause,[],[f951])).

fof(f951,plain,
    ( $false
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f950,f66])).

fof(f66,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl9_2
  <=> r1_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f950,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl9_1 ),
    inference(duplicate_literal_removal,[],[f948])).

fof(f948,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl9_1 ),
    inference(resolution,[],[f782,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f13,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f782,plain,
    ( ! [X20] :
        ( ~ r2_hidden(sK5(k2_relat_1(sK1),X20),sK0)
        | r1_xboole_0(k2_relat_1(sK1),X20) )
    | ~ spl9_1 ),
    inference(resolution,[],[f764,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f764,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK1))
        | ~ r2_hidden(X0,sK0) )
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f763,f34])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
      | k1_xboole_0 != k10_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k2_relat_1(sK1),sK0)
      | k1_xboole_0 = k10_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
        | k1_xboole_0 != k10_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k2_relat_1(sK1),sK0)
        | k1_xboole_0 = k10_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f763,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f752,f223])).

fof(f223,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f222,f104])).

fof(f104,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f95,f73])).

fof(f73,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f51,f39])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f95,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f74,f47])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X1,X2),X0)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f48,f46])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f222,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ) ),
    inference(superposition,[],[f130,f38])).

fof(f38,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_relat_1(X0))
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | ~ r2_hidden(X1,k2_relat_1(X0))
      | ~ r2_hidden(X1,k2_relat_1(X0)) ) ),
    inference(resolution,[],[f77,f60])).

fof(f60,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f29,f32,f31,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f77,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(k4_tarski(sK8(X3,X2),X2),X4)
      | ~ r1_xboole_0(X4,X3)
      | ~ r2_hidden(X2,k2_relat_1(X3)) ) ),
    inference(resolution,[],[f60,f48])).

fof(f752,plain,
    ( ! [X0] :
        ( r2_hidden(sK8(sK1,X0),k1_xboole_0)
        | ~ r2_hidden(X0,sK0)
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl9_1 ),
    inference(superposition,[],[f88,f68])).

fof(f68,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl9_1
  <=> k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X2,X0),k10_relat_1(X2,X1))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k2_relat_1(X2)) ) ),
    inference(resolution,[],[f56,f60])).

fof(f56,plain,(
    ! [X6,X0,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ r2_hidden(X7,X1)
      | r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK2(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK3(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) )
                | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK4(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f23,f22,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK4(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(f743,plain,
    ( spl9_1
    | ~ spl9_2 ),
    inference(avatar_contradiction_clause,[],[f742])).

fof(f742,plain,
    ( $false
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f741,f34])).

fof(f741,plain,
    ( ~ v1_relat_1(sK1)
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f708,f73])).

fof(f708,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),k1_xboole_0)
    | ~ v1_relat_1(sK1)
    | spl9_1
    | ~ spl9_2 ),
    inference(trivial_inequality_removal,[],[f677])).

fof(f677,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(sK1),k1_xboole_0)
    | ~ v1_relat_1(sK1)
    | spl9_1
    | ~ spl9_2 ),
    inference(superposition,[],[f132,f654])).

fof(f654,plain,(
    ! [X10] :
      ( k1_xboole_0 = k10_relat_1(X10,k1_xboole_0)
      | ~ v1_relat_1(X10) ) ),
    inference(resolution,[],[f281,f277])).

fof(f277,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X8,k10_relat_1(X9,k1_xboole_0))
      | ~ v1_relat_1(X9) ) ),
    inference(resolution,[],[f223,f57])).

fof(f57,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f281,plain,(
    ! [X1] :
      ( r2_hidden(sK6(k1_xboole_0,X1),X1)
      | k1_xboole_0 = X1 ) ),
    inference(forward_demodulation,[],[f273,f38])).

fof(f273,plain,(
    ! [X1] :
      ( k2_relat_1(k1_xboole_0) = X1
      | r2_hidden(sK6(k1_xboole_0,X1),X1) ) ),
    inference(resolution,[],[f223,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
      | k2_relat_1(X0) = X1
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f132,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k10_relat_1(sK1,X0)
        | ~ r1_xboole_0(k2_relat_1(sK1),X0) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f131,f34])).

fof(f131,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k10_relat_1(sK1,X0)
        | ~ v1_relat_1(sK1)
        | ~ r1_xboole_0(k2_relat_1(sK1),X0) )
    | spl9_1
    | ~ spl9_2 ),
    inference(superposition,[],[f128,f79])).

fof(f79,plain,(
    ! [X2,X1] :
      ( k10_relat_1(X1,X2) = k10_relat_1(X1,k1_xboole_0)
      | ~ v1_relat_1(X1)
      | ~ r1_xboole_0(k2_relat_1(X1),X2) ) ),
    inference(superposition,[],[f49,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f128,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_xboole_0)
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f127,f69])).

fof(f69,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f127,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_xboole_0)
    | ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f122,f34])).

fof(f122,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_xboole_0)
    | ~ v1_relat_1(sK1)
    | ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | spl9_1 ),
    inference(superposition,[],[f63,f79])).

fof(f63,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,sK0)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f70,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f35,f65,f62])).

fof(f35,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f36,f65,f62])).

fof(f36,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 != k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:37:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.43  % (32016)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (32018)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.52  % (32013)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.52  % (32010)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.53  % (32004)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (32006)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.53  % (32009)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.54  % (32005)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (32005)Refutation not found, incomplete strategy% (32005)------------------------------
% 0.20/0.54  % (32005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (32005)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (32005)Memory used [KB]: 10618
% 0.20/0.54  % (32005)Time elapsed: 0.109 s
% 0.20/0.54  % (32005)------------------------------
% 0.20/0.54  % (32005)------------------------------
% 0.20/0.54  % (32017)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.54  % (32015)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.54  % (32015)Refutation not found, incomplete strategy% (32015)------------------------------
% 0.20/0.54  % (32015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (32015)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (32015)Memory used [KB]: 10618
% 0.20/0.54  % (32015)Time elapsed: 0.122 s
% 0.20/0.54  % (32015)------------------------------
% 0.20/0.54  % (32015)------------------------------
% 0.20/0.55  % (32014)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.56  % (32024)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.56  % (32020)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.56  % (32008)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.56  % (32011)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.56  % (32012)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.57  % (32019)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.57  % (32007)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.57  % (32024)Refutation not found, incomplete strategy% (32024)------------------------------
% 0.20/0.57  % (32024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (32024)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (32024)Memory used [KB]: 10618
% 0.20/0.57  % (32024)Time elapsed: 0.151 s
% 0.20/0.57  % (32024)------------------------------
% 0.20/0.57  % (32024)------------------------------
% 1.69/0.58  % (32021)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.69/0.58  % (32006)Refutation found. Thanks to Tanya!
% 1.69/0.58  % SZS status Theorem for theBenchmark
% 1.69/0.58  % SZS output start Proof for theBenchmark
% 1.69/0.58  fof(f953,plain,(
% 1.69/0.58    $false),
% 1.69/0.58    inference(avatar_sat_refutation,[],[f67,f70,f743,f952])).
% 1.69/0.58  fof(f952,plain,(
% 1.69/0.58    ~spl9_1 | spl9_2),
% 1.69/0.58    inference(avatar_contradiction_clause,[],[f951])).
% 1.69/0.58  fof(f951,plain,(
% 1.69/0.58    $false | (~spl9_1 | spl9_2)),
% 1.69/0.58    inference(subsumption_resolution,[],[f950,f66])).
% 1.69/0.58  fof(f66,plain,(
% 1.69/0.58    ~r1_xboole_0(k2_relat_1(sK1),sK0) | spl9_2),
% 1.69/0.58    inference(avatar_component_clause,[],[f65])).
% 1.69/0.58  fof(f65,plain,(
% 1.69/0.58    spl9_2 <=> r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.69/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.69/0.58  fof(f950,plain,(
% 1.69/0.58    r1_xboole_0(k2_relat_1(sK1),sK0) | ~spl9_1),
% 1.69/0.58    inference(duplicate_literal_removal,[],[f948])).
% 1.69/0.58  fof(f948,plain,(
% 1.69/0.58    r1_xboole_0(k2_relat_1(sK1),sK0) | r1_xboole_0(k2_relat_1(sK1),sK0) | ~spl9_1),
% 1.69/0.58    inference(resolution,[],[f782,f47])).
% 1.69/0.58  fof(f47,plain,(
% 1.69/0.58    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f26])).
% 1.69/0.58  fof(f26,plain,(
% 1.69/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.69/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f13,f25])).
% 1.69/0.58  fof(f25,plain,(
% 1.69/0.58    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.69/0.58    introduced(choice_axiom,[])).
% 1.69/0.58  fof(f13,plain,(
% 1.69/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.69/0.58    inference(ennf_transformation,[],[f10])).
% 1.69/0.58  fof(f10,plain,(
% 1.69/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.69/0.58    inference(rectify,[],[f2])).
% 1.69/0.58  fof(f2,axiom,(
% 1.69/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.69/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.69/0.58  fof(f782,plain,(
% 1.69/0.58    ( ! [X20] : (~r2_hidden(sK5(k2_relat_1(sK1),X20),sK0) | r1_xboole_0(k2_relat_1(sK1),X20)) ) | ~spl9_1),
% 1.69/0.58    inference(resolution,[],[f764,f46])).
% 1.69/0.58  fof(f46,plain,(
% 1.69/0.58    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f26])).
% 1.69/0.58  fof(f764,plain,(
% 1.69/0.58    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | ~r2_hidden(X0,sK0)) ) | ~spl9_1),
% 1.69/0.58    inference(subsumption_resolution,[],[f763,f34])).
% 1.69/0.58  fof(f34,plain,(
% 1.69/0.58    v1_relat_1(sK1)),
% 1.69/0.58    inference(cnf_transformation,[],[f18])).
% 1.69/0.58  fof(f18,plain,(
% 1.69/0.58    (~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)) & (r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 1.69/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).
% 1.69/0.58  fof(f17,plain,(
% 1.69/0.58    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)) & (r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 1.69/0.58    introduced(choice_axiom,[])).
% 1.69/0.58  fof(f16,plain,(
% 1.69/0.58    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 1.69/0.58    inference(flattening,[],[f15])).
% 1.69/0.58  fof(f15,plain,(
% 1.69/0.58    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 1.69/0.58    inference(nnf_transformation,[],[f11])).
% 1.69/0.58  fof(f11,plain,(
% 1.69/0.58    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.69/0.58    inference(ennf_transformation,[],[f9])).
% 1.69/0.58  fof(f9,negated_conjecture,(
% 1.69/0.58    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.69/0.58    inference(negated_conjecture,[],[f8])).
% 1.69/0.58  fof(f8,conjecture,(
% 1.69/0.58    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.69/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 1.69/0.58  fof(f763,plain,(
% 1.69/0.58    ( ! [X0] : (~r2_hidden(X0,sK0) | ~v1_relat_1(sK1) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | ~spl9_1),
% 1.69/0.58    inference(subsumption_resolution,[],[f752,f223])).
% 1.69/0.58  fof(f223,plain,(
% 1.69/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.69/0.58    inference(subsumption_resolution,[],[f222,f104])).
% 1.69/0.58  fof(f104,plain,(
% 1.69/0.58    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.69/0.58    inference(resolution,[],[f95,f73])).
% 1.69/0.58  fof(f73,plain,(
% 1.69/0.58    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.69/0.58    inference(trivial_inequality_removal,[],[f71])).
% 1.69/0.58  fof(f71,plain,(
% 1.69/0.58    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(X0,k1_xboole_0)) )),
% 1.69/0.58    inference(superposition,[],[f51,f39])).
% 1.69/0.58  fof(f39,plain,(
% 1.69/0.58    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f3])).
% 1.69/0.58  fof(f3,axiom,(
% 1.69/0.58    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.69/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.69/0.58  fof(f51,plain,(
% 1.69/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f27])).
% 1.69/0.58  fof(f27,plain,(
% 1.69/0.58    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.69/0.58    inference(nnf_transformation,[],[f1])).
% 1.69/0.58  fof(f1,axiom,(
% 1.69/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.69/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.69/0.58  fof(f95,plain,(
% 1.69/0.58    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2)) )),
% 1.69/0.58    inference(duplicate_literal_removal,[],[f94])).
% 1.69/0.58  fof(f94,plain,(
% 1.69/0.58    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2) | r1_xboole_0(X3,X2)) )),
% 1.69/0.58    inference(resolution,[],[f74,f47])).
% 1.69/0.58  fof(f74,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X1,X2),X0) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X2)) )),
% 1.69/0.58    inference(resolution,[],[f48,f46])).
% 1.69/0.58  fof(f48,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f26])).
% 1.69/0.58  fof(f222,plain,(
% 1.69/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 1.69/0.58    inference(superposition,[],[f130,f38])).
% 1.69/0.58  fof(f38,plain,(
% 1.69/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.69/0.58    inference(cnf_transformation,[],[f7])).
% 1.69/0.58  fof(f7,axiom,(
% 1.69/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.69/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.69/0.58  fof(f130,plain,(
% 1.69/0.58    ( ! [X0,X1] : (~r2_hidden(X1,k2_relat_1(X0)) | ~r1_xboole_0(X0,X0)) )),
% 1.69/0.58    inference(duplicate_literal_removal,[],[f129])).
% 1.69/0.58  fof(f129,plain,(
% 1.69/0.58    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | ~r2_hidden(X1,k2_relat_1(X0)) | ~r2_hidden(X1,k2_relat_1(X0))) )),
% 1.69/0.58    inference(resolution,[],[f77,f60])).
% 1.69/0.58  fof(f60,plain,(
% 1.69/0.58    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 1.69/0.58    inference(equality_resolution,[],[f52])).
% 1.69/0.58  fof(f52,plain,(
% 1.69/0.58    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 1.69/0.58    inference(cnf_transformation,[],[f33])).
% 1.69/0.58  fof(f33,plain,(
% 1.69/0.58    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.69/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f29,f32,f31,f30])).
% 1.69/0.58  fof(f30,plain,(
% 1.69/0.58    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 1.69/0.58    introduced(choice_axiom,[])).
% 1.69/0.58  fof(f31,plain,(
% 1.69/0.58    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0) => r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0))),
% 1.69/0.58    introduced(choice_axiom,[])).
% 1.69/0.58  fof(f32,plain,(
% 1.69/0.58    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0))),
% 1.69/0.58    introduced(choice_axiom,[])).
% 1.69/0.58  fof(f29,plain,(
% 1.69/0.58    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.69/0.58    inference(rectify,[],[f28])).
% 1.69/0.58  fof(f28,plain,(
% 1.69/0.58    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 1.69/0.58    inference(nnf_transformation,[],[f5])).
% 1.69/0.58  fof(f5,axiom,(
% 1.69/0.58    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.69/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 1.69/0.58  fof(f77,plain,(
% 1.69/0.58    ( ! [X4,X2,X3] : (~r2_hidden(k4_tarski(sK8(X3,X2),X2),X4) | ~r1_xboole_0(X4,X3) | ~r2_hidden(X2,k2_relat_1(X3))) )),
% 1.69/0.58    inference(resolution,[],[f60,f48])).
% 1.69/0.58  fof(f752,plain,(
% 1.69/0.58    ( ! [X0] : (r2_hidden(sK8(sK1,X0),k1_xboole_0) | ~r2_hidden(X0,sK0) | ~v1_relat_1(sK1) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | ~spl9_1),
% 1.69/0.58    inference(superposition,[],[f88,f68])).
% 1.69/0.58  fof(f68,plain,(
% 1.69/0.58    k1_xboole_0 = k10_relat_1(sK1,sK0) | ~spl9_1),
% 1.69/0.58    inference(avatar_component_clause,[],[f62])).
% 1.69/0.58  fof(f62,plain,(
% 1.69/0.58    spl9_1 <=> k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.69/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.69/0.58  fof(f88,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (r2_hidden(sK8(X2,X0),k10_relat_1(X2,X1)) | ~r2_hidden(X0,X1) | ~v1_relat_1(X2) | ~r2_hidden(X0,k2_relat_1(X2))) )),
% 1.69/0.58    inference(resolution,[],[f56,f60])).
% 1.69/0.58  fof(f56,plain,(
% 1.69/0.58    ( ! [X6,X0,X7,X1] : (~r2_hidden(k4_tarski(X6,X7),X0) | ~r2_hidden(X7,X1) | r2_hidden(X6,k10_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.69/0.58    inference(equality_resolution,[],[f42])).
% 1.69/0.58  fof(f42,plain,(
% 1.69/0.58    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f24])).
% 1.69/0.58  fof(f24,plain,(
% 1.69/0.58    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.69/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f23,f22,f21])).
% 1.69/0.58  fof(f21,plain,(
% 1.69/0.58    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.69/0.58    introduced(choice_axiom,[])).
% 1.69/0.58  fof(f22,plain,(
% 1.69/0.58    ! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)))),
% 1.69/0.58    introduced(choice_axiom,[])).
% 1.69/0.58  fof(f23,plain,(
% 1.69/0.58    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0)))),
% 1.69/0.58    introduced(choice_axiom,[])).
% 1.69/0.58  fof(f20,plain,(
% 1.69/0.58    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.69/0.58    inference(rectify,[],[f19])).
% 1.69/0.58  fof(f19,plain,(
% 1.69/0.58    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.69/0.58    inference(nnf_transformation,[],[f12])).
% 1.69/0.58  fof(f12,plain,(
% 1.69/0.58    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 1.69/0.58    inference(ennf_transformation,[],[f4])).
% 1.69/0.58  fof(f4,axiom,(
% 1.69/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 1.69/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).
% 1.69/0.58  fof(f743,plain,(
% 1.69/0.58    spl9_1 | ~spl9_2),
% 1.69/0.58    inference(avatar_contradiction_clause,[],[f742])).
% 1.69/0.58  fof(f742,plain,(
% 1.69/0.58    $false | (spl9_1 | ~spl9_2)),
% 1.69/0.58    inference(subsumption_resolution,[],[f741,f34])).
% 1.69/0.58  fof(f741,plain,(
% 1.69/0.58    ~v1_relat_1(sK1) | (spl9_1 | ~spl9_2)),
% 1.69/0.58    inference(subsumption_resolution,[],[f708,f73])).
% 1.69/0.58  fof(f708,plain,(
% 1.69/0.58    ~r1_xboole_0(k2_relat_1(sK1),k1_xboole_0) | ~v1_relat_1(sK1) | (spl9_1 | ~spl9_2)),
% 1.69/0.58    inference(trivial_inequality_removal,[],[f677])).
% 1.69/0.58  fof(f677,plain,(
% 1.69/0.58    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k2_relat_1(sK1),k1_xboole_0) | ~v1_relat_1(sK1) | (spl9_1 | ~spl9_2)),
% 1.69/0.58    inference(superposition,[],[f132,f654])).
% 1.69/0.58  fof(f654,plain,(
% 1.69/0.58    ( ! [X10] : (k1_xboole_0 = k10_relat_1(X10,k1_xboole_0) | ~v1_relat_1(X10)) )),
% 1.69/0.58    inference(resolution,[],[f281,f277])).
% 1.69/0.58  fof(f277,plain,(
% 1.69/0.58    ( ! [X8,X9] : (~r2_hidden(X8,k10_relat_1(X9,k1_xboole_0)) | ~v1_relat_1(X9)) )),
% 1.69/0.58    inference(resolution,[],[f223,f57])).
% 1.69/0.58  fof(f57,plain,(
% 1.69/0.58    ( ! [X6,X0,X1] : (r2_hidden(sK4(X0,X1,X6),X1) | ~r2_hidden(X6,k10_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.69/0.58    inference(equality_resolution,[],[f41])).
% 1.69/0.58  fof(f41,plain,(
% 1.69/0.58    ( ! [X6,X2,X0,X1] : (r2_hidden(sK4(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f24])).
% 1.69/0.58  fof(f281,plain,(
% 1.69/0.58    ( ! [X1] : (r2_hidden(sK6(k1_xboole_0,X1),X1) | k1_xboole_0 = X1) )),
% 1.69/0.58    inference(forward_demodulation,[],[f273,f38])).
% 1.69/0.58  fof(f273,plain,(
% 1.69/0.58    ( ! [X1] : (k2_relat_1(k1_xboole_0) = X1 | r2_hidden(sK6(k1_xboole_0,X1),X1)) )),
% 1.69/0.58    inference(resolution,[],[f223,f54])).
% 1.69/0.58  fof(f54,plain,(
% 1.69/0.58    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | k2_relat_1(X0) = X1 | r2_hidden(sK6(X0,X1),X1)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f33])).
% 1.69/0.58  fof(f132,plain,(
% 1.69/0.58    ( ! [X0] : (k1_xboole_0 != k10_relat_1(sK1,X0) | ~r1_xboole_0(k2_relat_1(sK1),X0)) ) | (spl9_1 | ~spl9_2)),
% 1.69/0.58    inference(subsumption_resolution,[],[f131,f34])).
% 1.69/0.58  fof(f131,plain,(
% 1.69/0.58    ( ! [X0] : (k1_xboole_0 != k10_relat_1(sK1,X0) | ~v1_relat_1(sK1) | ~r1_xboole_0(k2_relat_1(sK1),X0)) ) | (spl9_1 | ~spl9_2)),
% 1.69/0.58    inference(superposition,[],[f128,f79])).
% 1.69/0.58  fof(f79,plain,(
% 1.69/0.58    ( ! [X2,X1] : (k10_relat_1(X1,X2) = k10_relat_1(X1,k1_xboole_0) | ~v1_relat_1(X1) | ~r1_xboole_0(k2_relat_1(X1),X2)) )),
% 1.69/0.58    inference(superposition,[],[f49,f50])).
% 1.69/0.58  fof(f50,plain,(
% 1.69/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f27])).
% 1.69/0.58  fof(f49,plain,(
% 1.69/0.58    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f14])).
% 1.69/0.58  fof(f14,plain,(
% 1.69/0.58    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.69/0.58    inference(ennf_transformation,[],[f6])).
% 1.69/0.58  fof(f6,axiom,(
% 1.69/0.58    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 1.69/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 1.69/0.58  fof(f128,plain,(
% 1.69/0.58    k1_xboole_0 != k10_relat_1(sK1,k1_xboole_0) | (spl9_1 | ~spl9_2)),
% 1.69/0.58    inference(subsumption_resolution,[],[f127,f69])).
% 1.69/0.58  fof(f69,plain,(
% 1.69/0.58    r1_xboole_0(k2_relat_1(sK1),sK0) | ~spl9_2),
% 1.69/0.58    inference(avatar_component_clause,[],[f65])).
% 1.69/0.58  fof(f127,plain,(
% 1.69/0.58    k1_xboole_0 != k10_relat_1(sK1,k1_xboole_0) | ~r1_xboole_0(k2_relat_1(sK1),sK0) | spl9_1),
% 1.69/0.58    inference(subsumption_resolution,[],[f122,f34])).
% 1.69/0.58  fof(f122,plain,(
% 1.69/0.58    k1_xboole_0 != k10_relat_1(sK1,k1_xboole_0) | ~v1_relat_1(sK1) | ~r1_xboole_0(k2_relat_1(sK1),sK0) | spl9_1),
% 1.69/0.58    inference(superposition,[],[f63,f79])).
% 1.69/0.58  fof(f63,plain,(
% 1.69/0.58    k1_xboole_0 != k10_relat_1(sK1,sK0) | spl9_1),
% 1.69/0.58    inference(avatar_component_clause,[],[f62])).
% 1.69/0.58  fof(f70,plain,(
% 1.69/0.58    spl9_1 | spl9_2),
% 1.69/0.58    inference(avatar_split_clause,[],[f35,f65,f62])).
% 1.69/0.58  fof(f35,plain,(
% 1.69/0.58    r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.69/0.58    inference(cnf_transformation,[],[f18])).
% 1.69/0.58  fof(f67,plain,(
% 1.69/0.58    ~spl9_1 | ~spl9_2),
% 1.69/0.58    inference(avatar_split_clause,[],[f36,f65,f62])).
% 1.69/0.58  fof(f36,plain,(
% 1.69/0.58    ~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)),
% 1.69/0.58    inference(cnf_transformation,[],[f18])).
% 1.69/0.58  % SZS output end Proof for theBenchmark
% 1.69/0.58  % (32006)------------------------------
% 1.69/0.58  % (32006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.58  % (32006)Termination reason: Refutation
% 1.69/0.58  
% 1.69/0.58  % (32006)Memory used [KB]: 11129
% 1.69/0.58  % (32006)Time elapsed: 0.146 s
% 1.69/0.58  % (32006)------------------------------
% 1.69/0.58  % (32006)------------------------------
% 1.69/0.58  % (32003)Success in time 0.216 s
%------------------------------------------------------------------------------
