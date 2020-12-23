%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 129 expanded)
%              Number of leaves         :   15 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :  283 ( 540 expanded)
%              Number of equality atoms :   43 ( 103 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f745,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f684,f741])).

fof(f741,plain,(
    spl9_25 ),
    inference(avatar_contradiction_clause,[],[f740])).

fof(f740,plain,
    ( $false
    | spl9_25 ),
    inference(subsumption_resolution,[],[f739,f31])).

fof(f31,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k2_relat_1(sK0) != k9_relat_1(sK0,k1_relat_1(sK0))
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( k2_relat_1(X0) != k9_relat_1(X0,k1_relat_1(X0))
        & v1_relat_1(X0) )
   => ( k2_relat_1(sK0) != k9_relat_1(sK0,k1_relat_1(sK0))
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( k2_relat_1(X0) != k9_relat_1(X0,k1_relat_1(X0))
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f739,plain,
    ( ~ v1_relat_1(sK0)
    | spl9_25 ),
    inference(subsumption_resolution,[],[f738,f659])).

fof(f659,plain,
    ( ~ r2_hidden(sK4(sK0,k1_relat_1(sK0),k2_relat_1(sK0)),k2_relat_1(sK0))
    | spl9_25 ),
    inference(avatar_component_clause,[],[f658])).

fof(f658,plain,
    ( spl9_25
  <=> r2_hidden(sK4(sK0,k1_relat_1(sK0),k2_relat_1(sK0)),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f738,plain,
    ( r2_hidden(sK4(sK0,k1_relat_1(sK0),k2_relat_1(sK0)),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl9_25 ),
    inference(subsumption_resolution,[],[f730,f32])).

fof(f32,plain,(
    k2_relat_1(sK0) != k9_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f730,plain,
    ( k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))
    | r2_hidden(sK4(sK0,k1_relat_1(sK0),k2_relat_1(sK0)),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl9_25 ),
    inference(resolution,[],[f691,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK4(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK4(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK5(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X0) )
                | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK6(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK6(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f22,f25,f24,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X4,X3),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X3),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(X4,sK4(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X0) )
     => ( r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK6(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK6(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X5,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X8,X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

fof(f691,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK4(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),sK0)
    | spl9_25 ),
    inference(resolution,[],[f659,f50])).

fof(f50,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f16,f19,f18,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f684,plain,(
    ~ spl9_25 ),
    inference(avatar_contradiction_clause,[],[f683])).

fof(f683,plain,
    ( $false
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f677,f660])).

fof(f660,plain,
    ( r2_hidden(sK4(sK0,k1_relat_1(sK0),k2_relat_1(sK0)),k2_relat_1(sK0))
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f658])).

fof(f677,plain,
    ( ~ r2_hidden(sK4(sK0,k1_relat_1(sK0),k2_relat_1(sK0)),k2_relat_1(sK0))
    | ~ spl9_25 ),
    inference(resolution,[],[f675,f51])).

fof(f51,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f675,plain,
    ( ! [X5] : ~ r2_hidden(k4_tarski(X5,sK4(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),sK0)
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f674,f514])).

fof(f514,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK0)
      | r2_hidden(X0,k1_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f513,f31])).

fof(f513,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(sK0))
      | ~ r2_hidden(k4_tarski(X0,X1),sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f503,f66])).

fof(f66,plain,(
    v1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f31,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f503,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(sK0))
      | ~ r2_hidden(k4_tarski(X0,X1),sK0)
      | ~ v1_relat_1(k4_relat_1(sK0))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f212,f55])).

fof(f55,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ( ( ~ r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
                  | ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) )
                & ( r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
                  | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X3,X2),X0) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_1)).

fof(f212,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X1),k4_relat_1(sK0))
      | r2_hidden(X1,k1_relat_1(sK0)) ) ),
    inference(superposition,[],[f50,f65])).

fof(f65,plain,(
    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f31,f48])).

fof(f48,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f674,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k1_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(X5,sK4(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),sK0) )
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f673,f31])).

fof(f673,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k1_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(X5,sK4(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f670,f32])).

fof(f670,plain,
    ( ! [X5] :
        ( k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))
        | ~ r2_hidden(X5,k1_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(X5,sK4(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl9_25 ),
    inference(resolution,[],[f660,f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(k4_tarski(X4,sK4(X0,X1,X2)),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:17:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (22602)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (22598)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (22598)Refutation not found, incomplete strategy% (22598)------------------------------
% 0.22/0.48  % (22598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (22603)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (22598)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (22598)Memory used [KB]: 10618
% 0.22/0.49  % (22598)Time elapsed: 0.061 s
% 0.22/0.49  % (22598)------------------------------
% 0.22/0.49  % (22598)------------------------------
% 0.22/0.49  % (22616)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.49  % (22601)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.49  % (22606)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (22616)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f745,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f684,f741])).
% 0.22/0.50  fof(f741,plain,(
% 0.22/0.50    spl9_25),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f740])).
% 0.22/0.50  fof(f740,plain,(
% 0.22/0.50    $false | spl9_25),
% 0.22/0.50    inference(subsumption_resolution,[],[f739,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    v1_relat_1(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    k2_relat_1(sK0) != k9_relat_1(sK0,k1_relat_1(sK0)) & v1_relat_1(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ? [X0] : (k2_relat_1(X0) != k9_relat_1(X0,k1_relat_1(X0)) & v1_relat_1(X0)) => (k2_relat_1(sK0) != k9_relat_1(sK0,k1_relat_1(sK0)) & v1_relat_1(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f8,plain,(
% 0.22/0.50    ? [X0] : (k2_relat_1(X0) != k9_relat_1(X0,k1_relat_1(X0)) & v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (v1_relat_1(X0) => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)))),
% 0.22/0.50    inference(negated_conjecture,[],[f6])).
% 0.22/0.50  fof(f6,conjecture,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.22/0.50  fof(f739,plain,(
% 0.22/0.50    ~v1_relat_1(sK0) | spl9_25),
% 0.22/0.50    inference(subsumption_resolution,[],[f738,f659])).
% 0.22/0.50  fof(f659,plain,(
% 0.22/0.50    ~r2_hidden(sK4(sK0,k1_relat_1(sK0),k2_relat_1(sK0)),k2_relat_1(sK0)) | spl9_25),
% 0.22/0.50    inference(avatar_component_clause,[],[f658])).
% 0.22/0.50  fof(f658,plain,(
% 0.22/0.50    spl9_25 <=> r2_hidden(sK4(sK0,k1_relat_1(sK0),k2_relat_1(sK0)),k2_relat_1(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 0.22/0.50  fof(f738,plain,(
% 0.22/0.50    r2_hidden(sK4(sK0,k1_relat_1(sK0),k2_relat_1(sK0)),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | spl9_25),
% 0.22/0.50    inference(subsumption_resolution,[],[f730,f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    k2_relat_1(sK0) != k9_relat_1(sK0,k1_relat_1(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f730,plain,(
% 0.22/0.50    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) | r2_hidden(sK4(sK0,k1_relat_1(sK0),k2_relat_1(sK0)),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | spl9_25),
% 0.22/0.50    inference(resolution,[],[f691,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X0) | r2_hidden(sK4(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK4(X0,X1,X2)),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & ((r2_hidden(sK6(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X6),X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f22,f25,f24,f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK4(X0,X1,X2)),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X0)) => (r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) => (r2_hidden(sK6(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X6),X6),X0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(rectify,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).
% 0.22/0.50  fof(f691,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK4(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),sK0)) ) | spl9_25),
% 0.22/0.50    inference(resolution,[],[f659,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f16,f19,f18,f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0) => r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.50    inference(rectify,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.22/0.50  fof(f684,plain,(
% 0.22/0.50    ~spl9_25),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f683])).
% 0.22/0.50  fof(f683,plain,(
% 0.22/0.50    $false | ~spl9_25),
% 0.22/0.50    inference(subsumption_resolution,[],[f677,f660])).
% 0.22/0.50  fof(f660,plain,(
% 0.22/0.50    r2_hidden(sK4(sK0,k1_relat_1(sK0),k2_relat_1(sK0)),k2_relat_1(sK0)) | ~spl9_25),
% 0.22/0.50    inference(avatar_component_clause,[],[f658])).
% 0.22/0.50  fof(f677,plain,(
% 0.22/0.50    ~r2_hidden(sK4(sK0,k1_relat_1(sK0),k2_relat_1(sK0)),k2_relat_1(sK0)) | ~spl9_25),
% 0.22/0.50    inference(resolution,[],[f675,f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 0.22/0.50    inference(equality_resolution,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f675,plain,(
% 0.22/0.50    ( ! [X5] : (~r2_hidden(k4_tarski(X5,sK4(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),sK0)) ) | ~spl9_25),
% 0.22/0.50    inference(subsumption_resolution,[],[f674,f514])).
% 0.22/0.50  fof(f514,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK0) | r2_hidden(X0,k1_relat_1(sK0))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f513,f31])).
% 0.22/0.50  fof(f513,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(sK0)) | ~r2_hidden(k4_tarski(X0,X1),sK0) | ~v1_relat_1(sK0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f503,f66])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    v1_relat_1(k4_relat_1(sK0))),
% 0.22/0.50    inference(resolution,[],[f31,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.22/0.50  fof(f503,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(sK0)) | ~r2_hidden(k4_tarski(X0,X1),sK0) | ~v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f212,f55])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X4),X0) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0) | k4_relat_1(X0) != X1 | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ((~r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0) | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f28,f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1))) => ((~r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0) | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(rectify,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X3,X2),X0)) & (r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_1)).
% 0.22/0.50  fof(f212,plain,(
% 0.22/0.50    ( ! [X2,X1] : (~r2_hidden(k4_tarski(X2,X1),k4_relat_1(sK0)) | r2_hidden(X1,k1_relat_1(sK0))) )),
% 0.22/0.50    inference(superposition,[],[f50,f65])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))),
% 0.22/0.50    inference(resolution,[],[f31,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 0.22/0.50  fof(f674,plain,(
% 0.22/0.50    ( ! [X5] : (~r2_hidden(X5,k1_relat_1(sK0)) | ~r2_hidden(k4_tarski(X5,sK4(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),sK0)) ) | ~spl9_25),
% 0.22/0.50    inference(subsumption_resolution,[],[f673,f31])).
% 0.22/0.50  fof(f673,plain,(
% 0.22/0.50    ( ! [X5] : (~r2_hidden(X5,k1_relat_1(sK0)) | ~r2_hidden(k4_tarski(X5,sK4(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),sK0) | ~v1_relat_1(sK0)) ) | ~spl9_25),
% 0.22/0.50    inference(subsumption_resolution,[],[f670,f32])).
% 0.22/0.50  fof(f670,plain,(
% 0.22/0.50    ( ! [X5] : (k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) | ~r2_hidden(X5,k1_relat_1(sK0)) | ~r2_hidden(k4_tarski(X5,sK4(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),sK0) | ~v1_relat_1(sK0)) ) | ~spl9_25),
% 0.22/0.50    inference(resolution,[],[f660,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X1] : (k9_relat_1(X0,X1) = X2 | ~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK4(X0,X1,X2)),X0) | ~r2_hidden(sK4(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (22616)------------------------------
% 0.22/0.50  % (22616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (22616)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (22616)Memory used [KB]: 6524
% 0.22/0.50  % (22616)Time elapsed: 0.073 s
% 0.22/0.50  % (22616)------------------------------
% 0.22/0.50  % (22616)------------------------------
% 0.22/0.50  % (22611)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (22597)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (22604)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (22599)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (22609)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (22600)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (22612)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (22596)Success in time 0.146 s
%------------------------------------------------------------------------------
