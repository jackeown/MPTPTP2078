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
% DateTime   : Thu Dec  3 12:54:11 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  113 (1032 expanded)
%              Number of leaves         :   16 ( 381 expanded)
%              Depth                    :   32
%              Number of atoms          :  518 (10015 expanded)
%              Number of equality atoms :  139 (4448 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1723,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1722,f41])).

fof(f41,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK2 != sK3
    & k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3)
    & sK0 = k1_relat_1(sK3)
    & sK0 = k1_relat_1(sK2)
    & sK0 = k2_relat_1(sK1)
    & v1_funct_1(sK3)
    & v1_relat_1(sK3)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f17,f16,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( X2 != X3
                & k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
                & k1_relat_1(X3) = X0
                & k1_relat_1(X2) = X0
                & k2_relat_1(X1) = X0
                & v1_funct_1(X3)
                & v1_relat_1(X3) )
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k5_relat_1(sK1,X2) = k5_relat_1(sK1,X3)
              & k1_relat_1(X3) = sK0
              & k1_relat_1(X2) = sK0
              & sK0 = k2_relat_1(sK1)
              & v1_funct_1(X3)
              & v1_relat_1(X3) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( X2 != X3
            & k5_relat_1(sK1,X2) = k5_relat_1(sK1,X3)
            & k1_relat_1(X3) = sK0
            & k1_relat_1(X2) = sK0
            & sK0 = k2_relat_1(sK1)
            & v1_funct_1(X3)
            & v1_relat_1(X3) )
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( sK2 != X3
          & k5_relat_1(sK1,X3) = k5_relat_1(sK1,sK2)
          & k1_relat_1(X3) = sK0
          & sK0 = k1_relat_1(sK2)
          & sK0 = k2_relat_1(sK1)
          & v1_funct_1(X3)
          & v1_relat_1(X3) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X3] :
        ( sK2 != X3
        & k5_relat_1(sK1,X3) = k5_relat_1(sK1,sK2)
        & k1_relat_1(X3) = sK0
        & sK0 = k1_relat_1(sK2)
        & sK0 = k2_relat_1(sK1)
        & v1_funct_1(X3)
        & v1_relat_1(X3) )
   => ( sK2 != sK3
      & k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3)
      & sK0 = k1_relat_1(sK3)
      & sK0 = k1_relat_1(sK2)
      & sK0 = k2_relat_1(sK1)
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
              & k1_relat_1(X3) = X0
              & k1_relat_1(X2) = X0
              & k2_relat_1(X1) = X0
              & v1_funct_1(X3)
              & v1_relat_1(X3) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
              & k1_relat_1(X3) = X0
              & k1_relat_1(X2) = X0
              & k2_relat_1(X1) = X0
              & v1_funct_1(X3)
              & v1_relat_1(X3) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_relat_1(X3) )
               => ( ( k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
                    & k1_relat_1(X3) = X0
                    & k1_relat_1(X2) = X0
                    & k2_relat_1(X1) = X0 )
                 => X2 = X3 ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_relat_1(X3) )
             => ( ( k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
                  & k1_relat_1(X3) = X0
                  & k1_relat_1(X2) = X0
                  & k2_relat_1(X1) = X0 )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_funct_1)).

fof(f1722,plain,(
    ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f1721,f1577])).

fof(f1577,plain,(
    r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK3) ),
    inference(subsumption_resolution,[],[f1569,f984])).

fof(f984,plain,(
    r2_hidden(sK4(sK3,sK2),sK0) ),
    inference(subsumption_resolution,[],[f983,f41])).

fof(f983,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f969,f47])).

fof(f47,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f18])).

fof(f969,plain,
    ( sK2 = sK3
    | r2_hidden(sK4(sK3,sK2),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f963])).

fof(f963,plain,
    ( sK2 = sK3
    | r2_hidden(sK4(sK3,sK2),sK0)
    | ~ v1_relat_1(sK3)
    | r2_hidden(sK4(sK3,sK2),sK0) ),
    inference(resolution,[],[f192,f154])).

fof(f154,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(k4_tarski(X7,X8),sK3)
      | r2_hidden(X7,sK0) ) ),
    inference(superposition,[],[f68,f45])).

fof(f45,plain,(
    sK0 = k1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f68,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK9(X0,X1),X3),X0)
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK11(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f30,f33,f32,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK9(X0,X1),X3),X0)
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK9(X0,X1),X4),X0)
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK9(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK11(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f192,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(sK4(X2,sK2),sK5(X2,sK2)),X2)
      | sK2 = X2
      | r2_hidden(sK4(X2,sK2),sK0)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f183,f39])).

fof(f39,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f183,plain,(
    ! [X2] :
      ( r2_hidden(sK4(X2,sK2),sK0)
      | sK2 = X2
      | r2_hidden(k4_tarski(sK4(X2,sK2),sK5(X2,sK2)),X2)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f139,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
                  | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) )
                & ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
                  | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r2_hidden(k4_tarski(X2,X3),X1)
            | r2_hidden(k4_tarski(X2,X3),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
          | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) )
        & ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
          | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_relat_1)).

fof(f139,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(k4_tarski(X7,X8),sK2)
      | r2_hidden(X7,sK0) ) ),
    inference(superposition,[],[f68,f44])).

fof(f44,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f1569,plain,
    ( r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK3)
    | ~ r2_hidden(sK4(sK3,sK2),sK0) ),
    inference(superposition,[],[f735,f1490])).

fof(f1490,plain,(
    sK5(sK3,sK2) = k1_funct_1(sK2,sK4(sK3,sK2)) ),
    inference(subsumption_resolution,[],[f1489,f41])).

fof(f1489,plain,
    ( sK5(sK3,sK2) = k1_funct_1(sK2,sK4(sK3,sK2))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f1477,f47])).

fof(f1477,plain,
    ( sK2 = sK3
    | sK5(sK3,sK2) = k1_funct_1(sK2,sK4(sK3,sK2))
    | ~ v1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f1469])).

fof(f1469,plain,
    ( sK2 = sK3
    | sK5(sK3,sK2) = k1_funct_1(sK2,sK4(sK3,sK2))
    | ~ v1_relat_1(sK3)
    | sK5(sK3,sK2) = k1_funct_1(sK2,sK4(sK3,sK2)) ),
    inference(resolution,[],[f228,f740])).

fof(f740,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X4),sK3)
      | k1_funct_1(sK2,X3) = X4 ) ),
    inference(subsumption_resolution,[],[f739,f154])).

fof(f739,plain,(
    ! [X4,X3] :
      ( k1_funct_1(sK2,X3) = X4
      | ~ r2_hidden(X3,sK0)
      | ~ r2_hidden(k4_tarski(X3,X4),sK3) ) ),
    inference(subsumption_resolution,[],[f738,f41])).

fof(f738,plain,(
    ! [X4,X3] :
      ( k1_funct_1(sK2,X3) = X4
      | ~ r2_hidden(X3,sK0)
      | ~ r2_hidden(k4_tarski(X3,X4),sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f729,f42])).

fof(f42,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f729,plain,(
    ! [X4,X3] :
      ( k1_funct_1(sK2,X3) = X4
      | ~ r2_hidden(X3,sK0)
      | ~ r2_hidden(k4_tarski(X3,X4),sK3)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f714,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f714,plain,(
    ! [X0] :
      ( k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f707,f247])).

fof(f247,plain,(
    ! [X5] :
      ( r2_hidden(sK8(sK1,X5),k1_relat_1(sK1))
      | ~ r2_hidden(X5,sK0) ) ),
    inference(resolution,[],[f129,f68])).

fof(f129,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK8(sK1,X0),X0),sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(superposition,[],[f67,f43])).

fof(f43,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f24,f27,f26,f25])).

fof(f25,plain,(
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

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f707,plain,(
    ! [X0] :
      ( k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
      | ~ r2_hidden(sK8(sK1,X0),k1_relat_1(sK1))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(superposition,[],[f373,f219])).

fof(f219,plain,(
    ! [X5] :
      ( k1_funct_1(sK1,sK8(sK1,X5)) = X5
      | ~ r2_hidden(X5,sK0) ) ),
    inference(forward_demodulation,[],[f214,f43])).

fof(f214,plain,(
    ! [X5] :
      ( k1_funct_1(sK1,sK8(sK1,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f87,f67])).

fof(f87,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK1)
      | k1_funct_1(sK1,X2) = X3 ) ),
    inference(subsumption_resolution,[],[f83,f37])).

fof(f37,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f83,plain,(
    ! [X2,X3] :
      ( k1_funct_1(sK1,X2) = X3
      | ~ r2_hidden(k4_tarski(X2,X3),sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f38,f62])).

fof(f38,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f373,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(sK2,k1_funct_1(sK1,X0))
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f372,f37])).

fof(f372,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(sK2,k1_funct_1(sK1,X0))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f371,f38])).

fof(f371,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(sK2,k1_funct_1(sK1,X0))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f370,f39])).

fof(f370,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(sK2,k1_funct_1(sK1,X0))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f369,f40])).

fof(f40,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f369,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(sK2,k1_funct_1(sK1,X0))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(duplicate_literal_removal,[],[f363])).

fof(f363,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(sK2,k1_funct_1(sK1,X0))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f167,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(f167,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0)
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f166,f37])).

fof(f166,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f165,f38])).

fof(f165,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f164,f41])).

fof(f164,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK3)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f163,f42])).

fof(f163,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f52,f46])).

fof(f46,plain,(
    k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f228,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(sK4(X2,sK2),sK5(X2,sK2)),X2)
      | sK2 = X2
      | sK5(X2,sK2) = k1_funct_1(sK2,sK4(X2,sK2))
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f222,f39])).

fof(f222,plain,(
    ! [X2] :
      ( sK5(X2,sK2) = k1_funct_1(sK2,sK4(X2,sK2))
      | sK2 = X2
      | r2_hidden(k4_tarski(sK4(X2,sK2),sK5(X2,sK2)),X2)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f105,f50])).

fof(f105,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK2)
      | k1_funct_1(sK2,X2) = X3 ) ),
    inference(subsumption_resolution,[],[f101,f39])).

fof(f101,plain,(
    ! [X2,X3] :
      ( k1_funct_1(sK2,X2) = X3
      | ~ r2_hidden(k4_tarski(X2,X3),sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f40,f62])).

fof(f735,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(sK2,X1)),sK3)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(duplicate_literal_removal,[],[f731])).

fof(f731,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(sK2,X1)),sK3)
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(superposition,[],[f162,f714])).

fof(f162,plain,(
    ! [X10] :
      ( r2_hidden(k4_tarski(X10,k1_funct_1(sK3,X10)),sK3)
      | ~ r2_hidden(X10,sK0) ) ),
    inference(subsumption_resolution,[],[f161,f41])).

fof(f161,plain,(
    ! [X10] :
      ( ~ r2_hidden(X10,sK0)
      | r2_hidden(k4_tarski(X10,k1_funct_1(sK3,X10)),sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f156,f42])).

fof(f156,plain,(
    ! [X10] :
      ( ~ r2_hidden(X10,sK0)
      | r2_hidden(k4_tarski(X10,k1_funct_1(sK3,X10)),sK3)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f70,f45])).

fof(f70,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1721,plain,
    ( ~ r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f1712,f47])).

fof(f1712,plain,
    ( sK2 = sK3
    | ~ r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f1579,f94])).

fof(f94,plain,(
    ! [X3] :
      ( ~ r2_hidden(k4_tarski(sK4(X3,sK2),sK5(X3,sK2)),sK2)
      | sK2 = X3
      | ~ r2_hidden(k4_tarski(sK4(X3,sK2),sK5(X3,sK2)),X3)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f39,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1579,plain,(
    r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2) ),
    inference(subsumption_resolution,[],[f1572,f984])).

fof(f1572,plain,
    ( r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2)
    | ~ r2_hidden(sK4(sK3,sK2),sK0) ),
    inference(superposition,[],[f147,f1490])).

fof(f147,plain,(
    ! [X10] :
      ( r2_hidden(k4_tarski(X10,k1_funct_1(sK2,X10)),sK2)
      | ~ r2_hidden(X10,sK0) ) ),
    inference(subsumption_resolution,[],[f146,f39])).

fof(f146,plain,(
    ! [X10] :
      ( ~ r2_hidden(X10,sK0)
      | r2_hidden(k4_tarski(X10,k1_funct_1(sK2,X10)),sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f141,f40])).

fof(f141,plain,(
    ! [X10] :
      ( ~ r2_hidden(X10,sK0)
      | r2_hidden(k4_tarski(X10,k1_funct_1(sK2,X10)),sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f70,f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:10:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (28306)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.48  % (28323)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.49  % (28302)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (28303)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (28301)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.50  % (28322)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.50  % (28301)Refutation not found, incomplete strategy% (28301)------------------------------
% 0.20/0.50  % (28301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (28301)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (28301)Memory used [KB]: 10618
% 0.20/0.50  % (28301)Time elapsed: 0.104 s
% 0.20/0.50  % (28301)------------------------------
% 0.20/0.50  % (28301)------------------------------
% 0.20/0.50  % (28305)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (28307)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (28308)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.51  % (28304)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (28311)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.51  % (28317)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.51  % (28320)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (28308)Refutation not found, incomplete strategy% (28308)------------------------------
% 0.20/0.51  % (28308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (28308)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (28308)Memory used [KB]: 1663
% 0.20/0.51  % (28308)Time elapsed: 0.068 s
% 0.20/0.51  % (28308)------------------------------
% 0.20/0.51  % (28308)------------------------------
% 0.20/0.51  % (28326)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.52  % (28310)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.52  % (28324)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.52  % (28313)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.52  % (28325)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.52  % (28316)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  % (28318)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.52  % (28309)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.53  % (28319)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.53  % (28314)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.36/0.53  % (28327)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.36/0.53  % (28312)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.36/0.54  % (28321)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.48/0.59  % (28320)Refutation found. Thanks to Tanya!
% 1.48/0.59  % SZS status Theorem for theBenchmark
% 1.48/0.59  % SZS output start Proof for theBenchmark
% 1.48/0.59  fof(f1723,plain,(
% 1.48/0.59    $false),
% 1.48/0.59    inference(subsumption_resolution,[],[f1722,f41])).
% 1.48/0.59  fof(f41,plain,(
% 1.48/0.59    v1_relat_1(sK3)),
% 1.48/0.59    inference(cnf_transformation,[],[f18])).
% 1.48/0.59  fof(f18,plain,(
% 1.48/0.59    ((sK2 != sK3 & k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3) & sK0 = k1_relat_1(sK3) & sK0 = k1_relat_1(sK2) & sK0 = k2_relat_1(sK1) & v1_funct_1(sK3) & v1_relat_1(sK3)) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.48/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f17,f16,f15])).
% 1.48/0.59  fof(f15,plain,(
% 1.48/0.59    ? [X0,X1] : (? [X2] : (? [X3] : (X2 != X3 & k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0 & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (? [X3] : (X2 != X3 & k5_relat_1(sK1,X2) = k5_relat_1(sK1,X3) & k1_relat_1(X3) = sK0 & k1_relat_1(X2) = sK0 & sK0 = k2_relat_1(sK1) & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.48/0.59    introduced(choice_axiom,[])).
% 1.48/0.59  fof(f16,plain,(
% 1.48/0.59    ? [X2] : (? [X3] : (X2 != X3 & k5_relat_1(sK1,X2) = k5_relat_1(sK1,X3) & k1_relat_1(X3) = sK0 & k1_relat_1(X2) = sK0 & sK0 = k2_relat_1(sK1) & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(X2) & v1_relat_1(X2)) => (? [X3] : (sK2 != X3 & k5_relat_1(sK1,X3) = k5_relat_1(sK1,sK2) & k1_relat_1(X3) = sK0 & sK0 = k1_relat_1(sK2) & sK0 = k2_relat_1(sK1) & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.48/0.59    introduced(choice_axiom,[])).
% 1.48/0.59  fof(f17,plain,(
% 1.48/0.59    ? [X3] : (sK2 != X3 & k5_relat_1(sK1,X3) = k5_relat_1(sK1,sK2) & k1_relat_1(X3) = sK0 & sK0 = k1_relat_1(sK2) & sK0 = k2_relat_1(sK1) & v1_funct_1(X3) & v1_relat_1(X3)) => (sK2 != sK3 & k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3) & sK0 = k1_relat_1(sK3) & sK0 = k1_relat_1(sK2) & sK0 = k2_relat_1(sK1) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 1.48/0.59    introduced(choice_axiom,[])).
% 1.48/0.59  fof(f9,plain,(
% 1.48/0.59    ? [X0,X1] : (? [X2] : (? [X3] : (X2 != X3 & k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0 & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.48/0.59    inference(flattening,[],[f8])).
% 1.48/0.59  fof(f8,plain,(
% 1.48/0.59    ? [X0,X1] : (? [X2] : (? [X3] : ((X2 != X3 & (k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0)) & (v1_funct_1(X3) & v1_relat_1(X3))) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.48/0.59    inference(ennf_transformation,[],[f7])).
% 1.48/0.59  fof(f7,negated_conjecture,(
% 1.48/0.59    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0) => X2 = X3))))),
% 1.48/0.59    inference(negated_conjecture,[],[f6])).
% 1.48/0.59  fof(f6,conjecture,(
% 1.48/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0) => X2 = X3))))),
% 1.48/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_funct_1)).
% 1.48/0.59  fof(f1722,plain,(
% 1.48/0.59    ~v1_relat_1(sK3)),
% 1.48/0.59    inference(subsumption_resolution,[],[f1721,f1577])).
% 1.48/0.59  fof(f1577,plain,(
% 1.48/0.59    r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK3)),
% 1.48/0.59    inference(subsumption_resolution,[],[f1569,f984])).
% 1.48/0.59  fof(f984,plain,(
% 1.48/0.59    r2_hidden(sK4(sK3,sK2),sK0)),
% 1.48/0.59    inference(subsumption_resolution,[],[f983,f41])).
% 1.48/0.59  fof(f983,plain,(
% 1.48/0.59    r2_hidden(sK4(sK3,sK2),sK0) | ~v1_relat_1(sK3)),
% 1.48/0.59    inference(subsumption_resolution,[],[f969,f47])).
% 1.48/0.59  fof(f47,plain,(
% 1.48/0.59    sK2 != sK3),
% 1.48/0.59    inference(cnf_transformation,[],[f18])).
% 1.48/0.59  fof(f969,plain,(
% 1.48/0.59    sK2 = sK3 | r2_hidden(sK4(sK3,sK2),sK0) | ~v1_relat_1(sK3)),
% 1.48/0.59    inference(duplicate_literal_removal,[],[f963])).
% 1.48/0.59  fof(f963,plain,(
% 1.48/0.59    sK2 = sK3 | r2_hidden(sK4(sK3,sK2),sK0) | ~v1_relat_1(sK3) | r2_hidden(sK4(sK3,sK2),sK0)),
% 1.48/0.59    inference(resolution,[],[f192,f154])).
% 1.48/0.59  fof(f154,plain,(
% 1.48/0.59    ( ! [X8,X7] : (~r2_hidden(k4_tarski(X7,X8),sK3) | r2_hidden(X7,sK0)) )),
% 1.48/0.59    inference(superposition,[],[f68,f45])).
% 1.48/0.59  fof(f45,plain,(
% 1.48/0.59    sK0 = k1_relat_1(sK3)),
% 1.48/0.59    inference(cnf_transformation,[],[f18])).
% 1.48/0.59  fof(f68,plain,(
% 1.48/0.59    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 1.48/0.59    inference(equality_resolution,[],[f58])).
% 1.48/0.59  fof(f58,plain,(
% 1.48/0.59    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 1.48/0.59    inference(cnf_transformation,[],[f34])).
% 1.48/0.59  fof(f34,plain,(
% 1.48/0.59    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK9(X0,X1),X3),X0) | ~r2_hidden(sK9(X0,X1),X1)) & (r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) | r2_hidden(sK9(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK11(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.48/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f30,f33,f32,f31])).
% 1.48/0.59  fof(f31,plain,(
% 1.48/0.59    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK9(X0,X1),X3),X0) | ~r2_hidden(sK9(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK9(X0,X1),X4),X0) | r2_hidden(sK9(X0,X1),X1))))),
% 1.48/0.59    introduced(choice_axiom,[])).
% 1.48/0.59  fof(f32,plain,(
% 1.48/0.59    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK9(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0))),
% 1.48/0.59    introduced(choice_axiom,[])).
% 1.48/0.59  fof(f33,plain,(
% 1.48/0.59    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK11(X0,X5)),X0))),
% 1.48/0.59    introduced(choice_axiom,[])).
% 1.48/0.59  fof(f30,plain,(
% 1.48/0.59    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.48/0.59    inference(rectify,[],[f29])).
% 1.48/0.59  fof(f29,plain,(
% 1.48/0.59    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 1.48/0.59    inference(nnf_transformation,[],[f2])).
% 1.48/0.59  fof(f2,axiom,(
% 1.48/0.59    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.48/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 1.48/0.59  fof(f192,plain,(
% 1.48/0.59    ( ! [X2] : (r2_hidden(k4_tarski(sK4(X2,sK2),sK5(X2,sK2)),X2) | sK2 = X2 | r2_hidden(sK4(X2,sK2),sK0) | ~v1_relat_1(X2)) )),
% 1.48/0.59    inference(subsumption_resolution,[],[f183,f39])).
% 1.48/0.59  fof(f39,plain,(
% 1.48/0.59    v1_relat_1(sK2)),
% 1.48/0.59    inference(cnf_transformation,[],[f18])).
% 1.48/0.59  fof(f183,plain,(
% 1.48/0.59    ( ! [X2] : (r2_hidden(sK4(X2,sK2),sK0) | sK2 = X2 | r2_hidden(k4_tarski(sK4(X2,sK2),sK5(X2,sK2)),X2) | ~v1_relat_1(sK2) | ~v1_relat_1(X2)) )),
% 1.48/0.59    inference(resolution,[],[f139,f50])).
% 1.48/0.59  fof(f50,plain,(
% 1.48/0.59    ( ! [X0,X1] : (X0 = X1 | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f22])).
% 1.48/0.59  fof(f22,plain,(
% 1.48/0.59    ! [X0] : (! [X1] : (((X0 = X1 | ((~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(k4_tarski(X4,X5),X1)) & (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0))) | X0 != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.48/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f20,f21])).
% 1.48/0.59  fof(f21,plain,(
% 1.48/0.59    ! [X1,X0] : (? [X2,X3] : ((~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r2_hidden(k4_tarski(X2,X3),X1) | r2_hidden(k4_tarski(X2,X3),X0))) => ((~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0))))),
% 1.48/0.59    introduced(choice_axiom,[])).
% 1.48/0.59  fof(f20,plain,(
% 1.48/0.59    ! [X0] : (! [X1] : (((X0 = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r2_hidden(k4_tarski(X2,X3),X1) | r2_hidden(k4_tarski(X2,X3),X0)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(k4_tarski(X4,X5),X1)) & (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0))) | X0 != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.48/0.59    inference(rectify,[],[f19])).
% 1.48/0.59  fof(f19,plain,(
% 1.48/0.59    ! [X0] : (! [X1] : (((X0 = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r2_hidden(k4_tarski(X2,X3),X1) | r2_hidden(k4_tarski(X2,X3),X0)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | X0 != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.48/0.59    inference(nnf_transformation,[],[f10])).
% 1.48/0.59  fof(f10,plain,(
% 1.48/0.59    ! [X0] : (! [X1] : ((X0 = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) <=> r2_hidden(k4_tarski(X2,X3),X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.48/0.59    inference(ennf_transformation,[],[f1])).
% 1.48/0.59  fof(f1,axiom,(
% 1.48/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (X0 = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) <=> r2_hidden(k4_tarski(X2,X3),X1)))))),
% 1.48/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_relat_1)).
% 1.48/0.59  fof(f139,plain,(
% 1.48/0.59    ( ! [X8,X7] : (~r2_hidden(k4_tarski(X7,X8),sK2) | r2_hidden(X7,sK0)) )),
% 1.48/0.59    inference(superposition,[],[f68,f44])).
% 1.48/0.59  fof(f44,plain,(
% 1.48/0.59    sK0 = k1_relat_1(sK2)),
% 1.48/0.59    inference(cnf_transformation,[],[f18])).
% 1.48/0.59  fof(f1569,plain,(
% 1.48/0.59    r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK3) | ~r2_hidden(sK4(sK3,sK2),sK0)),
% 1.48/0.59    inference(superposition,[],[f735,f1490])).
% 1.48/0.59  fof(f1490,plain,(
% 1.48/0.59    sK5(sK3,sK2) = k1_funct_1(sK2,sK4(sK3,sK2))),
% 1.48/0.59    inference(subsumption_resolution,[],[f1489,f41])).
% 1.48/0.59  fof(f1489,plain,(
% 1.48/0.59    sK5(sK3,sK2) = k1_funct_1(sK2,sK4(sK3,sK2)) | ~v1_relat_1(sK3)),
% 1.48/0.59    inference(subsumption_resolution,[],[f1477,f47])).
% 1.48/0.59  fof(f1477,plain,(
% 1.48/0.59    sK2 = sK3 | sK5(sK3,sK2) = k1_funct_1(sK2,sK4(sK3,sK2)) | ~v1_relat_1(sK3)),
% 1.48/0.59    inference(duplicate_literal_removal,[],[f1469])).
% 1.48/0.59  fof(f1469,plain,(
% 1.48/0.59    sK2 = sK3 | sK5(sK3,sK2) = k1_funct_1(sK2,sK4(sK3,sK2)) | ~v1_relat_1(sK3) | sK5(sK3,sK2) = k1_funct_1(sK2,sK4(sK3,sK2))),
% 1.48/0.59    inference(resolution,[],[f228,f740])).
% 1.48/0.59  fof(f740,plain,(
% 1.48/0.59    ( ! [X4,X3] : (~r2_hidden(k4_tarski(X3,X4),sK3) | k1_funct_1(sK2,X3) = X4) )),
% 1.48/0.59    inference(subsumption_resolution,[],[f739,f154])).
% 1.48/0.59  fof(f739,plain,(
% 1.48/0.59    ( ! [X4,X3] : (k1_funct_1(sK2,X3) = X4 | ~r2_hidden(X3,sK0) | ~r2_hidden(k4_tarski(X3,X4),sK3)) )),
% 1.48/0.59    inference(subsumption_resolution,[],[f738,f41])).
% 1.48/0.59  fof(f738,plain,(
% 1.48/0.59    ( ! [X4,X3] : (k1_funct_1(sK2,X3) = X4 | ~r2_hidden(X3,sK0) | ~r2_hidden(k4_tarski(X3,X4),sK3) | ~v1_relat_1(sK3)) )),
% 1.48/0.59    inference(subsumption_resolution,[],[f729,f42])).
% 1.48/0.59  fof(f42,plain,(
% 1.48/0.59    v1_funct_1(sK3)),
% 1.48/0.59    inference(cnf_transformation,[],[f18])).
% 1.48/0.59  fof(f729,plain,(
% 1.48/0.59    ( ! [X4,X3] : (k1_funct_1(sK2,X3) = X4 | ~r2_hidden(X3,sK0) | ~r2_hidden(k4_tarski(X3,X4),sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 1.48/0.59    inference(superposition,[],[f714,f62])).
% 1.48/0.59  fof(f62,plain,(
% 1.48/0.59    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f36])).
% 1.48/0.59  fof(f36,plain,(
% 1.48/0.59    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.48/0.59    inference(flattening,[],[f35])).
% 1.48/0.59  fof(f35,plain,(
% 1.48/0.59    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.48/0.59    inference(nnf_transformation,[],[f14])).
% 1.48/0.59  fof(f14,plain,(
% 1.48/0.59    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.48/0.59    inference(flattening,[],[f13])).
% 1.48/0.59  fof(f13,plain,(
% 1.48/0.59    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.48/0.59    inference(ennf_transformation,[],[f5])).
% 1.48/0.59  fof(f5,axiom,(
% 1.48/0.59    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.48/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 1.48/0.59  fof(f714,plain,(
% 1.48/0.59    ( ! [X0] : (k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) | ~r2_hidden(X0,sK0)) )),
% 1.48/0.59    inference(subsumption_resolution,[],[f707,f247])).
% 1.48/0.59  fof(f247,plain,(
% 1.48/0.59    ( ! [X5] : (r2_hidden(sK8(sK1,X5),k1_relat_1(sK1)) | ~r2_hidden(X5,sK0)) )),
% 1.48/0.59    inference(resolution,[],[f129,f68])).
% 1.48/0.59  fof(f129,plain,(
% 1.48/0.59    ( ! [X0] : (r2_hidden(k4_tarski(sK8(sK1,X0),X0),sK1) | ~r2_hidden(X0,sK0)) )),
% 1.48/0.59    inference(superposition,[],[f67,f43])).
% 1.48/0.59  fof(f43,plain,(
% 1.48/0.59    sK0 = k2_relat_1(sK1)),
% 1.48/0.59    inference(cnf_transformation,[],[f18])).
% 1.48/0.59  fof(f67,plain,(
% 1.48/0.59    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 1.48/0.59    inference(equality_resolution,[],[f53])).
% 1.48/0.59  fof(f53,plain,(
% 1.48/0.59    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 1.48/0.59    inference(cnf_transformation,[],[f28])).
% 1.48/0.59  fof(f28,plain,(
% 1.48/0.59    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.48/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f24,f27,f26,f25])).
% 1.48/0.59  fof(f25,plain,(
% 1.48/0.59    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 1.48/0.59    introduced(choice_axiom,[])).
% 1.48/0.59  fof(f26,plain,(
% 1.48/0.59    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0) => r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0))),
% 1.48/0.59    introduced(choice_axiom,[])).
% 1.48/0.59  fof(f27,plain,(
% 1.48/0.59    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0))),
% 1.48/0.59    introduced(choice_axiom,[])).
% 1.48/0.59  fof(f24,plain,(
% 1.48/0.59    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.48/0.59    inference(rectify,[],[f23])).
% 1.48/0.59  fof(f23,plain,(
% 1.48/0.59    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 1.48/0.59    inference(nnf_transformation,[],[f3])).
% 1.48/0.59  fof(f3,axiom,(
% 1.48/0.59    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.48/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 1.48/0.59  fof(f707,plain,(
% 1.48/0.59    ( ! [X0] : (k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) | ~r2_hidden(sK8(sK1,X0),k1_relat_1(sK1)) | ~r2_hidden(X0,sK0)) )),
% 1.48/0.59    inference(superposition,[],[f373,f219])).
% 1.48/0.59  fof(f219,plain,(
% 1.48/0.59    ( ! [X5] : (k1_funct_1(sK1,sK8(sK1,X5)) = X5 | ~r2_hidden(X5,sK0)) )),
% 1.48/0.59    inference(forward_demodulation,[],[f214,f43])).
% 1.48/0.59  fof(f214,plain,(
% 1.48/0.59    ( ! [X5] : (k1_funct_1(sK1,sK8(sK1,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(sK1))) )),
% 1.48/0.59    inference(resolution,[],[f87,f67])).
% 1.48/0.59  fof(f87,plain,(
% 1.48/0.59    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK1) | k1_funct_1(sK1,X2) = X3) )),
% 1.48/0.59    inference(subsumption_resolution,[],[f83,f37])).
% 1.48/0.59  fof(f37,plain,(
% 1.48/0.59    v1_relat_1(sK1)),
% 1.48/0.59    inference(cnf_transformation,[],[f18])).
% 1.48/0.59  fof(f83,plain,(
% 1.48/0.59    ( ! [X2,X3] : (k1_funct_1(sK1,X2) = X3 | ~r2_hidden(k4_tarski(X2,X3),sK1) | ~v1_relat_1(sK1)) )),
% 1.48/0.59    inference(resolution,[],[f38,f62])).
% 1.48/0.59  fof(f38,plain,(
% 1.48/0.59    v1_funct_1(sK1)),
% 1.48/0.59    inference(cnf_transformation,[],[f18])).
% 1.48/0.59  fof(f373,plain,(
% 1.48/0.59    ( ! [X0] : (k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(sK2,k1_funct_1(sK1,X0)) | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 1.48/0.59    inference(subsumption_resolution,[],[f372,f37])).
% 1.48/0.59  fof(f372,plain,(
% 1.48/0.59    ( ! [X0] : (k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(sK2,k1_funct_1(sK1,X0)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 1.48/0.59    inference(subsumption_resolution,[],[f371,f38])).
% 1.48/0.59  fof(f371,plain,(
% 1.48/0.59    ( ! [X0] : (k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(sK2,k1_funct_1(sK1,X0)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.48/0.59    inference(subsumption_resolution,[],[f370,f39])).
% 1.48/0.59  fof(f370,plain,(
% 1.48/0.59    ( ! [X0] : (k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(sK2,k1_funct_1(sK1,X0)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.48/0.59    inference(subsumption_resolution,[],[f369,f40])).
% 1.48/0.59  fof(f40,plain,(
% 1.48/0.59    v1_funct_1(sK2)),
% 1.48/0.59    inference(cnf_transformation,[],[f18])).
% 1.48/0.59  fof(f369,plain,(
% 1.48/0.59    ( ! [X0] : (k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(sK2,k1_funct_1(sK1,X0)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.48/0.59    inference(duplicate_literal_removal,[],[f363])).
% 1.48/0.59  fof(f363,plain,(
% 1.48/0.59    ( ! [X0] : (k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(sK2,k1_funct_1(sK1,X0)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.48/0.59    inference(superposition,[],[f167,f52])).
% 1.48/0.59  fof(f52,plain,(
% 1.48/0.59    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f12])).
% 1.48/0.59  fof(f12,plain,(
% 1.48/0.59    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.48/0.59    inference(flattening,[],[f11])).
% 1.48/0.59  fof(f11,plain,(
% 1.48/0.59    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.48/0.59    inference(ennf_transformation,[],[f4])).
% 1.48/0.59  fof(f4,axiom,(
% 1.48/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 1.48/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
% 1.48/0.59  fof(f167,plain,(
% 1.48/0.59    ( ! [X0] : (k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0) | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 1.48/0.59    inference(subsumption_resolution,[],[f166,f37])).
% 1.48/0.59  fof(f166,plain,(
% 1.48/0.59    ( ! [X0] : (k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 1.48/0.59    inference(subsumption_resolution,[],[f165,f38])).
% 1.48/0.59  fof(f165,plain,(
% 1.48/0.59    ( ! [X0] : (k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.48/0.59    inference(subsumption_resolution,[],[f164,f41])).
% 1.48/0.59  fof(f164,plain,(
% 1.48/0.59    ( ! [X0] : (k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.48/0.59    inference(subsumption_resolution,[],[f163,f42])).
% 1.48/0.59  fof(f163,plain,(
% 1.48/0.59    ( ! [X0] : (k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.48/0.59    inference(superposition,[],[f52,f46])).
% 1.48/0.59  fof(f46,plain,(
% 1.48/0.59    k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3)),
% 1.48/0.59    inference(cnf_transformation,[],[f18])).
% 1.48/0.59  fof(f228,plain,(
% 1.48/0.59    ( ! [X2] : (r2_hidden(k4_tarski(sK4(X2,sK2),sK5(X2,sK2)),X2) | sK2 = X2 | sK5(X2,sK2) = k1_funct_1(sK2,sK4(X2,sK2)) | ~v1_relat_1(X2)) )),
% 1.48/0.59    inference(subsumption_resolution,[],[f222,f39])).
% 1.48/0.59  fof(f222,plain,(
% 1.48/0.59    ( ! [X2] : (sK5(X2,sK2) = k1_funct_1(sK2,sK4(X2,sK2)) | sK2 = X2 | r2_hidden(k4_tarski(sK4(X2,sK2),sK5(X2,sK2)),X2) | ~v1_relat_1(sK2) | ~v1_relat_1(X2)) )),
% 1.48/0.59    inference(resolution,[],[f105,f50])).
% 1.48/0.59  fof(f105,plain,(
% 1.48/0.59    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK2) | k1_funct_1(sK2,X2) = X3) )),
% 1.48/0.59    inference(subsumption_resolution,[],[f101,f39])).
% 1.48/0.59  fof(f101,plain,(
% 1.48/0.59    ( ! [X2,X3] : (k1_funct_1(sK2,X2) = X3 | ~r2_hidden(k4_tarski(X2,X3),sK2) | ~v1_relat_1(sK2)) )),
% 1.48/0.59    inference(resolution,[],[f40,f62])).
% 1.48/0.59  fof(f735,plain,(
% 1.48/0.59    ( ! [X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(sK2,X1)),sK3) | ~r2_hidden(X1,sK0)) )),
% 1.48/0.59    inference(duplicate_literal_removal,[],[f731])).
% 1.48/0.59  fof(f731,plain,(
% 1.48/0.59    ( ! [X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(sK2,X1)),sK3) | ~r2_hidden(X1,sK0) | ~r2_hidden(X1,sK0)) )),
% 1.48/0.59    inference(superposition,[],[f162,f714])).
% 1.48/0.59  fof(f162,plain,(
% 1.48/0.59    ( ! [X10] : (r2_hidden(k4_tarski(X10,k1_funct_1(sK3,X10)),sK3) | ~r2_hidden(X10,sK0)) )),
% 1.48/0.59    inference(subsumption_resolution,[],[f161,f41])).
% 1.48/0.59  fof(f161,plain,(
% 1.48/0.59    ( ! [X10] : (~r2_hidden(X10,sK0) | r2_hidden(k4_tarski(X10,k1_funct_1(sK3,X10)),sK3) | ~v1_relat_1(sK3)) )),
% 1.48/0.59    inference(subsumption_resolution,[],[f156,f42])).
% 1.48/0.59  fof(f156,plain,(
% 1.48/0.59    ( ! [X10] : (~r2_hidden(X10,sK0) | r2_hidden(k4_tarski(X10,k1_funct_1(sK3,X10)),sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 1.48/0.59    inference(superposition,[],[f70,f45])).
% 1.48/0.59  fof(f70,plain,(
% 1.48/0.59    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.48/0.59    inference(equality_resolution,[],[f63])).
% 1.48/0.59  fof(f63,plain,(
% 1.48/0.59    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f36])).
% 1.48/0.59  fof(f1721,plain,(
% 1.48/0.59    ~r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK3) | ~v1_relat_1(sK3)),
% 1.48/0.59    inference(subsumption_resolution,[],[f1712,f47])).
% 1.48/0.59  fof(f1712,plain,(
% 1.48/0.59    sK2 = sK3 | ~r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK3) | ~v1_relat_1(sK3)),
% 1.48/0.59    inference(resolution,[],[f1579,f94])).
% 1.48/0.59  fof(f94,plain,(
% 1.48/0.59    ( ! [X3] : (~r2_hidden(k4_tarski(sK4(X3,sK2),sK5(X3,sK2)),sK2) | sK2 = X3 | ~r2_hidden(k4_tarski(sK4(X3,sK2),sK5(X3,sK2)),X3) | ~v1_relat_1(X3)) )),
% 1.48/0.59    inference(resolution,[],[f39,f51])).
% 1.48/0.59  fof(f51,plain,(
% 1.48/0.59    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f22])).
% 1.48/0.59  fof(f1579,plain,(
% 1.48/0.59    r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2)),
% 1.48/0.59    inference(subsumption_resolution,[],[f1572,f984])).
% 1.48/0.59  fof(f1572,plain,(
% 1.48/0.59    r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2) | ~r2_hidden(sK4(sK3,sK2),sK0)),
% 1.48/0.59    inference(superposition,[],[f147,f1490])).
% 1.48/0.59  fof(f147,plain,(
% 1.48/0.59    ( ! [X10] : (r2_hidden(k4_tarski(X10,k1_funct_1(sK2,X10)),sK2) | ~r2_hidden(X10,sK0)) )),
% 1.48/0.59    inference(subsumption_resolution,[],[f146,f39])).
% 1.48/0.59  fof(f146,plain,(
% 1.48/0.59    ( ! [X10] : (~r2_hidden(X10,sK0) | r2_hidden(k4_tarski(X10,k1_funct_1(sK2,X10)),sK2) | ~v1_relat_1(sK2)) )),
% 1.48/0.59    inference(subsumption_resolution,[],[f141,f40])).
% 1.48/0.59  fof(f141,plain,(
% 1.48/0.59    ( ! [X10] : (~r2_hidden(X10,sK0) | r2_hidden(k4_tarski(X10,k1_funct_1(sK2,X10)),sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.48/0.59    inference(superposition,[],[f70,f44])).
% 1.48/0.59  % SZS output end Proof for theBenchmark
% 1.48/0.59  % (28320)------------------------------
% 1.48/0.59  % (28320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.59  % (28320)Termination reason: Refutation
% 1.48/0.59  
% 1.48/0.59  % (28320)Memory used [KB]: 2174
% 1.48/0.59  % (28320)Time elapsed: 0.192 s
% 1.48/0.59  % (28320)------------------------------
% 1.48/0.59  % (28320)------------------------------
% 1.48/0.59  % (28295)Success in time 0.233 s
%------------------------------------------------------------------------------
