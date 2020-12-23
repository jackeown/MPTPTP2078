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
% DateTime   : Thu Dec  3 12:54:10 EST 2020

% Result     : Theorem 2.12s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 765 expanded)
%              Number of leaves         :   17 ( 279 expanded)
%              Depth                    :   33
%              Number of atoms          :  562 (7328 expanded)
%              Number of equality atoms :  158 (3234 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f855,plain,(
    $false ),
    inference(subsumption_resolution,[],[f854,f52])).

fof(f52,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f22,f21,f20])).

fof(f20,plain,
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

fof(f21,plain,
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

fof(f22,plain,
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

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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

fof(f854,plain,(
    ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f849,f779])).

fof(f779,plain,(
    ~ r1_tarski(sK3,sK2) ),
    inference(subsumption_resolution,[],[f776,f58])).

fof(f58,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f23])).

fof(f776,plain,
    ( sK2 = sK3
    | ~ r1_tarski(sK3,sK2) ),
    inference(resolution,[],[f761,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f761,plain,(
    r1_tarski(sK2,sK3) ),
    inference(subsumption_resolution,[],[f756,f50])).

fof(f50,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f756,plain,
    ( r1_tarski(sK2,sK3)
    | ~ v1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f754])).

fof(f754,plain,
    ( r1_tarski(sK2,sK3)
    | r1_tarski(sK2,sK3)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f600,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(f600,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK4(sK2,X0),sK5(sK2,X0)),sK3)
      | r1_tarski(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f597,f101])).

fof(f101,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK2,X0),sK0)
      | r1_tarski(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f99,f50])).

fof(f99,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK2,X0),sK0)
      | ~ v1_relat_1(sK2)
      | r1_tarski(sK2,X0) ) ),
    inference(superposition,[],[f98,f55])).

fof(f55,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f60,f88])).

fof(f88,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK10(X0,X1),X3),X0)
            | ~ r2_hidden(sK10(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0)
            | r2_hidden(sK10(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f41,f44,f43,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK10(X0,X1),X3),X0)
          | ~ r2_hidden(sK10(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0)
          | r2_hidden(sK10(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f597,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK4(sK2,X0),sK5(sK2,X0)),sK3)
      | ~ r2_hidden(sK4(sK2,X0),sK0)
      | r1_tarski(sK2,X0) ) ),
    inference(superposition,[],[f568,f120])).

fof(f120,plain,(
    ! [X1] :
      ( k1_funct_1(sK2,sK4(sK2,X1)) = sK5(sK2,X1)
      | r1_tarski(sK2,X1) ) ),
    inference(subsumption_resolution,[],[f117,f50])).

fof(f117,plain,(
    ! [X1] :
      ( k1_funct_1(sK2,sK4(sK2,X1)) = sK5(sK2,X1)
      | r1_tarski(sK2,X1)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f110,f60])).

fof(f110,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK2)
      | k1_funct_1(sK2,X2) = X3 ) ),
    inference(subsumption_resolution,[],[f107,f50])).

fof(f107,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK2)
      | k1_funct_1(sK2,X2) = X3
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f80,f51])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f568,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(sK2,X1)),sK3)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(duplicate_literal_removal,[],[f565])).

fof(f565,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(sK2,X1)),sK3)
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(superposition,[],[f131,f560])).

fof(f560,plain,(
    ! [X0] :
      ( k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(duplicate_literal_removal,[],[f559])).

fof(f559,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(forward_demodulation,[],[f558,f54])).

fof(f54,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f558,plain,(
    ! [X0] :
      ( k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f557,f48])).

fof(f48,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f557,plain,(
    ! [X0] :
      ( k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,k2_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f555,f49])).

fof(f49,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f555,plain,(
    ! [X0] :
      ( k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,k2_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f539,f85])).

fof(f85,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK8(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK8(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK6(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK6(X0,X1),X1) )
              & ( ( sK6(X0,X1) = k1_funct_1(X0,sK7(X0,X1))
                  & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK6(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK8(X0,X5)) = X5
                    & r2_hidden(sK8(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f29,f32,f31,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK6(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK6(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK6(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK6(X0,X1) = k1_funct_1(X0,sK7(X0,X1))
        & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK8(X0,X5)) = X5
        & r2_hidden(sK8(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f539,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK8(sK1,X1),k1_relat_1(sK1))
      | k1_funct_1(sK3,X1) = k1_funct_1(sK2,X1)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(superposition,[],[f533,f269])).

fof(f269,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK8(sK1,X0)) = X0
      | ~ r2_hidden(X0,sK0) ) ),
    inference(forward_demodulation,[],[f268,f54])).

fof(f268,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | k1_funct_1(sK1,sK8(sK1,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f265,f48])).

fof(f265,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | k1_funct_1(sK1,sK8(sK1,X0)) = X0
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f84,f49])).

fof(f84,plain,(
    ! [X0,X5] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | k1_funct_1(X0,sK8(X0,X5)) = X5
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK8(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f533,plain,(
    ! [X1] :
      ( k1_funct_1(sK2,k1_funct_1(sK1,X1)) = k1_funct_1(sK3,k1_funct_1(sK1,X1))
      | ~ r2_hidden(X1,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f532,f48])).

fof(f532,plain,(
    ! [X1] :
      ( k1_funct_1(sK2,k1_funct_1(sK1,X1)) = k1_funct_1(sK3,k1_funct_1(sK1,X1))
      | ~ r2_hidden(X1,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f531,f49])).

fof(f531,plain,(
    ! [X1] :
      ( k1_funct_1(sK2,k1_funct_1(sK1,X1)) = k1_funct_1(sK3,k1_funct_1(sK1,X1))
      | ~ r2_hidden(X1,k1_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f530,f50])).

fof(f530,plain,(
    ! [X1] :
      ( k1_funct_1(sK2,k1_funct_1(sK1,X1)) = k1_funct_1(sK3,k1_funct_1(sK1,X1))
      | ~ r2_hidden(X1,k1_relat_1(sK1))
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f529,f51])).

fof(f529,plain,(
    ! [X1] :
      ( k1_funct_1(sK2,k1_funct_1(sK1,X1)) = k1_funct_1(sK3,k1_funct_1(sK1,X1))
      | ~ r2_hidden(X1,k1_relat_1(sK1))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(duplicate_literal_removal,[],[f526])).

fof(f526,plain,(
    ! [X1] :
      ( k1_funct_1(sK2,k1_funct_1(sK1,X1)) = k1_funct_1(sK3,k1_funct_1(sK1,X1))
      | ~ r2_hidden(X1,k1_relat_1(sK1))
      | ~ r2_hidden(X1,k1_relat_1(sK1))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f525,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(f525,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0)
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f524,f48])).

fof(f524,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f523,f49])).

fof(f523,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f522,f52])).

fof(f522,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK3)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f521,f53])).

fof(f53,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f521,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f68,f57])).

fof(f57,plain,(
    k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f131,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(forward_demodulation,[],[f129,f56])).

fof(f56,plain,(
    sK0 = k1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f129,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(superposition,[],[f89,f124])).

fof(f124,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,X0) = sK12(sK3,X0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(forward_demodulation,[],[f121,f56])).

fof(f121,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,X0) = sK12(sK3,X0)
      | ~ r2_hidden(X0,k1_relat_1(sK3)) ) ),
    inference(resolution,[],[f111,f89])).

fof(f111,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),sK3)
      | k1_funct_1(sK3,X4) = X5 ) ),
    inference(subsumption_resolution,[],[f108,f52])).

fof(f108,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),sK3)
      | k1_funct_1(sK3,X4) = X5
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f80,f53])).

fof(f89,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f849,plain,
    ( r1_tarski(sK3,sK2)
    | ~ v1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f847])).

fof(f847,plain,
    ( r1_tarski(sK3,sK2)
    | r1_tarski(sK3,sK2)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f744,f61])).

fof(f744,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(sK4(sK3,X2),sK5(sK3,X2)),sK2)
      | r1_tarski(sK3,X2) ) ),
    inference(subsumption_resolution,[],[f743,f102])).

fof(f102,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK3,X1),sK0)
      | r1_tarski(sK3,X1) ) ),
    inference(subsumption_resolution,[],[f100,f52])).

fof(f100,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK3,X1),sK0)
      | ~ v1_relat_1(sK3)
      | r1_tarski(sK3,X1) ) ),
    inference(superposition,[],[f98,f56])).

fof(f743,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(sK4(sK3,X2),sK5(sK3,X2)),sK2)
      | ~ r2_hidden(sK4(sK3,X2),sK0)
      | r1_tarski(sK3,X2) ) ),
    inference(superposition,[],[f128,f570])).

fof(f570,plain,(
    ! [X2] :
      ( sK5(sK3,X2) = k1_funct_1(sK2,sK4(sK3,X2))
      | r1_tarski(sK3,X2) ) ),
    inference(subsumption_resolution,[],[f562,f102])).

fof(f562,plain,(
    ! [X2] :
      ( sK5(sK3,X2) = k1_funct_1(sK2,sK4(sK3,X2))
      | ~ r2_hidden(sK4(sK3,X2),sK0)
      | r1_tarski(sK3,X2) ) ),
    inference(superposition,[],[f560,f125])).

fof(f125,plain,(
    ! [X1] :
      ( k1_funct_1(sK3,sK4(sK3,X1)) = sK5(sK3,X1)
      | r1_tarski(sK3,X1) ) ),
    inference(subsumption_resolution,[],[f122,f52])).

fof(f122,plain,(
    ! [X1] :
      ( k1_funct_1(sK3,sK4(sK3,X1)) = sK5(sK3,X1)
      | r1_tarski(sK3,X1)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f111,f60])).

fof(f128,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(duplicate_literal_removal,[],[f127])).

fof(f127,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(forward_demodulation,[],[f126,f55])).

fof(f126,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2)
      | ~ r2_hidden(X0,k1_relat_1(sK2))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(superposition,[],[f89,f119])).

fof(f119,plain,(
    ! [X0] :
      ( k1_funct_1(sK2,X0) = sK12(sK2,X0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(forward_demodulation,[],[f116,f55])).

fof(f116,plain,(
    ! [X0] :
      ( k1_funct_1(sK2,X0) = sK12(sK2,X0)
      | ~ r2_hidden(X0,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f110,f89])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:24:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (5986)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (5983)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (5987)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (6003)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (6004)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (5996)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (5981)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (6007)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.52  % (5994)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (5984)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (6011)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (6001)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (5995)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (5991)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (5993)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (5999)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (6000)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.53  % (5998)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (5982)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (5980)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (6009)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (6005)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (5989)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (6002)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (6007)Refutation not found, incomplete strategy% (6007)------------------------------
% 0.22/0.54  % (6007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (6007)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (6007)Memory used [KB]: 10874
% 0.22/0.54  % (6007)Time elapsed: 0.130 s
% 0.22/0.54  % (6007)------------------------------
% 0.22/0.54  % (6007)------------------------------
% 0.22/0.54  % (5990)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (5997)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (6008)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (5988)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (5992)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (6006)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 2.12/0.66  % (5983)Refutation found. Thanks to Tanya!
% 2.12/0.66  % SZS status Theorem for theBenchmark
% 2.12/0.66  % SZS output start Proof for theBenchmark
% 2.12/0.66  fof(f855,plain,(
% 2.12/0.66    $false),
% 2.12/0.66    inference(subsumption_resolution,[],[f854,f52])).
% 2.12/0.66  fof(f52,plain,(
% 2.12/0.66    v1_relat_1(sK3)),
% 2.12/0.66    inference(cnf_transformation,[],[f23])).
% 2.12/0.66  fof(f23,plain,(
% 2.12/0.66    ((sK2 != sK3 & k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3) & sK0 = k1_relat_1(sK3) & sK0 = k1_relat_1(sK2) & sK0 = k2_relat_1(sK1) & v1_funct_1(sK3) & v1_relat_1(sK3)) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 2.12/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f22,f21,f20])).
% 2.12/0.66  fof(f20,plain,(
% 2.12/0.66    ? [X0,X1] : (? [X2] : (? [X3] : (X2 != X3 & k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0 & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (? [X3] : (X2 != X3 & k5_relat_1(sK1,X2) = k5_relat_1(sK1,X3) & k1_relat_1(X3) = sK0 & k1_relat_1(X2) = sK0 & sK0 = k2_relat_1(sK1) & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 2.12/0.66    introduced(choice_axiom,[])).
% 2.12/0.66  fof(f21,plain,(
% 2.12/0.66    ? [X2] : (? [X3] : (X2 != X3 & k5_relat_1(sK1,X2) = k5_relat_1(sK1,X3) & k1_relat_1(X3) = sK0 & k1_relat_1(X2) = sK0 & sK0 = k2_relat_1(sK1) & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(X2) & v1_relat_1(X2)) => (? [X3] : (sK2 != X3 & k5_relat_1(sK1,X3) = k5_relat_1(sK1,sK2) & k1_relat_1(X3) = sK0 & sK0 = k1_relat_1(sK2) & sK0 = k2_relat_1(sK1) & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 2.12/0.66    introduced(choice_axiom,[])).
% 2.12/0.66  fof(f22,plain,(
% 2.12/0.66    ? [X3] : (sK2 != X3 & k5_relat_1(sK1,X3) = k5_relat_1(sK1,sK2) & k1_relat_1(X3) = sK0 & sK0 = k1_relat_1(sK2) & sK0 = k2_relat_1(sK1) & v1_funct_1(X3) & v1_relat_1(X3)) => (sK2 != sK3 & k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3) & sK0 = k1_relat_1(sK3) & sK0 = k1_relat_1(sK2) & sK0 = k2_relat_1(sK1) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 2.12/0.66    introduced(choice_axiom,[])).
% 2.12/0.66  fof(f11,plain,(
% 2.12/0.66    ? [X0,X1] : (? [X2] : (? [X3] : (X2 != X3 & k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0 & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.12/0.66    inference(flattening,[],[f10])).
% 2.12/0.66  fof(f10,plain,(
% 2.12/0.66    ? [X0,X1] : (? [X2] : (? [X3] : ((X2 != X3 & (k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0)) & (v1_funct_1(X3) & v1_relat_1(X3))) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 2.12/0.66    inference(ennf_transformation,[],[f9])).
% 2.12/0.66  fof(f9,negated_conjecture,(
% 2.12/0.66    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0) => X2 = X3))))),
% 2.12/0.66    inference(negated_conjecture,[],[f8])).
% 2.12/0.66  fof(f8,conjecture,(
% 2.12/0.66    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0) => X2 = X3))))),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_funct_1)).
% 2.12/0.66  fof(f854,plain,(
% 2.12/0.66    ~v1_relat_1(sK3)),
% 2.12/0.66    inference(subsumption_resolution,[],[f849,f779])).
% 2.12/0.66  fof(f779,plain,(
% 2.12/0.66    ~r1_tarski(sK3,sK2)),
% 2.12/0.66    inference(subsumption_resolution,[],[f776,f58])).
% 2.12/0.66  fof(f58,plain,(
% 2.12/0.66    sK2 != sK3),
% 2.12/0.66    inference(cnf_transformation,[],[f23])).
% 2.12/0.66  fof(f776,plain,(
% 2.12/0.66    sK2 = sK3 | ~r1_tarski(sK3,sK2)),
% 2.12/0.66    inference(resolution,[],[f761,f71])).
% 2.12/0.66  fof(f71,plain,(
% 2.12/0.66    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f35])).
% 2.12/0.66  fof(f35,plain,(
% 2.12/0.66    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.12/0.66    inference(flattening,[],[f34])).
% 2.12/0.66  fof(f34,plain,(
% 2.12/0.66    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.12/0.66    inference(nnf_transformation,[],[f2])).
% 2.12/0.66  fof(f2,axiom,(
% 2.12/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.12/0.66  fof(f761,plain,(
% 2.12/0.66    r1_tarski(sK2,sK3)),
% 2.12/0.66    inference(subsumption_resolution,[],[f756,f50])).
% 2.12/0.66  fof(f50,plain,(
% 2.12/0.66    v1_relat_1(sK2)),
% 2.12/0.66    inference(cnf_transformation,[],[f23])).
% 2.12/0.66  fof(f756,plain,(
% 2.12/0.66    r1_tarski(sK2,sK3) | ~v1_relat_1(sK2)),
% 2.12/0.66    inference(duplicate_literal_removal,[],[f754])).
% 2.12/0.66  fof(f754,plain,(
% 2.12/0.66    r1_tarski(sK2,sK3) | r1_tarski(sK2,sK3) | ~v1_relat_1(sK2)),
% 2.12/0.66    inference(resolution,[],[f600,f61])).
% 2.12/0.66  fof(f61,plain,(
% 2.12/0.66    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f27])).
% 2.12/0.66  fof(f27,plain,(
% 2.12/0.66    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 2.12/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f25,f26])).
% 2.12/0.66  fof(f26,plain,(
% 2.12/0.66    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)))),
% 2.12/0.66    introduced(choice_axiom,[])).
% 2.12/0.66  fof(f25,plain,(
% 2.12/0.66    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 2.12/0.66    inference(rectify,[],[f24])).
% 2.12/0.66  fof(f24,plain,(
% 2.12/0.66    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 2.12/0.66    inference(nnf_transformation,[],[f12])).
% 2.12/0.66  fof(f12,plain,(
% 2.12/0.66    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 2.12/0.66    inference(ennf_transformation,[],[f3])).
% 2.12/0.66  fof(f3,axiom,(
% 2.12/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).
% 2.12/0.66  fof(f600,plain,(
% 2.12/0.66    ( ! [X0] : (r2_hidden(k4_tarski(sK4(sK2,X0),sK5(sK2,X0)),sK3) | r1_tarski(sK2,X0)) )),
% 2.12/0.66    inference(subsumption_resolution,[],[f597,f101])).
% 2.12/0.66  fof(f101,plain,(
% 2.12/0.66    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | r1_tarski(sK2,X0)) )),
% 2.12/0.66    inference(subsumption_resolution,[],[f99,f50])).
% 2.12/0.66  fof(f99,plain,(
% 2.12/0.66    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | ~v1_relat_1(sK2) | r1_tarski(sK2,X0)) )),
% 2.12/0.66    inference(superposition,[],[f98,f55])).
% 2.12/0.66  fof(f55,plain,(
% 2.12/0.66    sK0 = k1_relat_1(sK2)),
% 2.12/0.66    inference(cnf_transformation,[],[f23])).
% 2.12/0.66  fof(f98,plain,(
% 2.12/0.66    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | ~v1_relat_1(X0) | r1_tarski(X0,X1)) )),
% 2.12/0.66    inference(resolution,[],[f60,f88])).
% 2.12/0.66  fof(f88,plain,(
% 2.12/0.66    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 2.12/0.66    inference(equality_resolution,[],[f76])).
% 2.12/0.66  fof(f76,plain,(
% 2.12/0.66    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 2.12/0.66    inference(cnf_transformation,[],[f45])).
% 2.12/0.66  fof(f45,plain,(
% 2.12/0.66    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK10(X0,X1),X3),X0) | ~r2_hidden(sK10(X0,X1),X1)) & (r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0) | r2_hidden(sK10(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.12/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f41,f44,f43,f42])).
% 2.12/0.66  fof(f42,plain,(
% 2.12/0.66    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK10(X0,X1),X3),X0) | ~r2_hidden(sK10(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0) | r2_hidden(sK10(X0,X1),X1))))),
% 2.12/0.66    introduced(choice_axiom,[])).
% 2.12/0.66  fof(f43,plain,(
% 2.12/0.66    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0))),
% 2.12/0.66    introduced(choice_axiom,[])).
% 2.12/0.66  fof(f44,plain,(
% 2.12/0.66    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0))),
% 2.12/0.66    introduced(choice_axiom,[])).
% 2.12/0.66  fof(f41,plain,(
% 2.12/0.66    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.12/0.66    inference(rectify,[],[f40])).
% 2.12/0.66  fof(f40,plain,(
% 2.12/0.66    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.12/0.66    inference(nnf_transformation,[],[f4])).
% 2.12/0.66  fof(f4,axiom,(
% 2.12/0.66    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 2.12/0.66  fof(f60,plain,(
% 2.12/0.66    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f27])).
% 2.12/0.66  fof(f597,plain,(
% 2.12/0.66    ( ! [X0] : (r2_hidden(k4_tarski(sK4(sK2,X0),sK5(sK2,X0)),sK3) | ~r2_hidden(sK4(sK2,X0),sK0) | r1_tarski(sK2,X0)) )),
% 2.12/0.66    inference(superposition,[],[f568,f120])).
% 2.12/0.66  fof(f120,plain,(
% 2.12/0.66    ( ! [X1] : (k1_funct_1(sK2,sK4(sK2,X1)) = sK5(sK2,X1) | r1_tarski(sK2,X1)) )),
% 2.12/0.66    inference(subsumption_resolution,[],[f117,f50])).
% 2.12/0.66  fof(f117,plain,(
% 2.12/0.66    ( ! [X1] : (k1_funct_1(sK2,sK4(sK2,X1)) = sK5(sK2,X1) | r1_tarski(sK2,X1) | ~v1_relat_1(sK2)) )),
% 2.12/0.66    inference(resolution,[],[f110,f60])).
% 2.12/0.66  fof(f110,plain,(
% 2.12/0.66    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK2) | k1_funct_1(sK2,X2) = X3) )),
% 2.12/0.66    inference(subsumption_resolution,[],[f107,f50])).
% 2.12/0.66  fof(f107,plain,(
% 2.12/0.66    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK2) | k1_funct_1(sK2,X2) = X3 | ~v1_relat_1(sK2)) )),
% 2.12/0.66    inference(resolution,[],[f80,f51])).
% 2.12/0.66  fof(f51,plain,(
% 2.12/0.66    v1_funct_1(sK2)),
% 2.12/0.66    inference(cnf_transformation,[],[f23])).
% 2.12/0.66  fof(f80,plain,(
% 2.12/0.66    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f47])).
% 2.12/0.66  fof(f47,plain,(
% 2.12/0.66    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.12/0.66    inference(flattening,[],[f46])).
% 2.12/0.66  fof(f46,plain,(
% 2.12/0.66    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.12/0.66    inference(nnf_transformation,[],[f19])).
% 2.12/0.66  fof(f19,plain,(
% 2.12/0.66    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.12/0.66    inference(flattening,[],[f18])).
% 2.12/0.66  fof(f18,plain,(
% 2.12/0.66    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.12/0.66    inference(ennf_transformation,[],[f7])).
% 2.12/0.66  fof(f7,axiom,(
% 2.12/0.66    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 2.12/0.66  fof(f568,plain,(
% 2.12/0.66    ( ! [X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(sK2,X1)),sK3) | ~r2_hidden(X1,sK0)) )),
% 2.12/0.66    inference(duplicate_literal_removal,[],[f565])).
% 2.12/0.66  fof(f565,plain,(
% 2.12/0.66    ( ! [X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(sK2,X1)),sK3) | ~r2_hidden(X1,sK0) | ~r2_hidden(X1,sK0)) )),
% 2.12/0.66    inference(superposition,[],[f131,f560])).
% 2.12/0.66  fof(f560,plain,(
% 2.12/0.66    ( ! [X0] : (k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) | ~r2_hidden(X0,sK0)) )),
% 2.12/0.66    inference(duplicate_literal_removal,[],[f559])).
% 2.12/0.66  fof(f559,plain,(
% 2.12/0.66    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) | ~r2_hidden(X0,sK0)) )),
% 2.12/0.66    inference(forward_demodulation,[],[f558,f54])).
% 2.12/0.66  fof(f54,plain,(
% 2.12/0.66    sK0 = k2_relat_1(sK1)),
% 2.12/0.66    inference(cnf_transformation,[],[f23])).
% 2.12/0.66  fof(f558,plain,(
% 2.12/0.66    ( ! [X0] : (k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) | ~r2_hidden(X0,sK0) | ~r2_hidden(X0,k2_relat_1(sK1))) )),
% 2.12/0.66    inference(subsumption_resolution,[],[f557,f48])).
% 2.12/0.66  fof(f48,plain,(
% 2.12/0.66    v1_relat_1(sK1)),
% 2.12/0.66    inference(cnf_transformation,[],[f23])).
% 2.12/0.66  fof(f557,plain,(
% 2.12/0.66    ( ! [X0] : (k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) | ~r2_hidden(X0,sK0) | ~r2_hidden(X0,k2_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 2.12/0.66    inference(subsumption_resolution,[],[f555,f49])).
% 2.12/0.66  fof(f49,plain,(
% 2.12/0.66    v1_funct_1(sK1)),
% 2.12/0.66    inference(cnf_transformation,[],[f23])).
% 2.12/0.66  fof(f555,plain,(
% 2.12/0.66    ( ! [X0] : (k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) | ~r2_hidden(X0,sK0) | ~r2_hidden(X0,k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 2.12/0.66    inference(resolution,[],[f539,f85])).
% 2.12/0.66  fof(f85,plain,(
% 2.12/0.66    ( ! [X0,X5] : (r2_hidden(sK8(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.12/0.66    inference(equality_resolution,[],[f62])).
% 2.12/0.66  fof(f62,plain,(
% 2.12/0.66    ( ! [X0,X5,X1] : (r2_hidden(sK8(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f33])).
% 2.12/0.66  fof(f33,plain,(
% 2.12/0.66    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK6(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK6(X0,X1),X1)) & ((sK6(X0,X1) = k1_funct_1(X0,sK7(X0,X1)) & r2_hidden(sK7(X0,X1),k1_relat_1(X0))) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK8(X0,X5)) = X5 & r2_hidden(sK8(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.12/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f29,f32,f31,f30])).
% 2.12/0.66  fof(f30,plain,(
% 2.12/0.66    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK6(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK6(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK6(X0,X1),X1))))),
% 2.12/0.66    introduced(choice_axiom,[])).
% 2.12/0.66  fof(f31,plain,(
% 2.12/0.66    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK6(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK6(X0,X1) = k1_funct_1(X0,sK7(X0,X1)) & r2_hidden(sK7(X0,X1),k1_relat_1(X0))))),
% 2.12/0.66    introduced(choice_axiom,[])).
% 2.12/0.66  fof(f32,plain,(
% 2.12/0.66    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK8(X0,X5)) = X5 & r2_hidden(sK8(X0,X5),k1_relat_1(X0))))),
% 2.12/0.66    introduced(choice_axiom,[])).
% 2.12/0.66  fof(f29,plain,(
% 2.12/0.66    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.12/0.66    inference(rectify,[],[f28])).
% 2.12/0.66  fof(f28,plain,(
% 2.12/0.66    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.12/0.66    inference(nnf_transformation,[],[f14])).
% 2.12/0.66  fof(f14,plain,(
% 2.12/0.66    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.12/0.66    inference(flattening,[],[f13])).
% 2.12/0.66  fof(f13,plain,(
% 2.12/0.66    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.12/0.66    inference(ennf_transformation,[],[f5])).
% 2.12/0.66  fof(f5,axiom,(
% 2.12/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 2.12/0.66  fof(f539,plain,(
% 2.12/0.66    ( ! [X1] : (~r2_hidden(sK8(sK1,X1),k1_relat_1(sK1)) | k1_funct_1(sK3,X1) = k1_funct_1(sK2,X1) | ~r2_hidden(X1,sK0)) )),
% 2.12/0.66    inference(superposition,[],[f533,f269])).
% 2.12/0.66  fof(f269,plain,(
% 2.12/0.66    ( ! [X0] : (k1_funct_1(sK1,sK8(sK1,X0)) = X0 | ~r2_hidden(X0,sK0)) )),
% 2.12/0.66    inference(forward_demodulation,[],[f268,f54])).
% 2.12/0.66  fof(f268,plain,(
% 2.12/0.66    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(sK1,sK8(sK1,X0)) = X0) )),
% 2.12/0.66    inference(subsumption_resolution,[],[f265,f48])).
% 2.12/0.66  fof(f265,plain,(
% 2.12/0.66    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(sK1,sK8(sK1,X0)) = X0 | ~v1_relat_1(sK1)) )),
% 2.12/0.66    inference(resolution,[],[f84,f49])).
% 2.12/0.66  fof(f84,plain,(
% 2.12/0.66    ( ! [X0,X5] : (~v1_funct_1(X0) | ~r2_hidden(X5,k2_relat_1(X0)) | k1_funct_1(X0,sK8(X0,X5)) = X5 | ~v1_relat_1(X0)) )),
% 2.12/0.66    inference(equality_resolution,[],[f63])).
% 2.12/0.66  fof(f63,plain,(
% 2.12/0.66    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK8(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f33])).
% 2.12/0.66  fof(f533,plain,(
% 2.12/0.66    ( ! [X1] : (k1_funct_1(sK2,k1_funct_1(sK1,X1)) = k1_funct_1(sK3,k1_funct_1(sK1,X1)) | ~r2_hidden(X1,k1_relat_1(sK1))) )),
% 2.12/0.66    inference(subsumption_resolution,[],[f532,f48])).
% 2.12/0.66  fof(f532,plain,(
% 2.12/0.66    ( ! [X1] : (k1_funct_1(sK2,k1_funct_1(sK1,X1)) = k1_funct_1(sK3,k1_funct_1(sK1,X1)) | ~r2_hidden(X1,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 2.12/0.66    inference(subsumption_resolution,[],[f531,f49])).
% 2.12/0.66  fof(f531,plain,(
% 2.12/0.66    ( ! [X1] : (k1_funct_1(sK2,k1_funct_1(sK1,X1)) = k1_funct_1(sK3,k1_funct_1(sK1,X1)) | ~r2_hidden(X1,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 2.12/0.66    inference(subsumption_resolution,[],[f530,f50])).
% 2.12/0.66  fof(f530,plain,(
% 2.12/0.66    ( ! [X1] : (k1_funct_1(sK2,k1_funct_1(sK1,X1)) = k1_funct_1(sK3,k1_funct_1(sK1,X1)) | ~r2_hidden(X1,k1_relat_1(sK1)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 2.12/0.66    inference(subsumption_resolution,[],[f529,f51])).
% 2.12/0.66  fof(f529,plain,(
% 2.12/0.66    ( ! [X1] : (k1_funct_1(sK2,k1_funct_1(sK1,X1)) = k1_funct_1(sK3,k1_funct_1(sK1,X1)) | ~r2_hidden(X1,k1_relat_1(sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 2.12/0.66    inference(duplicate_literal_removal,[],[f526])).
% 2.12/0.66  fof(f526,plain,(
% 2.12/0.66    ( ! [X1] : (k1_funct_1(sK2,k1_funct_1(sK1,X1)) = k1_funct_1(sK3,k1_funct_1(sK1,X1)) | ~r2_hidden(X1,k1_relat_1(sK1)) | ~r2_hidden(X1,k1_relat_1(sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 2.12/0.66    inference(superposition,[],[f525,f68])).
% 2.12/0.66  fof(f68,plain,(
% 2.12/0.66    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f16])).
% 2.12/0.66  fof(f16,plain,(
% 2.12/0.66    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.12/0.66    inference(flattening,[],[f15])).
% 2.12/0.66  fof(f15,plain,(
% 2.12/0.66    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.12/0.66    inference(ennf_transformation,[],[f6])).
% 2.12/0.66  fof(f6,axiom,(
% 2.12/0.66    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
% 2.12/0.66  fof(f525,plain,(
% 2.12/0.66    ( ! [X0] : (k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0) | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 2.12/0.66    inference(subsumption_resolution,[],[f524,f48])).
% 2.12/0.66  fof(f524,plain,(
% 2.12/0.66    ( ! [X0] : (k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 2.12/0.66    inference(subsumption_resolution,[],[f523,f49])).
% 2.12/0.66  fof(f523,plain,(
% 2.12/0.66    ( ! [X0] : (k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 2.12/0.66    inference(subsumption_resolution,[],[f522,f52])).
% 2.12/0.66  fof(f522,plain,(
% 2.12/0.66    ( ! [X0] : (k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 2.12/0.66    inference(subsumption_resolution,[],[f521,f53])).
% 2.12/0.66  fof(f53,plain,(
% 2.12/0.66    v1_funct_1(sK3)),
% 2.12/0.66    inference(cnf_transformation,[],[f23])).
% 2.12/0.66  fof(f521,plain,(
% 2.12/0.66    ( ! [X0] : (k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 2.12/0.66    inference(superposition,[],[f68,f57])).
% 2.12/0.66  fof(f57,plain,(
% 2.12/0.66    k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3)),
% 2.12/0.66    inference(cnf_transformation,[],[f23])).
% 2.12/0.66  fof(f131,plain,(
% 2.12/0.66    ( ! [X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) | ~r2_hidden(X0,sK0)) )),
% 2.12/0.66    inference(duplicate_literal_removal,[],[f130])).
% 2.12/0.66  fof(f130,plain,(
% 2.12/0.66    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) | ~r2_hidden(X0,sK0)) )),
% 2.12/0.66    inference(forward_demodulation,[],[f129,f56])).
% 2.12/0.66  fof(f56,plain,(
% 2.12/0.66    sK0 = k1_relat_1(sK3)),
% 2.12/0.66    inference(cnf_transformation,[],[f23])).
% 2.12/0.66  fof(f129,plain,(
% 2.12/0.66    ( ! [X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) | ~r2_hidden(X0,k1_relat_1(sK3)) | ~r2_hidden(X0,sK0)) )),
% 2.12/0.66    inference(superposition,[],[f89,f124])).
% 2.12/0.66  fof(f124,plain,(
% 2.12/0.66    ( ! [X0] : (k1_funct_1(sK3,X0) = sK12(sK3,X0) | ~r2_hidden(X0,sK0)) )),
% 2.12/0.66    inference(forward_demodulation,[],[f121,f56])).
% 2.12/0.66  fof(f121,plain,(
% 2.12/0.66    ( ! [X0] : (k1_funct_1(sK3,X0) = sK12(sK3,X0) | ~r2_hidden(X0,k1_relat_1(sK3))) )),
% 2.12/0.66    inference(resolution,[],[f111,f89])).
% 2.12/0.66  fof(f111,plain,(
% 2.12/0.66    ( ! [X4,X5] : (~r2_hidden(k4_tarski(X4,X5),sK3) | k1_funct_1(sK3,X4) = X5) )),
% 2.12/0.66    inference(subsumption_resolution,[],[f108,f52])).
% 2.12/0.66  fof(f108,plain,(
% 2.12/0.66    ( ! [X4,X5] : (~r2_hidden(k4_tarski(X4,X5),sK3) | k1_funct_1(sK3,X4) = X5 | ~v1_relat_1(sK3)) )),
% 2.12/0.66    inference(resolution,[],[f80,f53])).
% 2.12/0.66  fof(f89,plain,(
% 2.12/0.66    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 2.12/0.66    inference(equality_resolution,[],[f75])).
% 2.12/0.66  fof(f75,plain,(
% 2.12/0.66    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 2.12/0.66    inference(cnf_transformation,[],[f45])).
% 2.12/0.66  fof(f849,plain,(
% 2.12/0.66    r1_tarski(sK3,sK2) | ~v1_relat_1(sK3)),
% 2.12/0.66    inference(duplicate_literal_removal,[],[f847])).
% 2.12/0.66  fof(f847,plain,(
% 2.12/0.66    r1_tarski(sK3,sK2) | r1_tarski(sK3,sK2) | ~v1_relat_1(sK3)),
% 2.12/0.66    inference(resolution,[],[f744,f61])).
% 2.12/0.66  fof(f744,plain,(
% 2.12/0.66    ( ! [X2] : (r2_hidden(k4_tarski(sK4(sK3,X2),sK5(sK3,X2)),sK2) | r1_tarski(sK3,X2)) )),
% 2.12/0.66    inference(subsumption_resolution,[],[f743,f102])).
% 2.12/0.66  fof(f102,plain,(
% 2.12/0.66    ( ! [X1] : (r2_hidden(sK4(sK3,X1),sK0) | r1_tarski(sK3,X1)) )),
% 2.12/0.66    inference(subsumption_resolution,[],[f100,f52])).
% 2.12/0.66  fof(f100,plain,(
% 2.12/0.66    ( ! [X1] : (r2_hidden(sK4(sK3,X1),sK0) | ~v1_relat_1(sK3) | r1_tarski(sK3,X1)) )),
% 2.12/0.66    inference(superposition,[],[f98,f56])).
% 2.12/0.66  fof(f743,plain,(
% 2.12/0.66    ( ! [X2] : (r2_hidden(k4_tarski(sK4(sK3,X2),sK5(sK3,X2)),sK2) | ~r2_hidden(sK4(sK3,X2),sK0) | r1_tarski(sK3,X2)) )),
% 2.12/0.66    inference(superposition,[],[f128,f570])).
% 2.12/0.66  fof(f570,plain,(
% 2.12/0.66    ( ! [X2] : (sK5(sK3,X2) = k1_funct_1(sK2,sK4(sK3,X2)) | r1_tarski(sK3,X2)) )),
% 2.12/0.66    inference(subsumption_resolution,[],[f562,f102])).
% 2.12/0.66  fof(f562,plain,(
% 2.12/0.66    ( ! [X2] : (sK5(sK3,X2) = k1_funct_1(sK2,sK4(sK3,X2)) | ~r2_hidden(sK4(sK3,X2),sK0) | r1_tarski(sK3,X2)) )),
% 2.12/0.66    inference(superposition,[],[f560,f125])).
% 2.12/0.66  fof(f125,plain,(
% 2.12/0.66    ( ! [X1] : (k1_funct_1(sK3,sK4(sK3,X1)) = sK5(sK3,X1) | r1_tarski(sK3,X1)) )),
% 2.12/0.66    inference(subsumption_resolution,[],[f122,f52])).
% 2.12/0.66  fof(f122,plain,(
% 2.12/0.66    ( ! [X1] : (k1_funct_1(sK3,sK4(sK3,X1)) = sK5(sK3,X1) | r1_tarski(sK3,X1) | ~v1_relat_1(sK3)) )),
% 2.12/0.66    inference(resolution,[],[f111,f60])).
% 2.12/0.66  fof(f128,plain,(
% 2.12/0.66    ( ! [X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2) | ~r2_hidden(X0,sK0)) )),
% 2.12/0.66    inference(duplicate_literal_removal,[],[f127])).
% 2.12/0.66  fof(f127,plain,(
% 2.12/0.66    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2) | ~r2_hidden(X0,sK0)) )),
% 2.12/0.66    inference(forward_demodulation,[],[f126,f55])).
% 2.12/0.66  fof(f126,plain,(
% 2.12/0.66    ( ! [X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2) | ~r2_hidden(X0,k1_relat_1(sK2)) | ~r2_hidden(X0,sK0)) )),
% 2.12/0.66    inference(superposition,[],[f89,f119])).
% 2.12/0.66  fof(f119,plain,(
% 2.12/0.66    ( ! [X0] : (k1_funct_1(sK2,X0) = sK12(sK2,X0) | ~r2_hidden(X0,sK0)) )),
% 2.12/0.66    inference(forward_demodulation,[],[f116,f55])).
% 2.12/0.66  fof(f116,plain,(
% 2.12/0.66    ( ! [X0] : (k1_funct_1(sK2,X0) = sK12(sK2,X0) | ~r2_hidden(X0,k1_relat_1(sK2))) )),
% 2.12/0.66    inference(resolution,[],[f110,f89])).
% 2.12/0.66  % SZS output end Proof for theBenchmark
% 2.12/0.66  % (5983)------------------------------
% 2.12/0.66  % (5983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.66  % (5983)Termination reason: Refutation
% 2.12/0.66  
% 2.12/0.66  % (5983)Memory used [KB]: 11385
% 2.12/0.66  % (5983)Time elapsed: 0.248 s
% 2.12/0.66  % (5983)------------------------------
% 2.12/0.66  % (5983)------------------------------
% 2.12/0.67  % (5977)Success in time 0.303 s
%------------------------------------------------------------------------------
