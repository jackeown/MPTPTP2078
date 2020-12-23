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
% DateTime   : Thu Dec  3 12:51:53 EST 2020

% Result     : Theorem 1.97s
% Output     : Refutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 336 expanded)
%              Number of leaves         :   13 ( 105 expanded)
%              Depth                    :   25
%              Number of atoms          :  391 (2004 expanded)
%              Number of equality atoms :  183 ( 898 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f827,plain,(
    $false ),
    inference(subsumption_resolution,[],[f786,f650])).

fof(f650,plain,(
    ! [X5] : ~ r2_hidden(X5,sK0) ),
    inference(subsumption_resolution,[],[f647,f52])).

fof(f52,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f647,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK0)
      | ~ r2_hidden(sK1,k1_tarski(sK1)) ) ),
    inference(trivial_inequality_removal,[],[f633])).

fof(f633,plain,(
    ! [X5] :
      ( sK1 != sK1
      | sK0 != sK0
      | ~ r2_hidden(X5,sK0)
      | k1_tarski(sK1) != k1_tarski(sK1)
      | ~ r2_hidden(sK1,k1_tarski(sK1)) ) ),
    inference(superposition,[],[f77,f610])).

fof(f610,plain,(
    sK1 = sK2(sK7(sK0,sK1),k1_tarski(sK1)) ),
    inference(equality_resolution,[],[f539])).

fof(f539,plain,(
    ! [X0] :
      ( sK1 != X0
      | sK1 = sK2(sK7(sK0,X0),k1_tarski(sK1)) ) ),
    inference(equality_factoring,[],[f246])).

fof(f246,plain,(
    ! [X2] :
      ( sK2(sK7(sK0,X2),k1_tarski(sK1)) = X2
      | sK1 = sK2(sK7(sK0,X2),k1_tarski(sK1)) ) ),
    inference(resolution,[],[f204,f53])).

fof(f53,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f204,plain,(
    ! [X2] :
      ( r2_hidden(sK2(sK7(sK0,X2),k1_tarski(sK1)),k1_tarski(sK1))
      | sK2(sK7(sK0,X2),k1_tarski(sK1)) = X2 ) ),
    inference(subsumption_resolution,[],[f197,f89])).

fof(f89,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK7(sK0,X0),k1_tarski(sK1)),k1_tarski(sK1))
      | r2_hidden(sK3(sK7(sK0,X0),k1_tarski(sK1)),sK0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | r2_hidden(sK3(sK7(X0,X1),k1_tarski(sK1)),X0)
      | r2_hidden(sK2(sK7(X0,X1),k1_tarski(sK1)),k1_tarski(sK1)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(sK1) != X2
      | sK0 != X0
      | r2_hidden(sK3(sK7(X0,X1),X2),X0)
      | r2_hidden(sK2(sK7(X0,X1),X2),X2) ) ),
    inference(subsumption_resolution,[],[f61,f43])).

fof(f43,plain,(
    ! [X0,X1] : v1_relat_1(sK7(X0,X1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK7(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK7(X0,X1)) = X0
      & v1_funct_1(sK7(X0,X1))
      & v1_relat_1(sK7(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f11,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK7(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK7(X0,X1)) = X0
        & v1_funct_1(sK7(X0,X1))
        & v1_relat_1(sK7(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X0
      | k1_tarski(sK1) != X2
      | ~ v1_relat_1(sK7(X0,X1))
      | r2_hidden(sK3(sK7(X0,X1),X2),X0)
      | r2_hidden(sK2(sK7(X0,X1),X2),X2) ) ),
    inference(subsumption_resolution,[],[f60,f44])).

fof(f44,plain,(
    ! [X0,X1] : v1_funct_1(sK7(X0,X1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X0
      | k1_tarski(sK1) != X2
      | ~ v1_funct_1(sK7(X0,X1))
      | ~ v1_relat_1(sK7(X0,X1))
      | r2_hidden(sK3(sK7(X0,X1),X2),X0)
      | r2_hidden(sK2(sK7(X0,X1),X2),X2) ) ),
    inference(superposition,[],[f59,f45])).

fof(f45,plain,(
    ! [X0,X1] : k1_relat_1(sK7(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != sK0
      | k1_tarski(sK1) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_tarski(sK1) != X1
      | k1_relat_1(X0) != sK0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK2(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f30,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK2(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK2(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ( sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
                  & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK4(X0,X5)) = X5
                    & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f19,f18,f17])).

fof(f17,plain,(
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
              ( k1_funct_1(X0,X3) != sK2(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK2(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK2(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f30,plain,(
    ! [X2] :
      ( k2_relat_1(X2) != k1_tarski(sK1)
      | k1_relat_1(X2) != sK0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ! [X2] :
        ( k2_relat_1(X2) != k1_tarski(sK1)
        | k1_relat_1(X2) != sK0
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f13,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
          ! [X2] :
            ( k1_tarski(X1) != k2_relat_1(X2)
            | k1_relat_1(X2) != X0
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & k1_xboole_0 != X0 )
   => ( ? [X1] :
        ! [X2] :
          ( k1_tarski(X1) != k2_relat_1(X2)
          | k1_relat_1(X2) != sK0
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
      ! [X2] :
        ( k1_tarski(X1) != k2_relat_1(X2)
        | k1_relat_1(X2) != sK0
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
   => ! [X2] :
        ( k2_relat_1(X2) != k1_tarski(sK1)
        | k1_relat_1(X2) != sK0
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
        ! [X2] :
          ( k1_tarski(X1) != k2_relat_1(X2)
          | k1_relat_1(X2) != X0
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( k1_xboole_0 != X0
       => ! [X1] :
          ? [X2] :
            ( k1_tarski(X1) = k2_relat_1(X2)
            & k1_relat_1(X2) = X0
            & v1_funct_1(X2)
            & v1_relat_1(X2) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f197,plain,(
    ! [X2] :
      ( sK2(sK7(sK0,X2),k1_tarski(sK1)) = X2
      | r2_hidden(sK2(sK7(sK0,X2),k1_tarski(sK1)),k1_tarski(sK1))
      | ~ r2_hidden(sK3(sK7(sK0,X2),k1_tarski(sK1)),sK0) ) ),
    inference(superposition,[],[f105,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK7(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f105,plain,(
    ! [X0] :
      ( sK2(sK7(sK0,X0),k1_tarski(sK1)) = k1_funct_1(sK7(sK0,X0),sK3(sK7(sK0,X0),k1_tarski(sK1)))
      | r2_hidden(sK2(sK7(sK0,X0),k1_tarski(sK1)),k1_tarski(sK1)) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK2(sK7(X0,X1),k1_tarski(sK1)) = k1_funct_1(sK7(X0,X1),sK3(sK7(X0,X1),k1_tarski(sK1)))
      | r2_hidden(sK2(sK7(X0,X1),k1_tarski(sK1)),k1_tarski(sK1)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(sK1) != X2
      | sK0 != X0
      | sK2(sK7(X0,X1),X2) = k1_funct_1(sK7(X0,X1),sK3(sK7(X0,X1),X2))
      | r2_hidden(sK2(sK7(X0,X1),X2),X2) ) ),
    inference(subsumption_resolution,[],[f64,f43])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X0
      | k1_tarski(sK1) != X2
      | ~ v1_relat_1(sK7(X0,X1))
      | sK2(sK7(X0,X1),X2) = k1_funct_1(sK7(X0,X1),sK3(sK7(X0,X1),X2))
      | r2_hidden(sK2(sK7(X0,X1),X2),X2) ) ),
    inference(subsumption_resolution,[],[f63,f44])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X0
      | k1_tarski(sK1) != X2
      | ~ v1_funct_1(sK7(X0,X1))
      | ~ v1_relat_1(sK7(X0,X1))
      | sK2(sK7(X0,X1),X2) = k1_funct_1(sK7(X0,X1),sK3(sK7(X0,X1),X2))
      | r2_hidden(sK2(sK7(X0,X1),X2),X2) ) ),
    inference(superposition,[],[f58,f45])).

fof(f58,plain,(
    ! [X2,X3] :
      ( k1_relat_1(X2) != sK0
      | k1_tarski(sK1) != X3
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | sK2(X2,X3) = k1_funct_1(X2,sK3(X2,X3))
      | r2_hidden(sK2(X2,X3),X3) ) ),
    inference(duplicate_literal_removal,[],[f55])).

fof(f55,plain,(
    ! [X2,X3] :
      ( k1_tarski(sK1) != X3
      | k1_relat_1(X2) != sK0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | sK2(X2,X3) = k1_funct_1(X2,sK3(X2,X3))
      | r2_hidden(sK2(X2,X3),X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f30,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
      | r2_hidden(sK2(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f77,plain,(
    ! [X6,X8,X7,X9] :
      ( sK2(sK7(X6,X7),X9) != X7
      | sK0 != X6
      | ~ r2_hidden(X8,X6)
      | k1_tarski(sK1) != X9
      | ~ r2_hidden(sK2(sK7(X6,X7),X9),X9) ) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ r2_hidden(X8,X6)
      | sK0 != X6
      | sK2(sK7(X6,X7),X9) != X7
      | k1_tarski(sK1) != X9
      | ~ r2_hidden(sK2(sK7(X6,X7),X9),X9)
      | ~ r2_hidden(X8,X6) ) ),
    inference(forward_demodulation,[],[f75,f45])).

fof(f75,plain,(
    ! [X6,X8,X7,X9] :
      ( sK0 != X6
      | sK2(sK7(X6,X7),X9) != X7
      | k1_tarski(sK1) != X9
      | ~ r2_hidden(X8,k1_relat_1(sK7(X6,X7)))
      | ~ r2_hidden(sK2(sK7(X6,X7),X9),X9)
      | ~ r2_hidden(X8,X6) ) ),
    inference(forward_demodulation,[],[f74,f45])).

fof(f74,plain,(
    ! [X6,X8,X7,X9] :
      ( sK2(sK7(X6,X7),X9) != X7
      | sK0 != k1_relat_1(sK7(X6,X7))
      | k1_tarski(sK1) != X9
      | ~ r2_hidden(X8,k1_relat_1(sK7(X6,X7)))
      | ~ r2_hidden(sK2(sK7(X6,X7),X9),X9)
      | ~ r2_hidden(X8,X6) ) ),
    inference(subsumption_resolution,[],[f73,f43])).

fof(f73,plain,(
    ! [X6,X8,X7,X9] :
      ( sK2(sK7(X6,X7),X9) != X7
      | sK0 != k1_relat_1(sK7(X6,X7))
      | ~ v1_relat_1(sK7(X6,X7))
      | k1_tarski(sK1) != X9
      | ~ r2_hidden(X8,k1_relat_1(sK7(X6,X7)))
      | ~ r2_hidden(sK2(sK7(X6,X7),X9),X9)
      | ~ r2_hidden(X8,X6) ) ),
    inference(subsumption_resolution,[],[f68,f44])).

fof(f68,plain,(
    ! [X6,X8,X7,X9] :
      ( sK2(sK7(X6,X7),X9) != X7
      | sK0 != k1_relat_1(sK7(X6,X7))
      | ~ v1_funct_1(sK7(X6,X7))
      | ~ v1_relat_1(sK7(X6,X7))
      | k1_tarski(sK1) != X9
      | ~ r2_hidden(X8,k1_relat_1(sK7(X6,X7)))
      | ~ r2_hidden(sK2(sK7(X6,X7),X9),X9)
      | ~ r2_hidden(X8,X6) ) ),
    inference(superposition,[],[f57,f46])).

fof(f57,plain,(
    ! [X6,X4,X5] :
      ( k1_funct_1(X4,X6) != sK2(X4,X5)
      | sK0 != k1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | k1_tarski(sK1) != X5
      | ~ r2_hidden(X6,k1_relat_1(X4))
      | ~ r2_hidden(sK2(X4,X5),X5) ) ),
    inference(duplicate_literal_removal,[],[f56])).

fof(f56,plain,(
    ! [X6,X4,X5] :
      ( k1_tarski(sK1) != X5
      | sK0 != k1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | k1_funct_1(X4,X6) != sK2(X4,X5)
      | ~ r2_hidden(X6,k1_relat_1(X4))
      | ~ r2_hidden(sK2(X4,X5),X5)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f30,f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | k1_funct_1(X0,X3) != sK2(X0,X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(sK2(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f786,plain,(
    ! [X3] : r2_hidden(X3,sK0) ),
    inference(backward_demodulation,[],[f52,f702])).

fof(f702,plain,(
    ! [X14] : sK0 = k1_tarski(X14) ),
    inference(subsumption_resolution,[],[f699,f29])).

fof(f29,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).

fof(f699,plain,(
    ! [X14] :
      ( k1_xboole_0 = sK0
      | sK0 = k1_tarski(X14) ) ),
    inference(resolution,[],[f650,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( sK6(X0,X1) != X1
        & r2_hidden(sK6(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f10,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK6(X0,X1) != X1
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:30:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (10633)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (10633)Refutation not found, incomplete strategy% (10633)------------------------------
% 0.22/0.52  % (10633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (10633)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (10633)Memory used [KB]: 6140
% 0.22/0.52  % (10633)Time elapsed: 0.090 s
% 0.22/0.52  % (10633)------------------------------
% 0.22/0.52  % (10633)------------------------------
% 0.22/0.52  % (10647)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (10631)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (10641)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (10628)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (10649)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (10651)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (10641)Refutation not found, incomplete strategy% (10641)------------------------------
% 0.22/0.52  % (10641)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (10641)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (10641)Memory used [KB]: 6140
% 0.22/0.52  % (10641)Time elapsed: 0.109 s
% 0.22/0.52  % (10641)------------------------------
% 0.22/0.52  % (10641)------------------------------
% 0.22/0.52  % (10629)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (10629)Refutation not found, incomplete strategy% (10629)------------------------------
% 0.22/0.52  % (10629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (10629)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (10629)Memory used [KB]: 10618
% 0.22/0.52  % (10629)Time elapsed: 0.098 s
% 0.22/0.52  % (10629)------------------------------
% 0.22/0.52  % (10629)------------------------------
% 0.22/0.53  % (10636)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.53  % (10638)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.53  % (10646)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.53  % (10639)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.53  % (10644)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.53  % (10632)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  % (10634)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.54  % (10648)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.54  % (10652)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.54  % (10637)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.54  % (10635)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.54  % (10640)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.54  % (10630)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.55  % (10643)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.56  % (10645)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.56  % (10642)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.56  % (10634)Refutation not found, incomplete strategy% (10634)------------------------------
% 0.22/0.56  % (10634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (10634)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (10634)Memory used [KB]: 10618
% 0.22/0.56  % (10634)Time elapsed: 0.136 s
% 0.22/0.56  % (10634)------------------------------
% 0.22/0.56  % (10634)------------------------------
% 0.22/0.56  % (10650)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.56  % (10653)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.97/0.62  % (10646)Refutation found. Thanks to Tanya!
% 1.97/0.62  % SZS status Theorem for theBenchmark
% 1.97/0.62  % SZS output start Proof for theBenchmark
% 1.97/0.62  fof(f827,plain,(
% 1.97/0.62    $false),
% 1.97/0.62    inference(subsumption_resolution,[],[f786,f650])).
% 1.97/0.62  fof(f650,plain,(
% 1.97/0.62    ( ! [X5] : (~r2_hidden(X5,sK0)) )),
% 1.97/0.62    inference(subsumption_resolution,[],[f647,f52])).
% 1.97/0.62  fof(f52,plain,(
% 1.97/0.62    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 1.97/0.62    inference(equality_resolution,[],[f51])).
% 1.97/0.62  fof(f51,plain,(
% 1.97/0.62    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 1.97/0.62    inference(equality_resolution,[],[f38])).
% 1.97/0.62  fof(f38,plain,(
% 1.97/0.62    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.97/0.62    inference(cnf_transformation,[],[f24])).
% 1.97/0.62  fof(f24,plain,(
% 1.97/0.62    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.97/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).
% 1.97/0.62  fof(f23,plain,(
% 1.97/0.62    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 1.97/0.62    introduced(choice_axiom,[])).
% 1.97/0.62  fof(f22,plain,(
% 1.97/0.62    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.97/0.62    inference(rectify,[],[f21])).
% 1.97/0.62  fof(f21,plain,(
% 1.97/0.62    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.97/0.62    inference(nnf_transformation,[],[f1])).
% 1.97/0.62  fof(f1,axiom,(
% 1.97/0.62    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.97/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.97/0.62  fof(f647,plain,(
% 1.97/0.62    ( ! [X5] : (~r2_hidden(X5,sK0) | ~r2_hidden(sK1,k1_tarski(sK1))) )),
% 1.97/0.62    inference(trivial_inequality_removal,[],[f633])).
% 1.97/0.62  fof(f633,plain,(
% 1.97/0.62    ( ! [X5] : (sK1 != sK1 | sK0 != sK0 | ~r2_hidden(X5,sK0) | k1_tarski(sK1) != k1_tarski(sK1) | ~r2_hidden(sK1,k1_tarski(sK1))) )),
% 1.97/0.62    inference(superposition,[],[f77,f610])).
% 1.97/0.62  fof(f610,plain,(
% 1.97/0.62    sK1 = sK2(sK7(sK0,sK1),k1_tarski(sK1))),
% 1.97/0.62    inference(equality_resolution,[],[f539])).
% 1.97/0.62  fof(f539,plain,(
% 1.97/0.62    ( ! [X0] : (sK1 != X0 | sK1 = sK2(sK7(sK0,X0),k1_tarski(sK1))) )),
% 1.97/0.62    inference(equality_factoring,[],[f246])).
% 1.97/0.62  fof(f246,plain,(
% 1.97/0.62    ( ! [X2] : (sK2(sK7(sK0,X2),k1_tarski(sK1)) = X2 | sK1 = sK2(sK7(sK0,X2),k1_tarski(sK1))) )),
% 1.97/0.62    inference(resolution,[],[f204,f53])).
% 1.97/0.62  fof(f53,plain,(
% 1.97/0.62    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 1.97/0.62    inference(equality_resolution,[],[f37])).
% 1.97/0.62  fof(f37,plain,(
% 1.97/0.62    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.97/0.62    inference(cnf_transformation,[],[f24])).
% 1.97/0.62  fof(f204,plain,(
% 1.97/0.62    ( ! [X2] : (r2_hidden(sK2(sK7(sK0,X2),k1_tarski(sK1)),k1_tarski(sK1)) | sK2(sK7(sK0,X2),k1_tarski(sK1)) = X2) )),
% 1.97/0.62    inference(subsumption_resolution,[],[f197,f89])).
% 1.97/0.62  fof(f89,plain,(
% 1.97/0.62    ( ! [X0] : (r2_hidden(sK2(sK7(sK0,X0),k1_tarski(sK1)),k1_tarski(sK1)) | r2_hidden(sK3(sK7(sK0,X0),k1_tarski(sK1)),sK0)) )),
% 1.97/0.62    inference(equality_resolution,[],[f82])).
% 1.97/0.62  fof(f82,plain,(
% 1.97/0.62    ( ! [X0,X1] : (sK0 != X0 | r2_hidden(sK3(sK7(X0,X1),k1_tarski(sK1)),X0) | r2_hidden(sK2(sK7(X0,X1),k1_tarski(sK1)),k1_tarski(sK1))) )),
% 1.97/0.62    inference(equality_resolution,[],[f62])).
% 1.97/0.62  fof(f62,plain,(
% 1.97/0.62    ( ! [X2,X0,X1] : (k1_tarski(sK1) != X2 | sK0 != X0 | r2_hidden(sK3(sK7(X0,X1),X2),X0) | r2_hidden(sK2(sK7(X0,X1),X2),X2)) )),
% 1.97/0.62    inference(subsumption_resolution,[],[f61,f43])).
% 1.97/0.62  fof(f43,plain,(
% 1.97/0.62    ( ! [X0,X1] : (v1_relat_1(sK7(X0,X1))) )),
% 1.97/0.62    inference(cnf_transformation,[],[f28])).
% 1.97/0.62  fof(f28,plain,(
% 1.97/0.62    ! [X0,X1] : (! [X3] : (k1_funct_1(sK7(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK7(X0,X1)) = X0 & v1_funct_1(sK7(X0,X1)) & v1_relat_1(sK7(X0,X1)))),
% 1.97/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f11,f27])).
% 1.97/0.62  fof(f27,plain,(
% 1.97/0.62    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK7(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK7(X0,X1)) = X0 & v1_funct_1(sK7(X0,X1)) & v1_relat_1(sK7(X0,X1))))),
% 1.97/0.62    introduced(choice_axiom,[])).
% 1.97/0.62  fof(f11,plain,(
% 1.97/0.62    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.97/0.62    inference(ennf_transformation,[],[f4])).
% 1.97/0.62  fof(f4,axiom,(
% 1.97/0.62    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.97/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 1.97/0.62  fof(f61,plain,(
% 1.97/0.62    ( ! [X2,X0,X1] : (sK0 != X0 | k1_tarski(sK1) != X2 | ~v1_relat_1(sK7(X0,X1)) | r2_hidden(sK3(sK7(X0,X1),X2),X0) | r2_hidden(sK2(sK7(X0,X1),X2),X2)) )),
% 1.97/0.62    inference(subsumption_resolution,[],[f60,f44])).
% 1.97/0.62  fof(f44,plain,(
% 1.97/0.62    ( ! [X0,X1] : (v1_funct_1(sK7(X0,X1))) )),
% 1.97/0.62    inference(cnf_transformation,[],[f28])).
% 1.97/0.62  fof(f60,plain,(
% 1.97/0.62    ( ! [X2,X0,X1] : (sK0 != X0 | k1_tarski(sK1) != X2 | ~v1_funct_1(sK7(X0,X1)) | ~v1_relat_1(sK7(X0,X1)) | r2_hidden(sK3(sK7(X0,X1),X2),X0) | r2_hidden(sK2(sK7(X0,X1),X2),X2)) )),
% 1.97/0.62    inference(superposition,[],[f59,f45])).
% 1.97/0.62  fof(f45,plain,(
% 1.97/0.62    ( ! [X0,X1] : (k1_relat_1(sK7(X0,X1)) = X0) )),
% 1.97/0.62    inference(cnf_transformation,[],[f28])).
% 1.97/0.62  fof(f59,plain,(
% 1.97/0.62    ( ! [X0,X1] : (k1_relat_1(X0) != sK0 | k1_tarski(sK1) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | r2_hidden(sK2(X0,X1),X1)) )),
% 1.97/0.62    inference(duplicate_literal_removal,[],[f54])).
% 1.97/0.62  fof(f54,plain,(
% 1.97/0.62    ( ! [X0,X1] : (k1_tarski(sK1) != X1 | k1_relat_1(X0) != sK0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | r2_hidden(sK2(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.97/0.62    inference(superposition,[],[f30,f34])).
% 1.97/0.62  fof(f34,plain,(
% 1.97/0.62    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | r2_hidden(sK2(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.97/0.62    inference(cnf_transformation,[],[f20])).
% 1.97/0.62  fof(f20,plain,(
% 1.97/0.62    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & ((sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.97/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f19,f18,f17])).
% 1.97/0.62  fof(f17,plain,(
% 1.97/0.62    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1))))),
% 1.97/0.62    introduced(choice_axiom,[])).
% 1.97/0.62  fof(f18,plain,(
% 1.97/0.62    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))),
% 1.97/0.62    introduced(choice_axiom,[])).
% 1.97/0.62  fof(f19,plain,(
% 1.97/0.62    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))))),
% 1.97/0.62    introduced(choice_axiom,[])).
% 1.97/0.62  fof(f16,plain,(
% 1.97/0.62    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.97/0.62    inference(rectify,[],[f15])).
% 1.97/0.62  fof(f15,plain,(
% 1.97/0.62    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.97/0.62    inference(nnf_transformation,[],[f9])).
% 1.97/0.62  fof(f9,plain,(
% 1.97/0.62    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.97/0.62    inference(flattening,[],[f8])).
% 1.97/0.62  fof(f8,plain,(
% 1.97/0.62    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.97/0.62    inference(ennf_transformation,[],[f3])).
% 1.97/0.62  fof(f3,axiom,(
% 1.97/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.97/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 1.97/0.62  fof(f30,plain,(
% 1.97/0.62    ( ! [X2] : (k2_relat_1(X2) != k1_tarski(sK1) | k1_relat_1(X2) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.97/0.62    inference(cnf_transformation,[],[f14])).
% 1.97/0.62  fof(f14,plain,(
% 1.97/0.62    ! [X2] : (k2_relat_1(X2) != k1_tarski(sK1) | k1_relat_1(X2) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & k1_xboole_0 != sK0),
% 1.97/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f13,f12])).
% 1.97/0.62  fof(f12,plain,(
% 1.97/0.62    ? [X0] : (? [X1] : ! [X2] : (k1_tarski(X1) != k2_relat_1(X2) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & k1_xboole_0 != X0) => (? [X1] : ! [X2] : (k1_tarski(X1) != k2_relat_1(X2) | k1_relat_1(X2) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & k1_xboole_0 != sK0)),
% 1.97/0.62    introduced(choice_axiom,[])).
% 1.97/0.62  fof(f13,plain,(
% 1.97/0.62    ? [X1] : ! [X2] : (k1_tarski(X1) != k2_relat_1(X2) | k1_relat_1(X2) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) => ! [X2] : (k2_relat_1(X2) != k1_tarski(sK1) | k1_relat_1(X2) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.97/0.62    introduced(choice_axiom,[])).
% 1.97/0.62  fof(f7,plain,(
% 1.97/0.62    ? [X0] : (? [X1] : ! [X2] : (k1_tarski(X1) != k2_relat_1(X2) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & k1_xboole_0 != X0)),
% 1.97/0.62    inference(ennf_transformation,[],[f6])).
% 1.97/0.62  fof(f6,negated_conjecture,(
% 1.97/0.62    ~! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.97/0.62    inference(negated_conjecture,[],[f5])).
% 1.97/0.62  fof(f5,conjecture,(
% 1.97/0.62    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.97/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 1.97/0.62  fof(f197,plain,(
% 1.97/0.62    ( ! [X2] : (sK2(sK7(sK0,X2),k1_tarski(sK1)) = X2 | r2_hidden(sK2(sK7(sK0,X2),k1_tarski(sK1)),k1_tarski(sK1)) | ~r2_hidden(sK3(sK7(sK0,X2),k1_tarski(sK1)),sK0)) )),
% 1.97/0.62    inference(superposition,[],[f105,f46])).
% 1.97/0.62  fof(f46,plain,(
% 1.97/0.62    ( ! [X0,X3,X1] : (k1_funct_1(sK7(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 1.97/0.62    inference(cnf_transformation,[],[f28])).
% 1.97/0.62  fof(f105,plain,(
% 1.97/0.62    ( ! [X0] : (sK2(sK7(sK0,X0),k1_tarski(sK1)) = k1_funct_1(sK7(sK0,X0),sK3(sK7(sK0,X0),k1_tarski(sK1))) | r2_hidden(sK2(sK7(sK0,X0),k1_tarski(sK1)),k1_tarski(sK1))) )),
% 1.97/0.62    inference(equality_resolution,[],[f88])).
% 1.97/0.62  fof(f88,plain,(
% 1.97/0.62    ( ! [X0,X1] : (sK0 != X0 | sK2(sK7(X0,X1),k1_tarski(sK1)) = k1_funct_1(sK7(X0,X1),sK3(sK7(X0,X1),k1_tarski(sK1))) | r2_hidden(sK2(sK7(X0,X1),k1_tarski(sK1)),k1_tarski(sK1))) )),
% 1.97/0.62    inference(equality_resolution,[],[f65])).
% 1.97/0.62  fof(f65,plain,(
% 1.97/0.62    ( ! [X2,X0,X1] : (k1_tarski(sK1) != X2 | sK0 != X0 | sK2(sK7(X0,X1),X2) = k1_funct_1(sK7(X0,X1),sK3(sK7(X0,X1),X2)) | r2_hidden(sK2(sK7(X0,X1),X2),X2)) )),
% 1.97/0.62    inference(subsumption_resolution,[],[f64,f43])).
% 1.97/0.62  fof(f64,plain,(
% 1.97/0.62    ( ! [X2,X0,X1] : (sK0 != X0 | k1_tarski(sK1) != X2 | ~v1_relat_1(sK7(X0,X1)) | sK2(sK7(X0,X1),X2) = k1_funct_1(sK7(X0,X1),sK3(sK7(X0,X1),X2)) | r2_hidden(sK2(sK7(X0,X1),X2),X2)) )),
% 1.97/0.62    inference(subsumption_resolution,[],[f63,f44])).
% 1.97/0.62  fof(f63,plain,(
% 1.97/0.62    ( ! [X2,X0,X1] : (sK0 != X0 | k1_tarski(sK1) != X2 | ~v1_funct_1(sK7(X0,X1)) | ~v1_relat_1(sK7(X0,X1)) | sK2(sK7(X0,X1),X2) = k1_funct_1(sK7(X0,X1),sK3(sK7(X0,X1),X2)) | r2_hidden(sK2(sK7(X0,X1),X2),X2)) )),
% 1.97/0.62    inference(superposition,[],[f58,f45])).
% 1.97/0.62  fof(f58,plain,(
% 1.97/0.62    ( ! [X2,X3] : (k1_relat_1(X2) != sK0 | k1_tarski(sK1) != X3 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | sK2(X2,X3) = k1_funct_1(X2,sK3(X2,X3)) | r2_hidden(sK2(X2,X3),X3)) )),
% 1.97/0.62    inference(duplicate_literal_removal,[],[f55])).
% 1.97/0.62  fof(f55,plain,(
% 1.97/0.62    ( ! [X2,X3] : (k1_tarski(sK1) != X3 | k1_relat_1(X2) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | sK2(X2,X3) = k1_funct_1(X2,sK3(X2,X3)) | r2_hidden(sK2(X2,X3),X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.97/0.62    inference(superposition,[],[f30,f35])).
% 1.97/0.62  fof(f35,plain,(
% 1.97/0.62    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) | r2_hidden(sK2(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.97/0.62    inference(cnf_transformation,[],[f20])).
% 1.97/0.62  fof(f77,plain,(
% 1.97/0.62    ( ! [X6,X8,X7,X9] : (sK2(sK7(X6,X7),X9) != X7 | sK0 != X6 | ~r2_hidden(X8,X6) | k1_tarski(sK1) != X9 | ~r2_hidden(sK2(sK7(X6,X7),X9),X9)) )),
% 1.97/0.62    inference(duplicate_literal_removal,[],[f76])).
% 1.97/0.62  fof(f76,plain,(
% 1.97/0.62    ( ! [X6,X8,X7,X9] : (~r2_hidden(X8,X6) | sK0 != X6 | sK2(sK7(X6,X7),X9) != X7 | k1_tarski(sK1) != X9 | ~r2_hidden(sK2(sK7(X6,X7),X9),X9) | ~r2_hidden(X8,X6)) )),
% 1.97/0.62    inference(forward_demodulation,[],[f75,f45])).
% 1.97/0.62  fof(f75,plain,(
% 1.97/0.62    ( ! [X6,X8,X7,X9] : (sK0 != X6 | sK2(sK7(X6,X7),X9) != X7 | k1_tarski(sK1) != X9 | ~r2_hidden(X8,k1_relat_1(sK7(X6,X7))) | ~r2_hidden(sK2(sK7(X6,X7),X9),X9) | ~r2_hidden(X8,X6)) )),
% 1.97/0.62    inference(forward_demodulation,[],[f74,f45])).
% 1.97/0.62  fof(f74,plain,(
% 1.97/0.62    ( ! [X6,X8,X7,X9] : (sK2(sK7(X6,X7),X9) != X7 | sK0 != k1_relat_1(sK7(X6,X7)) | k1_tarski(sK1) != X9 | ~r2_hidden(X8,k1_relat_1(sK7(X6,X7))) | ~r2_hidden(sK2(sK7(X6,X7),X9),X9) | ~r2_hidden(X8,X6)) )),
% 1.97/0.62    inference(subsumption_resolution,[],[f73,f43])).
% 1.97/0.62  fof(f73,plain,(
% 1.97/0.62    ( ! [X6,X8,X7,X9] : (sK2(sK7(X6,X7),X9) != X7 | sK0 != k1_relat_1(sK7(X6,X7)) | ~v1_relat_1(sK7(X6,X7)) | k1_tarski(sK1) != X9 | ~r2_hidden(X8,k1_relat_1(sK7(X6,X7))) | ~r2_hidden(sK2(sK7(X6,X7),X9),X9) | ~r2_hidden(X8,X6)) )),
% 1.97/0.62    inference(subsumption_resolution,[],[f68,f44])).
% 1.97/0.62  fof(f68,plain,(
% 1.97/0.62    ( ! [X6,X8,X7,X9] : (sK2(sK7(X6,X7),X9) != X7 | sK0 != k1_relat_1(sK7(X6,X7)) | ~v1_funct_1(sK7(X6,X7)) | ~v1_relat_1(sK7(X6,X7)) | k1_tarski(sK1) != X9 | ~r2_hidden(X8,k1_relat_1(sK7(X6,X7))) | ~r2_hidden(sK2(sK7(X6,X7),X9),X9) | ~r2_hidden(X8,X6)) )),
% 1.97/0.62    inference(superposition,[],[f57,f46])).
% 1.97/0.62  fof(f57,plain,(
% 1.97/0.62    ( ! [X6,X4,X5] : (k1_funct_1(X4,X6) != sK2(X4,X5) | sK0 != k1_relat_1(X4) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | k1_tarski(sK1) != X5 | ~r2_hidden(X6,k1_relat_1(X4)) | ~r2_hidden(sK2(X4,X5),X5)) )),
% 1.97/0.62    inference(duplicate_literal_removal,[],[f56])).
% 1.97/0.62  fof(f56,plain,(
% 1.97/0.62    ( ! [X6,X4,X5] : (k1_tarski(sK1) != X5 | sK0 != k1_relat_1(X4) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | k1_funct_1(X4,X6) != sK2(X4,X5) | ~r2_hidden(X6,k1_relat_1(X4)) | ~r2_hidden(sK2(X4,X5),X5) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) )),
% 1.97/0.62    inference(superposition,[],[f30,f36])).
% 1.97/0.62  fof(f36,plain,(
% 1.97/0.62    ( ! [X0,X3,X1] : (k2_relat_1(X0) = X1 | k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(sK2(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.97/0.62    inference(cnf_transformation,[],[f20])).
% 1.97/0.62  fof(f786,plain,(
% 1.97/0.62    ( ! [X3] : (r2_hidden(X3,sK0)) )),
% 1.97/0.62    inference(backward_demodulation,[],[f52,f702])).
% 1.97/0.62  fof(f702,plain,(
% 1.97/0.62    ( ! [X14] : (sK0 = k1_tarski(X14)) )),
% 1.97/0.62    inference(subsumption_resolution,[],[f699,f29])).
% 1.97/0.62  fof(f29,plain,(
% 1.97/0.62    k1_xboole_0 != sK0),
% 1.97/0.62    inference(cnf_transformation,[],[f14])).
% 1.97/0.62  fof(f699,plain,(
% 1.97/0.62    ( ! [X14] : (k1_xboole_0 = sK0 | sK0 = k1_tarski(X14)) )),
% 1.97/0.62    inference(resolution,[],[f650,f41])).
% 1.97/0.62  fof(f41,plain,(
% 1.97/0.62    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.97/0.62    inference(cnf_transformation,[],[f26])).
% 1.97/0.62  fof(f26,plain,(
% 1.97/0.62    ! [X0,X1] : ((sK6(X0,X1) != X1 & r2_hidden(sK6(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 1.97/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f10,f25])).
% 1.97/0.62  fof(f25,plain,(
% 1.97/0.62    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK6(X0,X1) != X1 & r2_hidden(sK6(X0,X1),X0)))),
% 1.97/0.62    introduced(choice_axiom,[])).
% 1.97/0.62  fof(f10,plain,(
% 1.97/0.62    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 1.97/0.62    inference(ennf_transformation,[],[f2])).
% 1.97/0.62  fof(f2,axiom,(
% 1.97/0.62    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.97/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 1.97/0.62  % SZS output end Proof for theBenchmark
% 1.97/0.62  % (10646)------------------------------
% 1.97/0.62  % (10646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.62  % (10646)Termination reason: Refutation
% 1.97/0.62  
% 1.97/0.62  % (10646)Memory used [KB]: 2046
% 1.97/0.62  % (10646)Time elapsed: 0.199 s
% 1.97/0.62  % (10646)------------------------------
% 1.97/0.62  % (10646)------------------------------
% 1.97/0.63  % (10627)Success in time 0.259 s
%------------------------------------------------------------------------------
