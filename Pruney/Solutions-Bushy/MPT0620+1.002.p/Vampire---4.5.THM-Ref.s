%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0620+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:19 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 178 expanded)
%              Number of leaves         :   15 (  56 expanded)
%              Depth                    :   25
%              Number of atoms          :  395 (1014 expanded)
%              Number of equality atoms :  171 ( 443 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1492,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1491,f36])).

fof(f36,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ! [X2] :
        ( k2_relat_1(X2) != k1_tarski(sK1)
        | k1_relat_1(X2) != sK0
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
          ! [X2] :
            ( k2_relat_1(X2) != k1_tarski(X1)
            | k1_relat_1(X2) != X0
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & k1_xboole_0 != X0 )
   => ( ? [X1] :
        ! [X2] :
          ( k2_relat_1(X2) != k1_tarski(X1)
          | k1_relat_1(X2) != sK0
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
      ! [X2] :
        ( k2_relat_1(X2) != k1_tarski(X1)
        | k1_relat_1(X2) != sK0
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
   => ! [X2] :
        ( k2_relat_1(X2) != k1_tarski(sK1)
        | k1_relat_1(X2) != sK0
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
        ! [X2] :
          ( k2_relat_1(X2) != k1_tarski(X1)
          | k1_relat_1(X2) != X0
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( k1_xboole_0 != X0
       => ! [X1] :
          ? [X2] :
            ( k2_relat_1(X2) = k1_tarski(X1)
            & k1_relat_1(X2) = X0
            & v1_funct_1(X2)
            & v1_relat_1(X2) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

fof(f1491,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f1311,f39])).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f1311,plain,(
    v1_xboole_0(sK0) ),
    inference(resolution,[],[f1073,f46])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f4,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f1073,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f964,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f964,plain,(
    ! [X10] : ~ r2_hidden(X10,sK0) ),
    inference(subsumption_resolution,[],[f960,f62])).

fof(f62,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f960,plain,(
    ! [X10] :
      ( ~ r2_hidden(X10,sK0)
      | ~ r2_hidden(sK1,k1_tarski(sK1)) ) ),
    inference(trivial_inequality_removal,[],[f941])).

fof(f941,plain,(
    ! [X10] :
      ( sK1 != sK1
      | sK0 != sK0
      | ~ r2_hidden(X10,sK0)
      | k1_tarski(sK1) != k1_tarski(sK1)
      | ~ r2_hidden(sK1,k1_tarski(sK1)) ) ),
    inference(superposition,[],[f87,f887])).

fof(f887,plain,(
    sK1 = sK2(sK7(sK0,sK1),k1_tarski(sK1)) ),
    inference(equality_resolution,[],[f478])).

fof(f478,plain,(
    ! [X0] :
      ( sK1 != X0
      | sK1 = sK2(sK7(sK0,X0),k1_tarski(sK1)) ) ),
    inference(equality_factoring,[],[f168])).

fof(f168,plain,(
    ! [X2] :
      ( sK2(sK7(sK0,X2),k1_tarski(sK1)) = X2
      | sK1 = sK2(sK7(sK0,X2),k1_tarski(sK1)) ) ),
    inference(resolution,[],[f131,f63])).

fof(f63,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f131,plain,(
    ! [X1] :
      ( r2_hidden(sK2(sK7(sK0,X1),k1_tarski(sK1)),k1_tarski(sK1))
      | sK2(sK7(sK0,X1),k1_tarski(sK1)) = X1 ) ),
    inference(subsumption_resolution,[],[f126,f95])).

fof(f95,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK7(sK0,X0),k1_tarski(sK1)),k1_tarski(sK1))
      | r2_hidden(sK3(sK7(sK0,X0),k1_tarski(sK1)),sK0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | r2_hidden(sK3(sK7(X0,X1),k1_tarski(sK1)),X0)
      | r2_hidden(sK2(sK7(X0,X1),k1_tarski(sK1)),k1_tarski(sK1)) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(sK1) != X2
      | sK0 != X0
      | r2_hidden(sK3(sK7(X0,X1),X2),X0)
      | r2_hidden(sK2(sK7(X0,X1),X2),X2) ) ),
    inference(subsumption_resolution,[],[f71,f53])).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(sK7(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK7(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK7(X0,X1)) = X0
      & v1_funct_1(sK7(X0,X1))
      & v1_relat_1(sK7(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f18,f34])).

fof(f34,plain,(
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

fof(f18,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X0
      | k1_tarski(sK1) != X2
      | ~ v1_relat_1(sK7(X0,X1))
      | r2_hidden(sK3(sK7(X0,X1),X2),X0)
      | r2_hidden(sK2(sK7(X0,X1),X2),X2) ) ),
    inference(subsumption_resolution,[],[f70,f54])).

fof(f54,plain,(
    ! [X0,X1] : v1_funct_1(sK7(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X0
      | k1_tarski(sK1) != X2
      | ~ v1_funct_1(sK7(X0,X1))
      | ~ v1_relat_1(sK7(X0,X1))
      | r2_hidden(sK3(sK7(X0,X1),X2),X0)
      | r2_hidden(sK2(sK7(X0,X1),X2),X2) ) ),
    inference(superposition,[],[f69,f55])).

fof(f55,plain,(
    ! [X0,X1] : k1_relat_1(sK7(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f35])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != sK0
      | k1_tarski(sK1) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_tarski(sK1) != X1
      | k1_relat_1(X0) != sK0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK2(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f37,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK2(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f26,f25,f24])).

fof(f24,plain,(
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

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK2(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f37,plain,(
    ! [X2] :
      ( k2_relat_1(X2) != k1_tarski(sK1)
      | k1_relat_1(X2) != sK0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f126,plain,(
    ! [X1] :
      ( sK2(sK7(sK0,X1),k1_tarski(sK1)) = X1
      | r2_hidden(sK2(sK7(sK0,X1),k1_tarski(sK1)),k1_tarski(sK1))
      | ~ r2_hidden(sK3(sK7(sK0,X1),k1_tarski(sK1)),sK0) ) ),
    inference(superposition,[],[f100,f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK7(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f100,plain,(
    ! [X0] :
      ( sK2(sK7(sK0,X0),k1_tarski(sK1)) = k1_funct_1(sK7(sK0,X0),sK3(sK7(sK0,X0),k1_tarski(sK1)))
      | r2_hidden(sK2(sK7(sK0,X0),k1_tarski(sK1)),k1_tarski(sK1)) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK2(sK7(X0,X1),k1_tarski(sK1)) = k1_funct_1(sK7(X0,X1),sK3(sK7(X0,X1),k1_tarski(sK1)))
      | r2_hidden(sK2(sK7(X0,X1),k1_tarski(sK1)),k1_tarski(sK1)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(sK1) != X2
      | sK0 != X0
      | sK2(sK7(X0,X1),X2) = k1_funct_1(sK7(X0,X1),sK3(sK7(X0,X1),X2))
      | r2_hidden(sK2(sK7(X0,X1),X2),X2) ) ),
    inference(subsumption_resolution,[],[f74,f53])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X0
      | k1_tarski(sK1) != X2
      | ~ v1_relat_1(sK7(X0,X1))
      | sK2(sK7(X0,X1),X2) = k1_funct_1(sK7(X0,X1),sK3(sK7(X0,X1),X2))
      | r2_hidden(sK2(sK7(X0,X1),X2),X2) ) ),
    inference(subsumption_resolution,[],[f73,f54])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X0
      | k1_tarski(sK1) != X2
      | ~ v1_funct_1(sK7(X0,X1))
      | ~ v1_relat_1(sK7(X0,X1))
      | sK2(sK7(X0,X1),X2) = k1_funct_1(sK7(X0,X1),sK3(sK7(X0,X1),X2))
      | r2_hidden(sK2(sK7(X0,X1),X2),X2) ) ),
    inference(superposition,[],[f68,f55])).

fof(f68,plain,(
    ! [X2,X3] :
      ( k1_relat_1(X2) != sK0
      | k1_tarski(sK1) != X3
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | sK2(X2,X3) = k1_funct_1(X2,sK3(X2,X3))
      | r2_hidden(sK2(X2,X3),X3) ) ),
    inference(duplicate_literal_removal,[],[f65])).

fof(f65,plain,(
    ! [X2,X3] :
      ( k1_tarski(sK1) != X3
      | k1_relat_1(X2) != sK0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | sK2(X2,X3) = k1_funct_1(X2,sK3(X2,X3))
      | r2_hidden(sK2(X2,X3),X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f37,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
      | r2_hidden(sK2(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f87,plain,(
    ! [X6,X8,X7,X9] :
      ( sK2(sK7(X6,X7),X9) != X7
      | sK0 != X6
      | ~ r2_hidden(X8,X6)
      | k1_tarski(sK1) != X9
      | ~ r2_hidden(sK2(sK7(X6,X7),X9),X9) ) ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ r2_hidden(X8,X6)
      | sK0 != X6
      | sK2(sK7(X6,X7),X9) != X7
      | k1_tarski(sK1) != X9
      | ~ r2_hidden(sK2(sK7(X6,X7),X9),X9)
      | ~ r2_hidden(X8,X6) ) ),
    inference(forward_demodulation,[],[f85,f55])).

fof(f85,plain,(
    ! [X6,X8,X7,X9] :
      ( sK0 != X6
      | sK2(sK7(X6,X7),X9) != X7
      | k1_tarski(sK1) != X9
      | ~ r2_hidden(X8,k1_relat_1(sK7(X6,X7)))
      | ~ r2_hidden(sK2(sK7(X6,X7),X9),X9)
      | ~ r2_hidden(X8,X6) ) ),
    inference(forward_demodulation,[],[f84,f55])).

fof(f84,plain,(
    ! [X6,X8,X7,X9] :
      ( sK2(sK7(X6,X7),X9) != X7
      | sK0 != k1_relat_1(sK7(X6,X7))
      | k1_tarski(sK1) != X9
      | ~ r2_hidden(X8,k1_relat_1(sK7(X6,X7)))
      | ~ r2_hidden(sK2(sK7(X6,X7),X9),X9)
      | ~ r2_hidden(X8,X6) ) ),
    inference(subsumption_resolution,[],[f83,f53])).

fof(f83,plain,(
    ! [X6,X8,X7,X9] :
      ( sK2(sK7(X6,X7),X9) != X7
      | sK0 != k1_relat_1(sK7(X6,X7))
      | ~ v1_relat_1(sK7(X6,X7))
      | k1_tarski(sK1) != X9
      | ~ r2_hidden(X8,k1_relat_1(sK7(X6,X7)))
      | ~ r2_hidden(sK2(sK7(X6,X7),X9),X9)
      | ~ r2_hidden(X8,X6) ) ),
    inference(subsumption_resolution,[],[f78,f54])).

fof(f78,plain,(
    ! [X6,X8,X7,X9] :
      ( sK2(sK7(X6,X7),X9) != X7
      | sK0 != k1_relat_1(sK7(X6,X7))
      | ~ v1_funct_1(sK7(X6,X7))
      | ~ v1_relat_1(sK7(X6,X7))
      | k1_tarski(sK1) != X9
      | ~ r2_hidden(X8,k1_relat_1(sK7(X6,X7)))
      | ~ r2_hidden(sK2(sK7(X6,X7),X9),X9)
      | ~ r2_hidden(X8,X6) ) ),
    inference(superposition,[],[f67,f56])).

fof(f67,plain,(
    ! [X6,X4,X5] :
      ( k1_funct_1(X4,X6) != sK2(X4,X5)
      | sK0 != k1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | k1_tarski(sK1) != X5
      | ~ r2_hidden(X6,k1_relat_1(X4))
      | ~ r2_hidden(sK2(X4,X5),X5) ) ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,(
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
    inference(superposition,[],[f37,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | k1_funct_1(X0,X3) != sK2(X0,X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(sK2(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

%------------------------------------------------------------------------------
