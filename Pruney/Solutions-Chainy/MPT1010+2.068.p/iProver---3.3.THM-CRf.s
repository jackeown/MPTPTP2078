%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:15 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 281 expanded)
%              Number of clauses        :   57 (  75 expanded)
%              Number of leaves         :   20 (  62 expanded)
%              Depth                    :   20
%              Number of atoms          :  457 (1015 expanded)
%              Number of equality atoms :  228 ( 445 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f30])).

fof(f44,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( k1_funct_1(sK7,sK6) != sK5
      & r2_hidden(sK6,sK4)
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5))))
      & v1_funct_2(sK7,sK4,k1_tarski(sK5))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( k1_funct_1(sK7,sK6) != sK5
    & r2_hidden(sK6,sK4)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5))))
    & v1_funct_2(sK7,sK4,k1_tarski(sK5))
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f31,f44])).

fof(f78,plain,(
    r2_hidden(sK6,sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f41,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
              ( k1_funct_1(X0,X3) != sK1(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK1(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK1(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
                  & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X5)) = X5
                    & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f38,f41,f40,f39])).

fof(f60,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f95,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f96,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f95])).

fof(f77,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f80,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f88,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5)))) ),
    inference(definition_unfolding,[],[f77,f80])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f87,plain,(
    ! [X0] : ~ v1_xboole_0(k1_enumset1(X0,X0,X0)) ),
    inference(definition_unfolding,[],[f55,f80])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f32])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK0(X0,X1,X2) != X1
            & sK0(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( sK0(X0,X1,X2) = X1
          | sK0(X0,X1,X2) = X0
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK0(X0,X1,X2) != X1
              & sK0(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( sK0(X0,X1,X2) = X1
            | sK0(X0,X1,X2) = X0
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f86,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f47,f54])).

fof(f94,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k1_enumset1(X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f86])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f76,plain,(
    v1_funct_2(sK7,sK4,k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f45])).

fof(f89,plain,(
    v1_funct_2(sK7,sK4,k1_enumset1(sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f76,f80])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f48,f54])).

fof(f92,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f85])).

fof(f93,plain,(
    ! [X4,X1] : r2_hidden(X4,k1_enumset1(X4,X4,X1)) ),
    inference(equality_resolution,[],[f92])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f75,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,(
    k1_funct_1(sK7,sK6) != sK5 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_28,negated_conjecture,
    ( r2_hidden(sK6,sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_802,plain,
    ( r2_hidden(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_816,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5)))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_801,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_809,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1498,plain,
    ( k2_relset_1(sK4,k1_enumset1(sK5,sK5,sK5),sK7) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_801,c_809])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_811,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2075,plain,
    ( m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(k1_enumset1(sK5,sK5,sK5))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1498,c_811])).

cnf(c_34,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2845,plain,
    ( m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(k1_enumset1(sK5,sK5,sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2075,c_34])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_820,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2851,plain,
    ( m1_subset_1(X0,k1_enumset1(sK5,sK5,sK5)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2845,c_820])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_821,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3065,plain,
    ( r2_hidden(X0,k1_enumset1(sK5,sK5,sK5)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | v1_xboole_0(k1_enumset1(sK5,sK5,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2851,c_821])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(k1_enumset1(X0,X0,X0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_822,plain,
    ( v1_xboole_0(k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8710,plain,
    ( r2_hidden(X0,k1_enumset1(sK5,sK5,sK5)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3065,c_822])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_823,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k1_enumset1(X1,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8715,plain,
    ( sK5 = X0
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8710,c_823])).

cnf(c_9138,plain,
    ( k1_funct_1(sK7,X0) = sK5
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_816,c_8715])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_803,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4264,plain,
    ( k1_relset_1(sK4,k1_enumset1(sK5,sK5,sK5),sK7) = sK4
    | k1_enumset1(sK5,sK5,sK5) = k1_xboole_0
    | v1_funct_2(sK7,sK4,k1_enumset1(sK5,sK5,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_801,c_803])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_810,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1953,plain,
    ( k1_relset_1(sK4,k1_enumset1(sK5,sK5,sK5),sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_801,c_810])).

cnf(c_4268,plain,
    ( k1_enumset1(sK5,sK5,sK5) = k1_xboole_0
    | k1_relat_1(sK7) = sK4
    | v1_funct_2(sK7,sK4,k1_enumset1(sK5,sK5,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4264,c_1953])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK7,sK4,k1_enumset1(sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_4281,plain,
    ( ~ v1_funct_2(sK7,sK4,k1_enumset1(sK5,sK5,sK5))
    | k1_enumset1(sK5,sK5,sK5) = k1_xboole_0
    | k1_relat_1(sK7) = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4268])).

cnf(c_4283,plain,
    ( k1_relat_1(sK7) = sK4
    | k1_enumset1(sK5,sK5,sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4268,c_30,c_4281])).

cnf(c_4284,plain,
    ( k1_enumset1(sK5,sK5,sK5) = k1_xboole_0
    | k1_relat_1(sK7) = sK4 ),
    inference(renaming,[status(thm)],[c_4283])).

cnf(c_5,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_824,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_813,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1417,plain,
    ( r1_tarski(k1_enumset1(X0,X0,X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_824,c_813])).

cnf(c_4287,plain,
    ( k1_relat_1(sK7) = sK4
    | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4284,c_1417])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_829,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7099,plain,
    ( k1_relat_1(sK7) = sK4 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4287,c_829])).

cnf(c_9144,plain,
    ( k1_funct_1(sK7,X0) = sK5
    | r2_hidden(X0,sK4) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9138,c_7099])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_32,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1106,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5))))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1107,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5)))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1106])).

cnf(c_9723,plain,
    ( k1_funct_1(sK7,X0) = sK5
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9144,c_32,c_34,c_1107])).

cnf(c_9734,plain,
    ( k1_funct_1(sK7,sK6) = sK5 ),
    inference(superposition,[status(thm)],[c_802,c_9723])).

cnf(c_27,negated_conjecture,
    ( k1_funct_1(sK7,sK6) != sK5 ),
    inference(cnf_transformation,[],[f79])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9734,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:16:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.45/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.45/0.99  
% 3.45/0.99  ------  iProver source info
% 3.45/0.99  
% 3.45/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.45/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.45/0.99  git: non_committed_changes: false
% 3.45/0.99  git: last_make_outside_of_git: false
% 3.45/0.99  
% 3.45/0.99  ------ 
% 3.45/0.99  ------ Parsing...
% 3.45/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.45/0.99  ------ Proving...
% 3.45/0.99  ------ Problem Properties 
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  clauses                                 32
% 3.45/0.99  conjectures                             5
% 3.45/0.99  EPR                                     5
% 3.45/0.99  Horn                                    23
% 3.45/0.99  unary                                   9
% 3.45/0.99  binary                                  5
% 3.45/0.99  lits                                    87
% 3.45/0.99  lits eq                                 27
% 3.45/0.99  fd_pure                                 0
% 3.45/0.99  fd_pseudo                               0
% 3.45/0.99  fd_cond                                 3
% 3.45/0.99  fd_pseudo_cond                          6
% 3.45/0.99  AC symbols                              0
% 3.45/0.99  
% 3.45/0.99  ------ Input Options Time Limit: Unbounded
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  ------ 
% 3.45/0.99  Current options:
% 3.45/0.99  ------ 
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  ------ Proving...
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  % SZS status Theorem for theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  fof(f15,conjecture,(
% 3.45/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f16,negated_conjecture,(
% 3.45/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 3.45/0.99    inference(negated_conjecture,[],[f15])).
% 3.45/0.99  
% 3.45/0.99  fof(f30,plain,(
% 3.45/0.99    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 3.45/0.99    inference(ennf_transformation,[],[f16])).
% 3.45/0.99  
% 3.45/0.99  fof(f31,plain,(
% 3.45/0.99    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 3.45/0.99    inference(flattening,[],[f30])).
% 3.45/0.99  
% 3.45/0.99  fof(f44,plain,(
% 3.45/0.99    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK7,sK6) != sK5 & r2_hidden(sK6,sK4) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5)))) & v1_funct_2(sK7,sK4,k1_tarski(sK5)) & v1_funct_1(sK7))),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f45,plain,(
% 3.45/0.99    k1_funct_1(sK7,sK6) != sK5 & r2_hidden(sK6,sK4) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5)))) & v1_funct_2(sK7,sK4,k1_tarski(sK5)) & v1_funct_1(sK7)),
% 3.45/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f31,f44])).
% 3.45/0.99  
% 3.45/0.99  fof(f78,plain,(
% 3.45/0.99    r2_hidden(sK6,sK4)),
% 3.45/0.99    inference(cnf_transformation,[],[f45])).
% 3.45/0.99  
% 3.45/0.99  fof(f8,axiom,(
% 3.45/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f21,plain,(
% 3.45/0.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.45/0.99    inference(ennf_transformation,[],[f8])).
% 3.45/0.99  
% 3.45/0.99  fof(f22,plain,(
% 3.45/0.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.45/0.99    inference(flattening,[],[f21])).
% 3.45/0.99  
% 3.45/0.99  fof(f37,plain,(
% 3.45/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.45/0.99    inference(nnf_transformation,[],[f22])).
% 3.45/0.99  
% 3.45/0.99  fof(f38,plain,(
% 3.45/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.45/0.99    inference(rectify,[],[f37])).
% 3.45/0.99  
% 3.45/0.99  fof(f41,plain,(
% 3.45/0.99    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f40,plain,(
% 3.45/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f39,plain,(
% 3.45/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f42,plain,(
% 3.45/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.45/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f38,f41,f40,f39])).
% 3.45/0.99  
% 3.45/0.99  fof(f60,plain,(
% 3.45/0.99    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f42])).
% 3.45/0.99  
% 3.45/0.99  fof(f95,plain,(
% 3.45/0.99    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.45/0.99    inference(equality_resolution,[],[f60])).
% 3.45/0.99  
% 3.45/0.99  fof(f96,plain,(
% 3.45/0.99    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.45/0.99    inference(equality_resolution,[],[f95])).
% 3.45/0.99  
% 3.45/0.99  fof(f77,plain,(
% 3.45/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5))))),
% 3.45/0.99    inference(cnf_transformation,[],[f45])).
% 3.45/0.99  
% 3.45/0.99  fof(f3,axiom,(
% 3.45/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f53,plain,(
% 3.45/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f3])).
% 3.45/0.99  
% 3.45/0.99  fof(f4,axiom,(
% 3.45/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f54,plain,(
% 3.45/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f4])).
% 3.45/0.99  
% 3.45/0.99  fof(f80,plain,(
% 3.45/0.99    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 3.45/0.99    inference(definition_unfolding,[],[f53,f54])).
% 3.45/0.99  
% 3.45/0.99  fof(f88,plain,(
% 3.45/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5))))),
% 3.45/0.99    inference(definition_unfolding,[],[f77,f80])).
% 3.45/0.99  
% 3.45/0.99  fof(f13,axiom,(
% 3.45/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f27,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/0.99    inference(ennf_transformation,[],[f13])).
% 3.45/0.99  
% 3.45/0.99  fof(f68,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f27])).
% 3.45/0.99  
% 3.45/0.99  fof(f11,axiom,(
% 3.45/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f25,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/0.99    inference(ennf_transformation,[],[f11])).
% 3.45/0.99  
% 3.45/0.99  fof(f66,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f25])).
% 3.45/0.99  
% 3.45/0.99  fof(f7,axiom,(
% 3.45/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f19,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.45/0.99    inference(ennf_transformation,[],[f7])).
% 3.45/0.99  
% 3.45/0.99  fof(f20,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.45/0.99    inference(flattening,[],[f19])).
% 3.45/0.99  
% 3.45/0.99  fof(f57,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f20])).
% 3.45/0.99  
% 3.45/0.99  fof(f6,axiom,(
% 3.45/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f17,plain,(
% 3.45/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.45/0.99    inference(ennf_transformation,[],[f6])).
% 3.45/0.99  
% 3.45/0.99  fof(f18,plain,(
% 3.45/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.45/0.99    inference(flattening,[],[f17])).
% 3.45/0.99  
% 3.45/0.99  fof(f56,plain,(
% 3.45/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f18])).
% 3.45/0.99  
% 3.45/0.99  fof(f5,axiom,(
% 3.45/0.99    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f55,plain,(
% 3.45/0.99    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f5])).
% 3.45/0.99  
% 3.45/0.99  fof(f87,plain,(
% 3.45/0.99    ( ! [X0] : (~v1_xboole_0(k1_enumset1(X0,X0,X0))) )),
% 3.45/0.99    inference(definition_unfolding,[],[f55,f80])).
% 3.45/0.99  
% 3.45/0.99  fof(f2,axiom,(
% 3.45/0.99    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f32,plain,(
% 3.45/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.45/0.99    inference(nnf_transformation,[],[f2])).
% 3.45/0.99  
% 3.45/0.99  fof(f33,plain,(
% 3.45/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.45/0.99    inference(flattening,[],[f32])).
% 3.45/0.99  
% 3.45/0.99  fof(f34,plain,(
% 3.45/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.45/0.99    inference(rectify,[],[f33])).
% 3.45/0.99  
% 3.45/0.99  fof(f35,plain,(
% 3.45/0.99    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f36,plain,(
% 3.45/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.45/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 3.45/0.99  
% 3.45/0.99  fof(f47,plain,(
% 3.45/0.99    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 3.45/0.99    inference(cnf_transformation,[],[f36])).
% 3.45/0.99  
% 3.45/0.99  fof(f86,plain,(
% 3.45/0.99    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 3.45/0.99    inference(definition_unfolding,[],[f47,f54])).
% 3.45/0.99  
% 3.45/0.99  fof(f94,plain,(
% 3.45/0.99    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k1_enumset1(X0,X0,X1))) )),
% 3.45/0.99    inference(equality_resolution,[],[f86])).
% 3.45/0.99  
% 3.45/0.99  fof(f14,axiom,(
% 3.45/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f28,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/0.99    inference(ennf_transformation,[],[f14])).
% 3.45/0.99  
% 3.45/0.99  fof(f29,plain,(
% 3.45/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/0.99    inference(flattening,[],[f28])).
% 3.45/0.99  
% 3.45/0.99  fof(f43,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/0.99    inference(nnf_transformation,[],[f29])).
% 3.45/0.99  
% 3.45/0.99  fof(f69,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f43])).
% 3.45/0.99  
% 3.45/0.99  fof(f12,axiom,(
% 3.45/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f26,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/0.99    inference(ennf_transformation,[],[f12])).
% 3.45/0.99  
% 3.45/0.99  fof(f67,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f26])).
% 3.45/0.99  
% 3.45/0.99  fof(f76,plain,(
% 3.45/0.99    v1_funct_2(sK7,sK4,k1_tarski(sK5))),
% 3.45/0.99    inference(cnf_transformation,[],[f45])).
% 3.45/0.99  
% 3.45/0.99  fof(f89,plain,(
% 3.45/0.99    v1_funct_2(sK7,sK4,k1_enumset1(sK5,sK5,sK5))),
% 3.45/0.99    inference(definition_unfolding,[],[f76,f80])).
% 3.45/0.99  
% 3.45/0.99  fof(f48,plain,(
% 3.45/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.45/0.99    inference(cnf_transformation,[],[f36])).
% 3.45/0.99  
% 3.45/0.99  fof(f85,plain,(
% 3.45/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 3.45/0.99    inference(definition_unfolding,[],[f48,f54])).
% 3.45/0.99  
% 3.45/0.99  fof(f92,plain,(
% 3.45/0.99    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k1_enumset1(X4,X4,X1) != X2) )),
% 3.45/0.99    inference(equality_resolution,[],[f85])).
% 3.45/0.99  
% 3.45/0.99  fof(f93,plain,(
% 3.45/0.99    ( ! [X4,X1] : (r2_hidden(X4,k1_enumset1(X4,X4,X1))) )),
% 3.45/0.99    inference(equality_resolution,[],[f92])).
% 3.45/0.99  
% 3.45/0.99  fof(f9,axiom,(
% 3.45/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f23,plain,(
% 3.45/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.45/0.99    inference(ennf_transformation,[],[f9])).
% 3.45/0.99  
% 3.45/0.99  fof(f64,plain,(
% 3.45/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f23])).
% 3.45/0.99  
% 3.45/0.99  fof(f1,axiom,(
% 3.45/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f46,plain,(
% 3.45/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f1])).
% 3.45/0.99  
% 3.45/0.99  fof(f75,plain,(
% 3.45/0.99    v1_funct_1(sK7)),
% 3.45/0.99    inference(cnf_transformation,[],[f45])).
% 3.45/0.99  
% 3.45/0.99  fof(f10,axiom,(
% 3.45/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f24,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/0.99    inference(ennf_transformation,[],[f10])).
% 3.45/0.99  
% 3.45/0.99  fof(f65,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f24])).
% 3.45/0.99  
% 3.45/0.99  fof(f79,plain,(
% 3.45/0.99    k1_funct_1(sK7,sK6) != sK5),
% 3.45/0.99    inference(cnf_transformation,[],[f45])).
% 3.45/0.99  
% 3.45/0.99  cnf(c_28,negated_conjecture,
% 3.45/0.99      ( r2_hidden(sK6,sK4) ),
% 3.45/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_802,plain,
% 3.45/0.99      ( r2_hidden(sK6,sK4) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_13,plain,
% 3.45/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.45/0.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.45/0.99      | ~ v1_relat_1(X1)
% 3.45/0.99      | ~ v1_funct_1(X1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_816,plain,
% 3.45/0.99      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 3.45/0.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 3.45/0.99      | v1_relat_1(X1) != iProver_top
% 3.45/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_29,negated_conjecture,
% 3.45/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5)))) ),
% 3.45/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_801,plain,
% 3.45/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5)))) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_20,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.45/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_809,plain,
% 3.45/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.45/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1498,plain,
% 3.45/0.99      ( k2_relset_1(sK4,k1_enumset1(sK5,sK5,sK5),sK7) = k2_relat_1(sK7) ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_801,c_809]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_18,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/0.99      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 3.45/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_811,plain,
% 3.45/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.45/0.99      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2075,plain,
% 3.45/0.99      ( m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(k1_enumset1(sK5,sK5,sK5))) = iProver_top
% 3.45/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5)))) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_1498,c_811]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_34,plain,
% 3.45/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5)))) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2845,plain,
% 3.45/0.99      ( m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(k1_enumset1(sK5,sK5,sK5))) = iProver_top ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_2075,c_34]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_9,plain,
% 3.45/0.99      ( m1_subset_1(X0,X1)
% 3.45/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.45/0.99      | ~ r2_hidden(X0,X2) ),
% 3.45/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_820,plain,
% 3.45/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 3.45/0.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.45/0.99      | r2_hidden(X0,X2) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2851,plain,
% 3.45/0.99      ( m1_subset_1(X0,k1_enumset1(sK5,sK5,sK5)) = iProver_top
% 3.45/0.99      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_2845,c_820]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_8,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_821,plain,
% 3.45/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.45/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.45/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3065,plain,
% 3.45/0.99      ( r2_hidden(X0,k1_enumset1(sK5,sK5,sK5)) = iProver_top
% 3.45/0.99      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 3.45/0.99      | v1_xboole_0(k1_enumset1(sK5,sK5,sK5)) = iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_2851,c_821]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_7,plain,
% 3.45/0.99      ( ~ v1_xboole_0(k1_enumset1(X0,X0,X0)) ),
% 3.45/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_822,plain,
% 3.45/0.99      ( v1_xboole_0(k1_enumset1(X0,X0,X0)) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_8710,plain,
% 3.45/0.99      ( r2_hidden(X0,k1_enumset1(sK5,sK5,sK5)) = iProver_top
% 3.45/0.99      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 3.45/0.99      inference(forward_subsumption_resolution,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_3065,c_822]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_6,plain,
% 3.45/0.99      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 3.45/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_823,plain,
% 3.45/0.99      ( X0 = X1
% 3.45/0.99      | X0 = X2
% 3.45/0.99      | r2_hidden(X0,k1_enumset1(X1,X1,X2)) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_8715,plain,
% 3.45/0.99      ( sK5 = X0 | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_8710,c_823]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_9138,plain,
% 3.45/0.99      ( k1_funct_1(sK7,X0) = sK5
% 3.45/0.99      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.45/0.99      | v1_relat_1(sK7) != iProver_top
% 3.45/0.99      | v1_funct_1(sK7) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_816,c_8715]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_26,plain,
% 3.45/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.45/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.45/0.99      | k1_xboole_0 = X2 ),
% 3.45/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_803,plain,
% 3.45/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 3.45/0.99      | k1_xboole_0 = X1
% 3.45/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.45/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4264,plain,
% 3.45/0.99      ( k1_relset_1(sK4,k1_enumset1(sK5,sK5,sK5),sK7) = sK4
% 3.45/0.99      | k1_enumset1(sK5,sK5,sK5) = k1_xboole_0
% 3.45/0.99      | v1_funct_2(sK7,sK4,k1_enumset1(sK5,sK5,sK5)) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_801,c_803]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_19,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.45/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_810,plain,
% 3.45/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.45/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1953,plain,
% 3.45/0.99      ( k1_relset_1(sK4,k1_enumset1(sK5,sK5,sK5),sK7) = k1_relat_1(sK7) ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_801,c_810]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4268,plain,
% 3.45/0.99      ( k1_enumset1(sK5,sK5,sK5) = k1_xboole_0
% 3.45/0.99      | k1_relat_1(sK7) = sK4
% 3.45/0.99      | v1_funct_2(sK7,sK4,k1_enumset1(sK5,sK5,sK5)) != iProver_top ),
% 3.45/0.99      inference(demodulation,[status(thm)],[c_4264,c_1953]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_30,negated_conjecture,
% 3.45/0.99      ( v1_funct_2(sK7,sK4,k1_enumset1(sK5,sK5,sK5)) ),
% 3.45/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4281,plain,
% 3.45/0.99      ( ~ v1_funct_2(sK7,sK4,k1_enumset1(sK5,sK5,sK5))
% 3.45/0.99      | k1_enumset1(sK5,sK5,sK5) = k1_xboole_0
% 3.45/0.99      | k1_relat_1(sK7) = sK4 ),
% 3.45/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4268]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4283,plain,
% 3.45/0.99      ( k1_relat_1(sK7) = sK4 | k1_enumset1(sK5,sK5,sK5) = k1_xboole_0 ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_4268,c_30,c_4281]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4284,plain,
% 3.45/0.99      ( k1_enumset1(sK5,sK5,sK5) = k1_xboole_0 | k1_relat_1(sK7) = sK4 ),
% 3.45/0.99      inference(renaming,[status(thm)],[c_4283]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_5,plain,
% 3.45/0.99      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
% 3.45/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_824,plain,
% 3.45/0.99      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_16,plain,
% 3.45/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.45/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_813,plain,
% 3.45/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.45/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1417,plain,
% 3.45/0.99      ( r1_tarski(k1_enumset1(X0,X0,X1),X0) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_824,c_813]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4287,plain,
% 3.45/0.99      ( k1_relat_1(sK7) = sK4
% 3.45/0.99      | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_4284,c_1417]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_0,plain,
% 3.45/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.45/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_829,plain,
% 3.45/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_7099,plain,
% 3.45/0.99      ( k1_relat_1(sK7) = sK4 ),
% 3.45/0.99      inference(forward_subsumption_resolution,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_4287,c_829]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_9144,plain,
% 3.45/0.99      ( k1_funct_1(sK7,X0) = sK5
% 3.45/0.99      | r2_hidden(X0,sK4) != iProver_top
% 3.45/0.99      | v1_relat_1(sK7) != iProver_top
% 3.45/0.99      | v1_funct_1(sK7) != iProver_top ),
% 3.45/0.99      inference(light_normalisation,[status(thm)],[c_9138,c_7099]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_31,negated_conjecture,
% 3.45/0.99      ( v1_funct_1(sK7) ),
% 3.45/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_32,plain,
% 3.45/0.99      ( v1_funct_1(sK7) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_17,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/0.99      | v1_relat_1(X0) ),
% 3.45/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1106,plain,
% 3.45/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5))))
% 3.45/0.99      | v1_relat_1(sK7) ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1107,plain,
% 3.45/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5)))) != iProver_top
% 3.45/0.99      | v1_relat_1(sK7) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_1106]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_9723,plain,
% 3.45/0.99      ( k1_funct_1(sK7,X0) = sK5 | r2_hidden(X0,sK4) != iProver_top ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_9144,c_32,c_34,c_1107]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_9734,plain,
% 3.45/0.99      ( k1_funct_1(sK7,sK6) = sK5 ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_802,c_9723]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_27,negated_conjecture,
% 3.45/0.99      ( k1_funct_1(sK7,sK6) != sK5 ),
% 3.45/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(contradiction,plain,
% 3.45/0.99      ( $false ),
% 3.45/0.99      inference(minisat,[status(thm)],[c_9734,c_27]) ).
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  ------                               Statistics
% 3.45/0.99  
% 3.45/0.99  ------ Selected
% 3.45/0.99  
% 3.45/0.99  total_time:                             0.353
% 3.45/0.99  
%------------------------------------------------------------------------------
