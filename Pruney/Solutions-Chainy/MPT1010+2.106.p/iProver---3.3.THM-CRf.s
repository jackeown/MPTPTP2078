%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:22 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 295 expanded)
%              Number of clauses        :   53 (  70 expanded)
%              Number of leaves         :   20 (  69 expanded)
%              Depth                    :   18
%              Number of atoms          :  434 (1013 expanded)
%              Number of equality atoms :  219 ( 457 expanded)
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

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f27])).

fof(f41,plain,
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

fof(f42,plain,
    ( k1_funct_1(sK7,sK6) != sK5
    & r2_hidden(sK6,sK4)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5))))
    & v1_funct_2(sK7,sK4,k1_tarski(sK5))
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f28,f41])).

fof(f75,plain,(
    r2_hidden(sK6,sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f38,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f38,f37,f36])).

fof(f58,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f92,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f93,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f74,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f77])).

fof(f85,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) ),
    inference(definition_unfolding,[],[f74,f78])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f44,f77])).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f84])).

fof(f72,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

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

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f73,plain,(
    v1_funct_2(sK7,sK4,k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f42])).

fof(f86,plain,(
    v1_funct_2(sK7,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f73,f78])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f45,f77])).

fof(f89,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f83])).

fof(f90,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f89])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f76,plain,(
    k1_funct_1(sK7,sK6) != sK5 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_27,negated_conjecture,
    ( r2_hidden(sK6,sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_773,plain,
    ( r2_hidden(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_786,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_772,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_780,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1486,plain,
    ( k2_relset_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK7) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_772,c_780])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_782,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2022,plain,
    ( m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1486,c_782])).

cnf(c_33,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2699,plain,
    ( m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2022,c_33])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_792,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2704,plain,
    ( r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2699,c_792])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_793,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2795,plain,
    ( sK5 = X0
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2704,c_793])).

cnf(c_4895,plain,
    ( k1_funct_1(sK7,X0) = sK5
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_786,c_2795])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_31,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1155,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))
    | v1_relat_1(sK7) ),
    inference(resolution,[status(thm)],[c_8,c_28])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1184,plain,
    ( v1_relat_1(sK7) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1155,c_9])).

cnf(c_1185,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1184])).

cnf(c_6110,plain,
    ( k1_funct_1(sK7,X0) = sK5
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4895,c_31,c_1185])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_774,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3755,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = k1_xboole_0
    | k1_relset_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK7) = sK4
    | v1_funct_2(sK7,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_772,c_774])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_781,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1663,plain,
    ( k1_relset_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_772,c_781])).

cnf(c_3759,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = k1_xboole_0
    | k1_relat_1(sK7) = sK4
    | v1_funct_2(sK7,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3755,c_1663])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK7,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3772,plain,
    ( ~ v1_funct_2(sK7,sK4,k2_enumset1(sK5,sK5,sK5,sK5))
    | k2_enumset1(sK5,sK5,sK5,sK5) = k1_xboole_0
    | k1_relat_1(sK7) = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3759])).

cnf(c_3774,plain,
    ( k1_relat_1(sK7) = sK4
    | k2_enumset1(sK5,sK5,sK5,sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3759,c_29,c_3772])).

cnf(c_3775,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = k1_xboole_0
    | k1_relat_1(sK7) = sK4 ),
    inference(renaming,[status(thm)],[c_3774])).

cnf(c_5,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_794,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_783,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1472,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_794,c_783])).

cnf(c_3778,plain,
    ( k1_relat_1(sK7) = sK4
    | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3775,c_1472])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_799,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5767,plain,
    ( k1_relat_1(sK7) = sK4 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3778,c_799])).

cnf(c_6116,plain,
    ( k1_funct_1(sK7,X0) = sK5
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6110,c_5767])).

cnf(c_6125,plain,
    ( k1_funct_1(sK7,sK6) = sK5 ),
    inference(superposition,[status(thm)],[c_773,c_6116])).

cnf(c_26,negated_conjecture,
    ( k1_funct_1(sK7,sK6) != sK5 ),
    inference(cnf_transformation,[],[f76])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6125,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:49:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.46/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/0.99  
% 3.46/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.46/0.99  
% 3.46/0.99  ------  iProver source info
% 3.46/0.99  
% 3.46/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.46/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.46/0.99  git: non_committed_changes: false
% 3.46/0.99  git: last_make_outside_of_git: false
% 3.46/0.99  
% 3.46/0.99  ------ 
% 3.46/0.99  ------ Parsing...
% 3.46/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.46/0.99  
% 3.46/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.46/0.99  
% 3.46/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.46/0.99  
% 3.46/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.46/0.99  ------ Proving...
% 3.46/0.99  ------ Problem Properties 
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  clauses                                 31
% 3.46/0.99  conjectures                             5
% 3.46/0.99  EPR                                     4
% 3.46/0.99  Horn                                    23
% 3.46/0.99  unary                                   9
% 3.46/0.99  binary                                  4
% 3.46/0.99  lits                                    85
% 3.46/0.99  lits eq                                 27
% 3.46/0.99  fd_pure                                 0
% 3.46/0.99  fd_pseudo                               0
% 3.46/0.99  fd_cond                                 3
% 3.46/0.99  fd_pseudo_cond                          6
% 3.46/0.99  AC symbols                              0
% 3.46/0.99  
% 3.46/0.99  ------ Input Options Time Limit: Unbounded
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  ------ 
% 3.46/0.99  Current options:
% 3.46/0.99  ------ 
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  ------ Proving...
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  % SZS status Theorem for theBenchmark.p
% 3.46/0.99  
% 3.46/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.46/0.99  
% 3.46/0.99  fof(f15,conjecture,(
% 3.46/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 3.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f16,negated_conjecture,(
% 3.46/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 3.46/0.99    inference(negated_conjecture,[],[f15])).
% 3.46/0.99  
% 3.46/0.99  fof(f27,plain,(
% 3.46/0.99    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 3.46/0.99    inference(ennf_transformation,[],[f16])).
% 3.46/0.99  
% 3.46/0.99  fof(f28,plain,(
% 3.46/0.99    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 3.46/0.99    inference(flattening,[],[f27])).
% 3.46/0.99  
% 3.46/0.99  fof(f41,plain,(
% 3.46/0.99    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK7,sK6) != sK5 & r2_hidden(sK6,sK4) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5)))) & v1_funct_2(sK7,sK4,k1_tarski(sK5)) & v1_funct_1(sK7))),
% 3.46/0.99    introduced(choice_axiom,[])).
% 3.46/0.99  
% 3.46/0.99  fof(f42,plain,(
% 3.46/0.99    k1_funct_1(sK7,sK6) != sK5 & r2_hidden(sK6,sK4) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5)))) & v1_funct_2(sK7,sK4,k1_tarski(sK5)) & v1_funct_1(sK7)),
% 3.46/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f28,f41])).
% 3.46/0.99  
% 3.46/0.99  fof(f75,plain,(
% 3.46/0.99    r2_hidden(sK6,sK4)),
% 3.46/0.99    inference(cnf_transformation,[],[f42])).
% 3.46/0.99  
% 3.46/0.99  fof(f9,axiom,(
% 3.46/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f19,plain,(
% 3.46/0.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.46/0.99    inference(ennf_transformation,[],[f9])).
% 3.46/0.99  
% 3.46/0.99  fof(f20,plain,(
% 3.46/0.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.46/0.99    inference(flattening,[],[f19])).
% 3.46/0.99  
% 3.46/0.99  fof(f34,plain,(
% 3.46/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.46/0.99    inference(nnf_transformation,[],[f20])).
% 3.46/0.99  
% 3.46/0.99  fof(f35,plain,(
% 3.46/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.46/0.99    inference(rectify,[],[f34])).
% 3.46/0.99  
% 3.46/0.99  fof(f38,plain,(
% 3.46/0.99    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 3.46/0.99    introduced(choice_axiom,[])).
% 3.46/0.99  
% 3.46/0.99  fof(f37,plain,(
% 3.46/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 3.46/0.99    introduced(choice_axiom,[])).
% 3.46/0.99  
% 3.46/0.99  fof(f36,plain,(
% 3.46/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 3.46/0.99    introduced(choice_axiom,[])).
% 3.46/0.99  
% 3.46/0.99  fof(f39,plain,(
% 3.46/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.46/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f38,f37,f36])).
% 3.46/0.99  
% 3.46/0.99  fof(f58,plain,(
% 3.46/0.99    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.46/0.99    inference(cnf_transformation,[],[f39])).
% 3.46/0.99  
% 3.46/0.99  fof(f92,plain,(
% 3.46/0.99    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.46/0.99    inference(equality_resolution,[],[f58])).
% 3.46/0.99  
% 3.46/0.99  fof(f93,plain,(
% 3.46/0.99    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.46/0.99    inference(equality_resolution,[],[f92])).
% 3.46/0.99  
% 3.46/0.99  fof(f74,plain,(
% 3.46/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5))))),
% 3.46/0.99    inference(cnf_transformation,[],[f42])).
% 3.46/0.99  
% 3.46/0.99  fof(f3,axiom,(
% 3.46/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f50,plain,(
% 3.46/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.46/0.99    inference(cnf_transformation,[],[f3])).
% 3.46/0.99  
% 3.46/0.99  fof(f4,axiom,(
% 3.46/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f51,plain,(
% 3.46/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.46/0.99    inference(cnf_transformation,[],[f4])).
% 3.46/0.99  
% 3.46/0.99  fof(f5,axiom,(
% 3.46/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f52,plain,(
% 3.46/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.46/0.99    inference(cnf_transformation,[],[f5])).
% 3.46/0.99  
% 3.46/0.99  fof(f77,plain,(
% 3.46/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.46/0.99    inference(definition_unfolding,[],[f51,f52])).
% 3.46/0.99  
% 3.46/0.99  fof(f78,plain,(
% 3.46/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.46/0.99    inference(definition_unfolding,[],[f50,f77])).
% 3.46/0.99  
% 3.46/0.99  fof(f85,plain,(
% 3.46/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5))))),
% 3.46/0.99    inference(definition_unfolding,[],[f74,f78])).
% 3.46/0.99  
% 3.46/0.99  fof(f13,axiom,(
% 3.46/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f24,plain,(
% 3.46/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.46/0.99    inference(ennf_transformation,[],[f13])).
% 3.46/0.99  
% 3.46/0.99  fof(f65,plain,(
% 3.46/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.46/0.99    inference(cnf_transformation,[],[f24])).
% 3.46/0.99  
% 3.46/0.99  fof(f11,axiom,(
% 3.46/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 3.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f22,plain,(
% 3.46/0.99    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.46/0.99    inference(ennf_transformation,[],[f11])).
% 3.46/0.99  
% 3.46/0.99  fof(f63,plain,(
% 3.46/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.46/0.99    inference(cnf_transformation,[],[f22])).
% 3.46/0.99  
% 3.46/0.99  fof(f6,axiom,(
% 3.46/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f17,plain,(
% 3.46/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.46/0.99    inference(ennf_transformation,[],[f6])).
% 3.46/0.99  
% 3.46/0.99  fof(f53,plain,(
% 3.46/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.46/0.99    inference(cnf_transformation,[],[f17])).
% 3.46/0.99  
% 3.46/0.99  fof(f2,axiom,(
% 3.46/0.99    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f29,plain,(
% 3.46/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.46/0.99    inference(nnf_transformation,[],[f2])).
% 3.46/0.99  
% 3.46/0.99  fof(f30,plain,(
% 3.46/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.46/0.99    inference(flattening,[],[f29])).
% 3.46/0.99  
% 3.46/0.99  fof(f31,plain,(
% 3.46/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.46/0.99    inference(rectify,[],[f30])).
% 3.46/0.99  
% 3.46/0.99  fof(f32,plain,(
% 3.46/0.99    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.46/0.99    introduced(choice_axiom,[])).
% 3.46/0.99  
% 3.46/0.99  fof(f33,plain,(
% 3.46/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.46/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 3.46/0.99  
% 3.46/0.99  fof(f44,plain,(
% 3.46/0.99    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 3.46/0.99    inference(cnf_transformation,[],[f33])).
% 3.46/0.99  
% 3.46/0.99  fof(f84,plain,(
% 3.46/0.99    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 3.46/0.99    inference(definition_unfolding,[],[f44,f77])).
% 3.46/0.99  
% 3.46/0.99  fof(f91,plain,(
% 3.46/0.99    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 3.46/0.99    inference(equality_resolution,[],[f84])).
% 3.46/0.99  
% 3.46/0.99  fof(f72,plain,(
% 3.46/0.99    v1_funct_1(sK7)),
% 3.46/0.99    inference(cnf_transformation,[],[f42])).
% 3.46/0.99  
% 3.46/0.99  fof(f7,axiom,(
% 3.46/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f18,plain,(
% 3.46/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.46/0.99    inference(ennf_transformation,[],[f7])).
% 3.46/0.99  
% 3.46/0.99  fof(f54,plain,(
% 3.46/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.46/0.99    inference(cnf_transformation,[],[f18])).
% 3.46/0.99  
% 3.46/0.99  fof(f8,axiom,(
% 3.46/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f55,plain,(
% 3.46/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.46/0.99    inference(cnf_transformation,[],[f8])).
% 3.46/0.99  
% 3.46/0.99  fof(f14,axiom,(
% 3.46/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f25,plain,(
% 3.46/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.46/0.99    inference(ennf_transformation,[],[f14])).
% 3.46/0.99  
% 3.46/0.99  fof(f26,plain,(
% 3.46/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.46/0.99    inference(flattening,[],[f25])).
% 3.46/0.99  
% 3.46/0.99  fof(f40,plain,(
% 3.46/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.46/0.99    inference(nnf_transformation,[],[f26])).
% 3.46/0.99  
% 3.46/0.99  fof(f66,plain,(
% 3.46/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.46/0.99    inference(cnf_transformation,[],[f40])).
% 3.46/0.99  
% 3.46/0.99  fof(f12,axiom,(
% 3.46/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f23,plain,(
% 3.46/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.46/0.99    inference(ennf_transformation,[],[f12])).
% 3.46/0.99  
% 3.46/0.99  fof(f64,plain,(
% 3.46/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.46/0.99    inference(cnf_transformation,[],[f23])).
% 3.46/0.99  
% 3.46/0.99  fof(f73,plain,(
% 3.46/0.99    v1_funct_2(sK7,sK4,k1_tarski(sK5))),
% 3.46/0.99    inference(cnf_transformation,[],[f42])).
% 3.46/0.99  
% 3.46/0.99  fof(f86,plain,(
% 3.46/0.99    v1_funct_2(sK7,sK4,k2_enumset1(sK5,sK5,sK5,sK5))),
% 3.46/0.99    inference(definition_unfolding,[],[f73,f78])).
% 3.46/0.99  
% 3.46/0.99  fof(f45,plain,(
% 3.46/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.46/0.99    inference(cnf_transformation,[],[f33])).
% 3.46/0.99  
% 3.46/0.99  fof(f83,plain,(
% 3.46/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 3.46/0.99    inference(definition_unfolding,[],[f45,f77])).
% 3.46/0.99  
% 3.46/0.99  fof(f89,plain,(
% 3.46/0.99    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 3.46/0.99    inference(equality_resolution,[],[f83])).
% 3.46/0.99  
% 3.46/0.99  fof(f90,plain,(
% 3.46/0.99    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 3.46/0.99    inference(equality_resolution,[],[f89])).
% 3.46/0.99  
% 3.46/0.99  fof(f10,axiom,(
% 3.46/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f21,plain,(
% 3.46/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.46/0.99    inference(ennf_transformation,[],[f10])).
% 3.46/0.99  
% 3.46/0.99  fof(f62,plain,(
% 3.46/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.46/0.99    inference(cnf_transformation,[],[f21])).
% 3.46/0.99  
% 3.46/0.99  fof(f1,axiom,(
% 3.46/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f43,plain,(
% 3.46/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.46/0.99    inference(cnf_transformation,[],[f1])).
% 3.46/0.99  
% 3.46/0.99  fof(f76,plain,(
% 3.46/0.99    k1_funct_1(sK7,sK6) != sK5),
% 3.46/0.99    inference(cnf_transformation,[],[f42])).
% 3.46/0.99  
% 3.46/0.99  cnf(c_27,negated_conjecture,
% 3.46/0.99      ( r2_hidden(sK6,sK4) ),
% 3.46/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_773,plain,
% 3.46/0.99      ( r2_hidden(sK6,sK4) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_13,plain,
% 3.46/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.46/0.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.46/0.99      | ~ v1_funct_1(X1)
% 3.46/0.99      | ~ v1_relat_1(X1) ),
% 3.46/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_786,plain,
% 3.46/0.99      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 3.46/0.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 3.46/0.99      | v1_funct_1(X1) != iProver_top
% 3.46/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_28,negated_conjecture,
% 3.46/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) ),
% 3.46/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_772,plain,
% 3.46/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_19,plain,
% 3.46/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.46/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.46/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_780,plain,
% 3.46/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.46/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_1486,plain,
% 3.46/0.99      ( k2_relset_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK7) = k2_relat_1(sK7) ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_772,c_780]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_17,plain,
% 3.46/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.46/0.99      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 3.46/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_782,plain,
% 3.46/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.46/0.99      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2022,plain,
% 3.46/0.99      ( m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5))) = iProver_top
% 3.46/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) != iProver_top ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_1486,c_782]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_33,plain,
% 3.46/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2699,plain,
% 3.46/0.99      ( m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5))) = iProver_top ),
% 3.46/0.99      inference(global_propositional_subsumption,
% 3.46/0.99                [status(thm)],
% 3.46/0.99                [c_2022,c_33]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_7,plain,
% 3.46/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.46/0.99      | ~ r2_hidden(X2,X0)
% 3.46/0.99      | r2_hidden(X2,X1) ),
% 3.46/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_792,plain,
% 3.46/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.46/0.99      | r2_hidden(X2,X0) != iProver_top
% 3.46/0.99      | r2_hidden(X2,X1) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2704,plain,
% 3.46/0.99      ( r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top
% 3.46/0.99      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_2699,c_792]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_6,plain,
% 3.46/0.99      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 3.46/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_793,plain,
% 3.46/0.99      ( X0 = X1
% 3.46/0.99      | X0 = X2
% 3.46/0.99      | r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) != iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2795,plain,
% 3.46/0.99      ( sK5 = X0 | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_2704,c_793]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_4895,plain,
% 3.46/0.99      ( k1_funct_1(sK7,X0) = sK5
% 3.46/0.99      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.46/0.99      | v1_funct_1(sK7) != iProver_top
% 3.46/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_786,c_2795]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_30,negated_conjecture,
% 3.46/0.99      ( v1_funct_1(sK7) ),
% 3.46/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_31,plain,
% 3.46/0.99      ( v1_funct_1(sK7) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_8,plain,
% 3.46/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.46/0.99      | ~ v1_relat_1(X1)
% 3.46/0.99      | v1_relat_1(X0) ),
% 3.46/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_1155,plain,
% 3.46/0.99      ( ~ v1_relat_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))
% 3.46/0.99      | v1_relat_1(sK7) ),
% 3.46/0.99      inference(resolution,[status(thm)],[c_8,c_28]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_9,plain,
% 3.46/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.46/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_1184,plain,
% 3.46/0.99      ( v1_relat_1(sK7) ),
% 3.46/0.99      inference(forward_subsumption_resolution,
% 3.46/0.99                [status(thm)],
% 3.46/0.99                [c_1155,c_9]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_1185,plain,
% 3.46/0.99      ( v1_relat_1(sK7) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_1184]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_6110,plain,
% 3.46/0.99      ( k1_funct_1(sK7,X0) = sK5
% 3.46/0.99      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 3.46/0.99      inference(global_propositional_subsumption,
% 3.46/0.99                [status(thm)],
% 3.46/0.99                [c_4895,c_31,c_1185]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_25,plain,
% 3.46/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.46/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.46/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.46/0.99      | k1_xboole_0 = X2 ),
% 3.46/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_774,plain,
% 3.46/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 3.46/0.99      | k1_xboole_0 = X1
% 3.46/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.46/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_3755,plain,
% 3.46/0.99      ( k2_enumset1(sK5,sK5,sK5,sK5) = k1_xboole_0
% 3.46/0.99      | k1_relset_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK7) = sK4
% 3.46/0.99      | v1_funct_2(sK7,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_772,c_774]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_18,plain,
% 3.46/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.46/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.46/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_781,plain,
% 3.46/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.46/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_1663,plain,
% 3.46/0.99      ( k1_relset_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK7) = k1_relat_1(sK7) ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_772,c_781]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_3759,plain,
% 3.46/0.99      ( k2_enumset1(sK5,sK5,sK5,sK5) = k1_xboole_0
% 3.46/0.99      | k1_relat_1(sK7) = sK4
% 3.46/0.99      | v1_funct_2(sK7,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top ),
% 3.46/0.99      inference(demodulation,[status(thm)],[c_3755,c_1663]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_29,negated_conjecture,
% 3.46/0.99      ( v1_funct_2(sK7,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 3.46/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_3772,plain,
% 3.46/0.99      ( ~ v1_funct_2(sK7,sK4,k2_enumset1(sK5,sK5,sK5,sK5))
% 3.46/0.99      | k2_enumset1(sK5,sK5,sK5,sK5) = k1_xboole_0
% 3.46/0.99      | k1_relat_1(sK7) = sK4 ),
% 3.46/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3759]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_3774,plain,
% 3.46/0.99      ( k1_relat_1(sK7) = sK4
% 3.46/0.99      | k2_enumset1(sK5,sK5,sK5,sK5) = k1_xboole_0 ),
% 3.46/0.99      inference(global_propositional_subsumption,
% 3.46/0.99                [status(thm)],
% 3.46/0.99                [c_3759,c_29,c_3772]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_3775,plain,
% 3.46/0.99      ( k2_enumset1(sK5,sK5,sK5,sK5) = k1_xboole_0
% 3.46/0.99      | k1_relat_1(sK7) = sK4 ),
% 3.46/0.99      inference(renaming,[status(thm)],[c_3774]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_5,plain,
% 3.46/0.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 3.46/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_794,plain,
% 3.46/0.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_16,plain,
% 3.46/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.46/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_783,plain,
% 3.46/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.46/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_1472,plain,
% 3.46/0.99      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X0) != iProver_top ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_794,c_783]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_3778,plain,
% 3.46/0.99      ( k1_relat_1(sK7) = sK4
% 3.46/0.99      | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_3775,c_1472]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_0,plain,
% 3.46/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.46/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_799,plain,
% 3.46/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_5767,plain,
% 3.46/0.99      ( k1_relat_1(sK7) = sK4 ),
% 3.46/0.99      inference(forward_subsumption_resolution,
% 3.46/0.99                [status(thm)],
% 3.46/0.99                [c_3778,c_799]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_6116,plain,
% 3.46/0.99      ( k1_funct_1(sK7,X0) = sK5 | r2_hidden(X0,sK4) != iProver_top ),
% 3.46/0.99      inference(light_normalisation,[status(thm)],[c_6110,c_5767]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_6125,plain,
% 3.46/0.99      ( k1_funct_1(sK7,sK6) = sK5 ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_773,c_6116]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_26,negated_conjecture,
% 3.46/0.99      ( k1_funct_1(sK7,sK6) != sK5 ),
% 3.46/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(contradiction,plain,
% 3.46/0.99      ( $false ),
% 3.46/0.99      inference(minisat,[status(thm)],[c_6125,c_26]) ).
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.46/0.99  
% 3.46/0.99  ------                               Statistics
% 3.46/0.99  
% 3.46/0.99  ------ Selected
% 3.46/0.99  
% 3.46/0.99  total_time:                             0.201
% 3.46/0.99  
%------------------------------------------------------------------------------
