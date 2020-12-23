%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:54 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 373 expanded)
%              Number of clauses        :   59 ( 130 expanded)
%              Number of leaves         :   14 (  82 expanded)
%              Depth                    :   18
%              Number of atoms          :  396 (1694 expanded)
%              Number of equality atoms :  115 ( 361 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f24])).

fof(f28,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
        & r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1,X2)) = X3
        & r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK0(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK0(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK0(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( k1_funct_1(X0,sK1(X0,X1,X2)) = sK0(X0,X1,X2)
                  & r2_hidden(sK1(X0,X1,X2),X1)
                  & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
                    & r2_hidden(sK2(X0,X1,X6),X1)
                    & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f28,f27,f26])).

fof(f41,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f57,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f20])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK7
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X5,X0) )
        & r2_hidden(sK7,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK6,X5) != X4
              | ~ r2_hidden(X5,sK5)
              | ~ r2_hidden(X5,sK3) )
          & r2_hidden(X4,k7_relset_1(sK3,sK4,sK6,sK5)) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ! [X5] :
        ( k1_funct_1(sK6,X5) != sK7
        | ~ r2_hidden(X5,sK5)
        | ~ r2_hidden(X5,sK3) )
    & r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f21,f31,f30])).

fof(f50,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f32])).

fof(f40,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f51,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,(
    r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(cnf_transformation,[],[f32])).

fof(f42,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f53,plain,(
    ! [X5] :
      ( k1_funct_1(sK6,X5) != sK7
      | ~ r2_hidden(X5,sK5)
      | ~ r2_hidden(X5,sK3) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_497,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_498,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
    | r2_hidden(sK2(sK6,X1,X0),X1)
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_497])).

cnf(c_1467,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(sK6,X1,X0),X1) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_498])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_482,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_20])).

cnf(c_483,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
    | r2_hidden(sK2(sK6,X1,X0),k1_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_1468,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(sK6,X1,X0),k1_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_483])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1472,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_15,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_286,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_15,c_5])).

cnf(c_1469,plain,
    ( r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_286])).

cnf(c_2527,plain,
    ( r1_tarski(k1_relat_1(sK6),sK3) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1472,c_1469])).

cnf(c_22,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1627,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK3,sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1628,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK3,sK4)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1627])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_164,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_210,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_164])).

cnf(c_1675,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_210])).

cnf(c_1716,plain,
    ( ~ r1_tarski(sK6,k2_zfmisc_1(sK3,sK4))
    | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1675])).

cnf(c_1717,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1716])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1737,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1738,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1737])).

cnf(c_2024,plain,
    ( r1_tarski(k1_relat_1(sK6),sK3)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_286])).

cnf(c_2025,plain,
    ( r1_tarski(k1_relat_1(sK6),sK3) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2024])).

cnf(c_2627,plain,
    ( r1_tarski(k1_relat_1(sK6),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2527,c_22,c_1628,c_1717,c_1738,c_2025])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_207,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_0,c_164])).

cnf(c_1471,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_207])).

cnf(c_3227,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2627,c_1471])).

cnf(c_3320,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(sK6,X1,X0),sK3) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_3227])).

cnf(c_3648,plain,
    ( r2_hidden(sK2(sK6,X1,X0),sK3) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3320,c_22,c_1628,c_1717,c_1738])).

cnf(c_3649,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(sK6,X1,X0),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3648])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1475,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1934,plain,
    ( k7_relset_1(sK3,sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_1472,c_1475])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1473,plain,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2031,plain,
    ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1934,c_1473])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK2(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_512,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK2(X1,X2,X0)) = X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_513,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK2(sK6,X1,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_1466,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0,X1)) = X1
    | r2_hidden(X1,k9_relat_1(sK6,X0)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_513])).

cnf(c_2035,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5,sK7)) = sK7
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2031,c_1466])).

cnf(c_2323,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5,sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2035,c_22,c_1628,c_1717,c_1738])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK5)
    | k1_funct_1(sK6,X0) != sK7 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1474,plain,
    ( k1_funct_1(sK6,X0) != sK7
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2327,plain,
    ( r2_hidden(sK2(sK6,sK5,sK7),sK3) != iProver_top
    | r2_hidden(sK2(sK6,sK5,sK7),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2323,c_1474])).

cnf(c_3657,plain,
    ( r2_hidden(sK2(sK6,sK5,sK7),sK5) != iProver_top
    | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3649,c_2327])).

cnf(c_3675,plain,
    ( r2_hidden(sK2(sK6,sK5,sK7),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3657,c_2031])).

cnf(c_3680,plain,
    ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1467,c_3675])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3680,c_2031,c_1738,c_1717,c_1628,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:37:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.35/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/0.99  
% 2.35/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.35/0.99  
% 2.35/0.99  ------  iProver source info
% 2.35/0.99  
% 2.35/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.35/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.35/0.99  git: non_committed_changes: false
% 2.35/0.99  git: last_make_outside_of_git: false
% 2.35/0.99  
% 2.35/0.99  ------ 
% 2.35/0.99  
% 2.35/0.99  ------ Input Options
% 2.35/0.99  
% 2.35/0.99  --out_options                           all
% 2.35/0.99  --tptp_safe_out                         true
% 2.35/0.99  --problem_path                          ""
% 2.35/0.99  --include_path                          ""
% 2.35/0.99  --clausifier                            res/vclausify_rel
% 2.35/0.99  --clausifier_options                    --mode clausify
% 2.35/0.99  --stdin                                 false
% 2.35/0.99  --stats_out                             all
% 2.35/0.99  
% 2.35/0.99  ------ General Options
% 2.35/0.99  
% 2.35/0.99  --fof                                   false
% 2.35/0.99  --time_out_real                         305.
% 2.35/0.99  --time_out_virtual                      -1.
% 2.35/0.99  --symbol_type_check                     false
% 2.35/0.99  --clausify_out                          false
% 2.35/0.99  --sig_cnt_out                           false
% 2.35/0.99  --trig_cnt_out                          false
% 2.35/0.99  --trig_cnt_out_tolerance                1.
% 2.35/0.99  --trig_cnt_out_sk_spl                   false
% 2.35/0.99  --abstr_cl_out                          false
% 2.35/0.99  
% 2.35/0.99  ------ Global Options
% 2.35/0.99  
% 2.35/0.99  --schedule                              default
% 2.35/0.99  --add_important_lit                     false
% 2.35/0.99  --prop_solver_per_cl                    1000
% 2.35/0.99  --min_unsat_core                        false
% 2.35/0.99  --soft_assumptions                      false
% 2.35/0.99  --soft_lemma_size                       3
% 2.35/0.99  --prop_impl_unit_size                   0
% 2.35/0.99  --prop_impl_unit                        []
% 2.35/0.99  --share_sel_clauses                     true
% 2.35/0.99  --reset_solvers                         false
% 2.35/0.99  --bc_imp_inh                            [conj_cone]
% 2.35/0.99  --conj_cone_tolerance                   3.
% 2.35/0.99  --extra_neg_conj                        none
% 2.35/0.99  --large_theory_mode                     true
% 2.35/0.99  --prolific_symb_bound                   200
% 2.35/0.99  --lt_threshold                          2000
% 2.35/0.99  --clause_weak_htbl                      true
% 2.35/0.99  --gc_record_bc_elim                     false
% 2.35/0.99  
% 2.35/0.99  ------ Preprocessing Options
% 2.35/0.99  
% 2.35/0.99  --preprocessing_flag                    true
% 2.35/0.99  --time_out_prep_mult                    0.1
% 2.35/0.99  --splitting_mode                        input
% 2.35/0.99  --splitting_grd                         true
% 2.35/0.99  --splitting_cvd                         false
% 2.35/0.99  --splitting_cvd_svl                     false
% 2.35/0.99  --splitting_nvd                         32
% 2.35/0.99  --sub_typing                            true
% 2.35/0.99  --prep_gs_sim                           true
% 2.35/0.99  --prep_unflatten                        true
% 2.35/0.99  --prep_res_sim                          true
% 2.35/0.99  --prep_upred                            true
% 2.35/0.99  --prep_sem_filter                       exhaustive
% 2.35/0.99  --prep_sem_filter_out                   false
% 2.35/0.99  --pred_elim                             true
% 2.35/0.99  --res_sim_input                         true
% 2.35/0.99  --eq_ax_congr_red                       true
% 2.35/0.99  --pure_diseq_elim                       true
% 2.35/0.99  --brand_transform                       false
% 2.35/0.99  --non_eq_to_eq                          false
% 2.35/0.99  --prep_def_merge                        true
% 2.35/0.99  --prep_def_merge_prop_impl              false
% 2.35/0.99  --prep_def_merge_mbd                    true
% 2.35/0.99  --prep_def_merge_tr_red                 false
% 2.35/0.99  --prep_def_merge_tr_cl                  false
% 2.35/0.99  --smt_preprocessing                     true
% 2.35/0.99  --smt_ac_axioms                         fast
% 2.35/0.99  --preprocessed_out                      false
% 2.35/0.99  --preprocessed_stats                    false
% 2.35/0.99  
% 2.35/0.99  ------ Abstraction refinement Options
% 2.35/0.99  
% 2.35/0.99  --abstr_ref                             []
% 2.35/0.99  --abstr_ref_prep                        false
% 2.35/0.99  --abstr_ref_until_sat                   false
% 2.35/0.99  --abstr_ref_sig_restrict                funpre
% 2.35/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.35/0.99  --abstr_ref_under                       []
% 2.35/0.99  
% 2.35/0.99  ------ SAT Options
% 2.35/0.99  
% 2.35/0.99  --sat_mode                              false
% 2.35/0.99  --sat_fm_restart_options                ""
% 2.35/0.99  --sat_gr_def                            false
% 2.35/0.99  --sat_epr_types                         true
% 2.35/0.99  --sat_non_cyclic_types                  false
% 2.35/0.99  --sat_finite_models                     false
% 2.35/0.99  --sat_fm_lemmas                         false
% 2.35/0.99  --sat_fm_prep                           false
% 2.35/0.99  --sat_fm_uc_incr                        true
% 2.35/0.99  --sat_out_model                         small
% 2.35/0.99  --sat_out_clauses                       false
% 2.35/0.99  
% 2.35/0.99  ------ QBF Options
% 2.35/0.99  
% 2.35/0.99  --qbf_mode                              false
% 2.35/0.99  --qbf_elim_univ                         false
% 2.35/0.99  --qbf_dom_inst                          none
% 2.35/0.99  --qbf_dom_pre_inst                      false
% 2.35/0.99  --qbf_sk_in                             false
% 2.35/0.99  --qbf_pred_elim                         true
% 2.35/0.99  --qbf_split                             512
% 2.35/0.99  
% 2.35/0.99  ------ BMC1 Options
% 2.35/0.99  
% 2.35/0.99  --bmc1_incremental                      false
% 2.35/0.99  --bmc1_axioms                           reachable_all
% 2.35/0.99  --bmc1_min_bound                        0
% 2.35/0.99  --bmc1_max_bound                        -1
% 2.35/0.99  --bmc1_max_bound_default                -1
% 2.35/0.99  --bmc1_symbol_reachability              true
% 2.35/0.99  --bmc1_property_lemmas                  false
% 2.35/0.99  --bmc1_k_induction                      false
% 2.35/0.99  --bmc1_non_equiv_states                 false
% 2.35/0.99  --bmc1_deadlock                         false
% 2.35/0.99  --bmc1_ucm                              false
% 2.35/0.99  --bmc1_add_unsat_core                   none
% 2.35/0.99  --bmc1_unsat_core_children              false
% 2.35/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.35/0.99  --bmc1_out_stat                         full
% 2.35/0.99  --bmc1_ground_init                      false
% 2.35/0.99  --bmc1_pre_inst_next_state              false
% 2.35/0.99  --bmc1_pre_inst_state                   false
% 2.35/0.99  --bmc1_pre_inst_reach_state             false
% 2.35/0.99  --bmc1_out_unsat_core                   false
% 2.35/0.99  --bmc1_aig_witness_out                  false
% 2.35/0.99  --bmc1_verbose                          false
% 2.35/0.99  --bmc1_dump_clauses_tptp                false
% 2.35/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.35/0.99  --bmc1_dump_file                        -
% 2.35/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.35/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.35/0.99  --bmc1_ucm_extend_mode                  1
% 2.35/0.99  --bmc1_ucm_init_mode                    2
% 2.35/0.99  --bmc1_ucm_cone_mode                    none
% 2.35/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.35/0.99  --bmc1_ucm_relax_model                  4
% 2.35/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.35/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.35/0.99  --bmc1_ucm_layered_model                none
% 2.35/0.99  --bmc1_ucm_max_lemma_size               10
% 2.35/0.99  
% 2.35/0.99  ------ AIG Options
% 2.35/0.99  
% 2.35/0.99  --aig_mode                              false
% 2.35/0.99  
% 2.35/0.99  ------ Instantiation Options
% 2.35/0.99  
% 2.35/0.99  --instantiation_flag                    true
% 2.35/0.99  --inst_sos_flag                         false
% 2.35/0.99  --inst_sos_phase                        true
% 2.35/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.35/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.35/0.99  --inst_lit_sel_side                     num_symb
% 2.35/0.99  --inst_solver_per_active                1400
% 2.35/0.99  --inst_solver_calls_frac                1.
% 2.35/0.99  --inst_passive_queue_type               priority_queues
% 2.35/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.35/0.99  --inst_passive_queues_freq              [25;2]
% 2.35/0.99  --inst_dismatching                      true
% 2.35/0.99  --inst_eager_unprocessed_to_passive     true
% 2.35/0.99  --inst_prop_sim_given                   true
% 2.35/0.99  --inst_prop_sim_new                     false
% 2.35/0.99  --inst_subs_new                         false
% 2.35/0.99  --inst_eq_res_simp                      false
% 2.35/0.99  --inst_subs_given                       false
% 2.35/0.99  --inst_orphan_elimination               true
% 2.35/0.99  --inst_learning_loop_flag               true
% 2.35/0.99  --inst_learning_start                   3000
% 2.35/0.99  --inst_learning_factor                  2
% 2.35/0.99  --inst_start_prop_sim_after_learn       3
% 2.35/0.99  --inst_sel_renew                        solver
% 2.35/0.99  --inst_lit_activity_flag                true
% 2.35/0.99  --inst_restr_to_given                   false
% 2.35/0.99  --inst_activity_threshold               500
% 2.35/0.99  --inst_out_proof                        true
% 2.35/0.99  
% 2.35/0.99  ------ Resolution Options
% 2.35/0.99  
% 2.35/0.99  --resolution_flag                       true
% 2.35/0.99  --res_lit_sel                           adaptive
% 2.35/0.99  --res_lit_sel_side                      none
% 2.35/0.99  --res_ordering                          kbo
% 2.35/0.99  --res_to_prop_solver                    active
% 2.35/0.99  --res_prop_simpl_new                    false
% 2.35/0.99  --res_prop_simpl_given                  true
% 2.35/0.99  --res_passive_queue_type                priority_queues
% 2.35/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.35/0.99  --res_passive_queues_freq               [15;5]
% 2.35/0.99  --res_forward_subs                      full
% 2.35/0.99  --res_backward_subs                     full
% 2.35/0.99  --res_forward_subs_resolution           true
% 2.35/0.99  --res_backward_subs_resolution          true
% 2.35/0.99  --res_orphan_elimination                true
% 2.35/0.99  --res_time_limit                        2.
% 2.35/0.99  --res_out_proof                         true
% 2.35/0.99  
% 2.35/0.99  ------ Superposition Options
% 2.35/0.99  
% 2.35/0.99  --superposition_flag                    true
% 2.35/0.99  --sup_passive_queue_type                priority_queues
% 2.35/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.35/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.35/0.99  --demod_completeness_check              fast
% 2.35/0.99  --demod_use_ground                      true
% 2.35/0.99  --sup_to_prop_solver                    passive
% 2.35/0.99  --sup_prop_simpl_new                    true
% 2.35/0.99  --sup_prop_simpl_given                  true
% 2.35/0.99  --sup_fun_splitting                     false
% 2.35/0.99  --sup_smt_interval                      50000
% 2.35/0.99  
% 2.35/0.99  ------ Superposition Simplification Setup
% 2.35/0.99  
% 2.35/0.99  --sup_indices_passive                   []
% 2.35/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.35/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.99  --sup_full_bw                           [BwDemod]
% 2.35/0.99  --sup_immed_triv                        [TrivRules]
% 2.35/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.35/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.99  --sup_immed_bw_main                     []
% 2.35/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.35/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.35/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.35/0.99  
% 2.35/0.99  ------ Combination Options
% 2.35/0.99  
% 2.35/0.99  --comb_res_mult                         3
% 2.35/0.99  --comb_sup_mult                         2
% 2.35/0.99  --comb_inst_mult                        10
% 2.35/0.99  
% 2.35/0.99  ------ Debug Options
% 2.35/0.99  
% 2.35/0.99  --dbg_backtrace                         false
% 2.35/0.99  --dbg_dump_prop_clauses                 false
% 2.35/0.99  --dbg_dump_prop_clauses_file            -
% 2.35/0.99  --dbg_out_stat                          false
% 2.35/0.99  ------ Parsing...
% 2.35/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.35/0.99  
% 2.35/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.35/0.99  
% 2.35/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.35/0.99  
% 2.35/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.35/0.99  ------ Proving...
% 2.35/0.99  ------ Problem Properties 
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  clauses                                 18
% 2.35/0.99  conjectures                             3
% 2.35/0.99  EPR                                     2
% 2.35/0.99  Horn                                    15
% 2.35/0.99  unary                                   3
% 2.35/0.99  binary                                  3
% 2.35/0.99  lits                                    52
% 2.35/0.99  lits eq                                 9
% 2.35/0.99  fd_pure                                 0
% 2.35/0.99  fd_pseudo                               0
% 2.35/0.99  fd_cond                                 0
% 2.35/0.99  fd_pseudo_cond                          4
% 2.35/0.99  AC symbols                              0
% 2.35/0.99  
% 2.35/0.99  ------ Schedule dynamic 5 is on 
% 2.35/0.99  
% 2.35/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  ------ 
% 2.35/0.99  Current options:
% 2.35/0.99  ------ 
% 2.35/0.99  
% 2.35/0.99  ------ Input Options
% 2.35/0.99  
% 2.35/0.99  --out_options                           all
% 2.35/0.99  --tptp_safe_out                         true
% 2.35/0.99  --problem_path                          ""
% 2.35/0.99  --include_path                          ""
% 2.35/0.99  --clausifier                            res/vclausify_rel
% 2.35/0.99  --clausifier_options                    --mode clausify
% 2.35/0.99  --stdin                                 false
% 2.35/0.99  --stats_out                             all
% 2.35/0.99  
% 2.35/0.99  ------ General Options
% 2.35/0.99  
% 2.35/0.99  --fof                                   false
% 2.35/0.99  --time_out_real                         305.
% 2.35/0.99  --time_out_virtual                      -1.
% 2.35/0.99  --symbol_type_check                     false
% 2.35/0.99  --clausify_out                          false
% 2.35/0.99  --sig_cnt_out                           false
% 2.35/0.99  --trig_cnt_out                          false
% 2.35/0.99  --trig_cnt_out_tolerance                1.
% 2.35/0.99  --trig_cnt_out_sk_spl                   false
% 2.35/0.99  --abstr_cl_out                          false
% 2.35/0.99  
% 2.35/0.99  ------ Global Options
% 2.35/0.99  
% 2.35/0.99  --schedule                              default
% 2.35/0.99  --add_important_lit                     false
% 2.35/0.99  --prop_solver_per_cl                    1000
% 2.35/0.99  --min_unsat_core                        false
% 2.35/0.99  --soft_assumptions                      false
% 2.35/0.99  --soft_lemma_size                       3
% 2.35/0.99  --prop_impl_unit_size                   0
% 2.35/0.99  --prop_impl_unit                        []
% 2.35/0.99  --share_sel_clauses                     true
% 2.35/0.99  --reset_solvers                         false
% 2.35/0.99  --bc_imp_inh                            [conj_cone]
% 2.35/0.99  --conj_cone_tolerance                   3.
% 2.35/0.99  --extra_neg_conj                        none
% 2.35/0.99  --large_theory_mode                     true
% 2.35/0.99  --prolific_symb_bound                   200
% 2.35/0.99  --lt_threshold                          2000
% 2.35/0.99  --clause_weak_htbl                      true
% 2.35/0.99  --gc_record_bc_elim                     false
% 2.35/0.99  
% 2.35/0.99  ------ Preprocessing Options
% 2.35/0.99  
% 2.35/0.99  --preprocessing_flag                    true
% 2.35/0.99  --time_out_prep_mult                    0.1
% 2.35/0.99  --splitting_mode                        input
% 2.35/0.99  --splitting_grd                         true
% 2.35/0.99  --splitting_cvd                         false
% 2.35/0.99  --splitting_cvd_svl                     false
% 2.35/0.99  --splitting_nvd                         32
% 2.35/0.99  --sub_typing                            true
% 2.35/0.99  --prep_gs_sim                           true
% 2.35/0.99  --prep_unflatten                        true
% 2.35/0.99  --prep_res_sim                          true
% 2.35/0.99  --prep_upred                            true
% 2.35/0.99  --prep_sem_filter                       exhaustive
% 2.35/0.99  --prep_sem_filter_out                   false
% 2.35/0.99  --pred_elim                             true
% 2.35/0.99  --res_sim_input                         true
% 2.35/0.99  --eq_ax_congr_red                       true
% 2.35/0.99  --pure_diseq_elim                       true
% 2.35/0.99  --brand_transform                       false
% 2.35/0.99  --non_eq_to_eq                          false
% 2.35/0.99  --prep_def_merge                        true
% 2.35/0.99  --prep_def_merge_prop_impl              false
% 2.35/0.99  --prep_def_merge_mbd                    true
% 2.35/0.99  --prep_def_merge_tr_red                 false
% 2.35/0.99  --prep_def_merge_tr_cl                  false
% 2.35/0.99  --smt_preprocessing                     true
% 2.35/0.99  --smt_ac_axioms                         fast
% 2.35/0.99  --preprocessed_out                      false
% 2.35/0.99  --preprocessed_stats                    false
% 2.35/0.99  
% 2.35/0.99  ------ Abstraction refinement Options
% 2.35/0.99  
% 2.35/0.99  --abstr_ref                             []
% 2.35/0.99  --abstr_ref_prep                        false
% 2.35/0.99  --abstr_ref_until_sat                   false
% 2.35/0.99  --abstr_ref_sig_restrict                funpre
% 2.35/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.35/0.99  --abstr_ref_under                       []
% 2.35/0.99  
% 2.35/0.99  ------ SAT Options
% 2.35/0.99  
% 2.35/0.99  --sat_mode                              false
% 2.35/0.99  --sat_fm_restart_options                ""
% 2.35/0.99  --sat_gr_def                            false
% 2.35/0.99  --sat_epr_types                         true
% 2.35/0.99  --sat_non_cyclic_types                  false
% 2.35/0.99  --sat_finite_models                     false
% 2.35/0.99  --sat_fm_lemmas                         false
% 2.35/0.99  --sat_fm_prep                           false
% 2.35/0.99  --sat_fm_uc_incr                        true
% 2.35/0.99  --sat_out_model                         small
% 2.35/0.99  --sat_out_clauses                       false
% 2.35/0.99  
% 2.35/0.99  ------ QBF Options
% 2.35/0.99  
% 2.35/0.99  --qbf_mode                              false
% 2.35/0.99  --qbf_elim_univ                         false
% 2.35/0.99  --qbf_dom_inst                          none
% 2.35/0.99  --qbf_dom_pre_inst                      false
% 2.35/0.99  --qbf_sk_in                             false
% 2.35/0.99  --qbf_pred_elim                         true
% 2.35/0.99  --qbf_split                             512
% 2.35/0.99  
% 2.35/0.99  ------ BMC1 Options
% 2.35/0.99  
% 2.35/0.99  --bmc1_incremental                      false
% 2.35/0.99  --bmc1_axioms                           reachable_all
% 2.35/0.99  --bmc1_min_bound                        0
% 2.35/0.99  --bmc1_max_bound                        -1
% 2.35/0.99  --bmc1_max_bound_default                -1
% 2.35/0.99  --bmc1_symbol_reachability              true
% 2.35/0.99  --bmc1_property_lemmas                  false
% 2.35/0.99  --bmc1_k_induction                      false
% 2.35/0.99  --bmc1_non_equiv_states                 false
% 2.35/0.99  --bmc1_deadlock                         false
% 2.35/0.99  --bmc1_ucm                              false
% 2.35/0.99  --bmc1_add_unsat_core                   none
% 2.35/0.99  --bmc1_unsat_core_children              false
% 2.35/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.35/0.99  --bmc1_out_stat                         full
% 2.35/0.99  --bmc1_ground_init                      false
% 2.35/0.99  --bmc1_pre_inst_next_state              false
% 2.35/0.99  --bmc1_pre_inst_state                   false
% 2.35/0.99  --bmc1_pre_inst_reach_state             false
% 2.35/0.99  --bmc1_out_unsat_core                   false
% 2.35/0.99  --bmc1_aig_witness_out                  false
% 2.35/0.99  --bmc1_verbose                          false
% 2.35/0.99  --bmc1_dump_clauses_tptp                false
% 2.35/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.35/0.99  --bmc1_dump_file                        -
% 2.35/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.35/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.35/0.99  --bmc1_ucm_extend_mode                  1
% 2.35/0.99  --bmc1_ucm_init_mode                    2
% 2.35/0.99  --bmc1_ucm_cone_mode                    none
% 2.35/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.35/0.99  --bmc1_ucm_relax_model                  4
% 2.35/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.35/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.35/0.99  --bmc1_ucm_layered_model                none
% 2.35/0.99  --bmc1_ucm_max_lemma_size               10
% 2.35/0.99  
% 2.35/0.99  ------ AIG Options
% 2.35/0.99  
% 2.35/0.99  --aig_mode                              false
% 2.35/0.99  
% 2.35/0.99  ------ Instantiation Options
% 2.35/0.99  
% 2.35/0.99  --instantiation_flag                    true
% 2.35/0.99  --inst_sos_flag                         false
% 2.35/0.99  --inst_sos_phase                        true
% 2.35/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.35/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.35/0.99  --inst_lit_sel_side                     none
% 2.35/0.99  --inst_solver_per_active                1400
% 2.35/0.99  --inst_solver_calls_frac                1.
% 2.35/0.99  --inst_passive_queue_type               priority_queues
% 2.35/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.35/0.99  --inst_passive_queues_freq              [25;2]
% 2.35/0.99  --inst_dismatching                      true
% 2.35/0.99  --inst_eager_unprocessed_to_passive     true
% 2.35/0.99  --inst_prop_sim_given                   true
% 2.35/0.99  --inst_prop_sim_new                     false
% 2.35/0.99  --inst_subs_new                         false
% 2.35/0.99  --inst_eq_res_simp                      false
% 2.35/0.99  --inst_subs_given                       false
% 2.35/0.99  --inst_orphan_elimination               true
% 2.35/0.99  --inst_learning_loop_flag               true
% 2.35/0.99  --inst_learning_start                   3000
% 2.35/0.99  --inst_learning_factor                  2
% 2.35/0.99  --inst_start_prop_sim_after_learn       3
% 2.35/0.99  --inst_sel_renew                        solver
% 2.35/0.99  --inst_lit_activity_flag                true
% 2.35/0.99  --inst_restr_to_given                   false
% 2.35/0.99  --inst_activity_threshold               500
% 2.35/0.99  --inst_out_proof                        true
% 2.35/0.99  
% 2.35/0.99  ------ Resolution Options
% 2.35/0.99  
% 2.35/0.99  --resolution_flag                       false
% 2.35/0.99  --res_lit_sel                           adaptive
% 2.35/0.99  --res_lit_sel_side                      none
% 2.35/0.99  --res_ordering                          kbo
% 2.35/0.99  --res_to_prop_solver                    active
% 2.35/0.99  --res_prop_simpl_new                    false
% 2.35/0.99  --res_prop_simpl_given                  true
% 2.35/0.99  --res_passive_queue_type                priority_queues
% 2.35/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.35/0.99  --res_passive_queues_freq               [15;5]
% 2.35/0.99  --res_forward_subs                      full
% 2.35/0.99  --res_backward_subs                     full
% 2.35/0.99  --res_forward_subs_resolution           true
% 2.35/0.99  --res_backward_subs_resolution          true
% 2.35/0.99  --res_orphan_elimination                true
% 2.35/0.99  --res_time_limit                        2.
% 2.35/0.99  --res_out_proof                         true
% 2.35/0.99  
% 2.35/0.99  ------ Superposition Options
% 2.35/0.99  
% 2.35/0.99  --superposition_flag                    true
% 2.35/0.99  --sup_passive_queue_type                priority_queues
% 2.35/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.35/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.35/0.99  --demod_completeness_check              fast
% 2.35/0.99  --demod_use_ground                      true
% 2.35/0.99  --sup_to_prop_solver                    passive
% 2.35/0.99  --sup_prop_simpl_new                    true
% 2.35/0.99  --sup_prop_simpl_given                  true
% 2.35/0.99  --sup_fun_splitting                     false
% 2.35/0.99  --sup_smt_interval                      50000
% 2.35/0.99  
% 2.35/0.99  ------ Superposition Simplification Setup
% 2.35/0.99  
% 2.35/0.99  --sup_indices_passive                   []
% 2.35/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.35/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.99  --sup_full_bw                           [BwDemod]
% 2.35/0.99  --sup_immed_triv                        [TrivRules]
% 2.35/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.35/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.99  --sup_immed_bw_main                     []
% 2.35/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.35/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.35/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.35/0.99  
% 2.35/0.99  ------ Combination Options
% 2.35/0.99  
% 2.35/0.99  --comb_res_mult                         3
% 2.35/0.99  --comb_sup_mult                         2
% 2.35/0.99  --comb_inst_mult                        10
% 2.35/0.99  
% 2.35/0.99  ------ Debug Options
% 2.35/0.99  
% 2.35/0.99  --dbg_backtrace                         false
% 2.35/0.99  --dbg_dump_prop_clauses                 false
% 2.35/0.99  --dbg_dump_prop_clauses_file            -
% 2.35/0.99  --dbg_out_stat                          false
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  ------ Proving...
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  % SZS status Theorem for theBenchmark.p
% 2.35/0.99  
% 2.35/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.35/0.99  
% 2.35/0.99  fof(f6,axiom,(
% 2.35/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 2.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f16,plain,(
% 2.35/0.99    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.35/0.99    inference(ennf_transformation,[],[f6])).
% 2.35/0.99  
% 2.35/0.99  fof(f17,plain,(
% 2.35/0.99    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.35/0.99    inference(flattening,[],[f16])).
% 2.35/0.99  
% 2.35/0.99  fof(f24,plain,(
% 2.35/0.99    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.35/0.99    inference(nnf_transformation,[],[f17])).
% 2.35/0.99  
% 2.35/0.99  fof(f25,plain,(
% 2.35/0.99    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.35/0.99    inference(rectify,[],[f24])).
% 2.35/0.99  
% 2.35/0.99  fof(f28,plain,(
% 2.35/0.99    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1,X6)) = X6 & r2_hidden(sK2(X0,X1,X6),X1) & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0))))),
% 2.35/0.99    introduced(choice_axiom,[])).
% 2.35/0.99  
% 2.35/0.99  fof(f27,plain,(
% 2.35/0.99    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1,X2)) = X3 & r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0))))) )),
% 2.35/0.99    introduced(choice_axiom,[])).
% 2.35/0.99  
% 2.35/0.99  fof(f26,plain,(
% 2.35/0.99    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK0(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK0(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.35/0.99    introduced(choice_axiom,[])).
% 2.35/0.99  
% 2.35/0.99  fof(f29,plain,(
% 2.35/0.99    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK0(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((k1_funct_1(X0,sK1(X0,X1,X2)) = sK0(X0,X1,X2) & r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK2(X0,X1,X6)) = X6 & r2_hidden(sK2(X0,X1,X6),X1) & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.35/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f28,f27,f26])).
% 2.35/0.99  
% 2.35/0.99  fof(f41,plain,(
% 2.35/0.99    ( ! [X6,X2,X0,X1] : (r2_hidden(sK2(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.35/0.99    inference(cnf_transformation,[],[f29])).
% 2.35/0.99  
% 2.35/0.99  fof(f57,plain,(
% 2.35/0.99    ( ! [X6,X0,X1] : (r2_hidden(sK2(X0,X1,X6),X1) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.35/0.99    inference(equality_resolution,[],[f41])).
% 2.35/0.99  
% 2.35/0.99  fof(f9,conjecture,(
% 2.35/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f10,negated_conjecture,(
% 2.35/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.35/0.99    inference(negated_conjecture,[],[f9])).
% 2.35/0.99  
% 2.35/0.99  fof(f11,plain,(
% 2.35/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.35/0.99    inference(pure_predicate_removal,[],[f10])).
% 2.35/0.99  
% 2.35/0.99  fof(f20,plain,(
% 2.35/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 2.35/0.99    inference(ennf_transformation,[],[f11])).
% 2.35/0.99  
% 2.35/0.99  fof(f21,plain,(
% 2.35/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 2.35/0.99    inference(flattening,[],[f20])).
% 2.35/0.99  
% 2.35/0.99  fof(f31,plain,(
% 2.35/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK7 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(sK7,k7_relset_1(X0,X1,X3,X2)))) )),
% 2.35/0.99    introduced(choice_axiom,[])).
% 2.35/0.99  
% 2.35/0.99  fof(f30,plain,(
% 2.35/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK6,X5) != X4 | ~r2_hidden(X5,sK5) | ~r2_hidden(X5,sK3)) & r2_hidden(X4,k7_relset_1(sK3,sK4,sK6,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK6))),
% 2.35/0.99    introduced(choice_axiom,[])).
% 2.35/0.99  
% 2.35/0.99  fof(f32,plain,(
% 2.35/0.99    (! [X5] : (k1_funct_1(sK6,X5) != sK7 | ~r2_hidden(X5,sK5) | ~r2_hidden(X5,sK3)) & r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK6)),
% 2.35/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f21,f31,f30])).
% 2.35/0.99  
% 2.35/0.99  fof(f50,plain,(
% 2.35/0.99    v1_funct_1(sK6)),
% 2.35/0.99    inference(cnf_transformation,[],[f32])).
% 2.35/0.99  
% 2.35/0.99  fof(f40,plain,(
% 2.35/0.99    ( ! [X6,X2,X0,X1] : (r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.35/0.99    inference(cnf_transformation,[],[f29])).
% 2.35/0.99  
% 2.35/0.99  fof(f58,plain,(
% 2.35/0.99    ( ! [X6,X0,X1] : (r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.35/0.99    inference(equality_resolution,[],[f40])).
% 2.35/0.99  
% 2.35/0.99  fof(f51,plain,(
% 2.35/0.99    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 2.35/0.99    inference(cnf_transformation,[],[f32])).
% 2.35/0.99  
% 2.35/0.99  fof(f7,axiom,(
% 2.35/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f12,plain,(
% 2.35/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.35/0.99    inference(pure_predicate_removal,[],[f7])).
% 2.35/0.99  
% 2.35/0.99  fof(f18,plain,(
% 2.35/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.35/0.99    inference(ennf_transformation,[],[f12])).
% 2.35/0.99  
% 2.35/0.99  fof(f48,plain,(
% 2.35/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.35/0.99    inference(cnf_transformation,[],[f18])).
% 2.35/0.99  
% 2.35/0.99  fof(f4,axiom,(
% 2.35/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f15,plain,(
% 2.35/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.35/0.99    inference(ennf_transformation,[],[f4])).
% 2.35/0.99  
% 2.35/0.99  fof(f23,plain,(
% 2.35/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.35/0.99    inference(nnf_transformation,[],[f15])).
% 2.35/0.99  
% 2.35/0.99  fof(f37,plain,(
% 2.35/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.35/0.99    inference(cnf_transformation,[],[f23])).
% 2.35/0.99  
% 2.35/0.99  fof(f2,axiom,(
% 2.35/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f22,plain,(
% 2.35/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.35/0.99    inference(nnf_transformation,[],[f2])).
% 2.35/0.99  
% 2.35/0.99  fof(f34,plain,(
% 2.35/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.35/0.99    inference(cnf_transformation,[],[f22])).
% 2.35/0.99  
% 2.35/0.99  fof(f3,axiom,(
% 2.35/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f14,plain,(
% 2.35/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.35/0.99    inference(ennf_transformation,[],[f3])).
% 2.35/0.99  
% 2.35/0.99  fof(f36,plain,(
% 2.35/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.35/0.99    inference(cnf_transformation,[],[f14])).
% 2.35/0.99  
% 2.35/0.99  fof(f35,plain,(
% 2.35/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.35/0.99    inference(cnf_transformation,[],[f22])).
% 2.35/0.99  
% 2.35/0.99  fof(f5,axiom,(
% 2.35/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f39,plain,(
% 2.35/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.35/0.99    inference(cnf_transformation,[],[f5])).
% 2.35/0.99  
% 2.35/0.99  fof(f1,axiom,(
% 2.35/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f13,plain,(
% 2.35/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.35/0.99    inference(ennf_transformation,[],[f1])).
% 2.35/0.99  
% 2.35/0.99  fof(f33,plain,(
% 2.35/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.35/0.99    inference(cnf_transformation,[],[f13])).
% 2.35/0.99  
% 2.35/0.99  fof(f8,axiom,(
% 2.35/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f19,plain,(
% 2.35/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.35/0.99    inference(ennf_transformation,[],[f8])).
% 2.35/0.99  
% 2.35/0.99  fof(f49,plain,(
% 2.35/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.35/0.99    inference(cnf_transformation,[],[f19])).
% 2.35/0.99  
% 2.35/0.99  fof(f52,plain,(
% 2.35/0.99    r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))),
% 2.35/0.99    inference(cnf_transformation,[],[f32])).
% 2.35/0.99  
% 2.35/0.99  fof(f42,plain,(
% 2.35/0.99    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK2(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.35/0.99    inference(cnf_transformation,[],[f29])).
% 2.35/0.99  
% 2.35/0.99  fof(f56,plain,(
% 2.35/0.99    ( ! [X6,X0,X1] : (k1_funct_1(X0,sK2(X0,X1,X6)) = X6 | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.35/0.99    inference(equality_resolution,[],[f42])).
% 2.35/0.99  
% 2.35/0.99  fof(f53,plain,(
% 2.35/0.99    ( ! [X5] : (k1_funct_1(sK6,X5) != sK7 | ~r2_hidden(X5,sK5) | ~r2_hidden(X5,sK3)) )),
% 2.35/0.99    inference(cnf_transformation,[],[f32])).
% 2.35/0.99  
% 2.35/0.99  cnf(c_13,plain,
% 2.35/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.35/0.99      | r2_hidden(sK2(X1,X2,X0),X2)
% 2.35/0.99      | ~ v1_funct_1(X1)
% 2.35/0.99      | ~ v1_relat_1(X1) ),
% 2.35/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_20,negated_conjecture,
% 2.35/0.99      ( v1_funct_1(sK6) ),
% 2.35/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_497,plain,
% 2.35/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.35/0.99      | r2_hidden(sK2(X1,X2,X0),X2)
% 2.35/0.99      | ~ v1_relat_1(X1)
% 2.35/0.99      | sK6 != X1 ),
% 2.35/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_498,plain,
% 2.35/0.99      ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
% 2.35/0.99      | r2_hidden(sK2(sK6,X1,X0),X1)
% 2.35/0.99      | ~ v1_relat_1(sK6) ),
% 2.35/0.99      inference(unflattening,[status(thm)],[c_497]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1467,plain,
% 2.35/0.99      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 2.35/0.99      | r2_hidden(sK2(sK6,X1,X0),X1) = iProver_top
% 2.35/0.99      | v1_relat_1(sK6) != iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_498]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_14,plain,
% 2.35/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.35/0.99      | r2_hidden(sK2(X1,X2,X0),k1_relat_1(X1))
% 2.35/0.99      | ~ v1_funct_1(X1)
% 2.35/0.99      | ~ v1_relat_1(X1) ),
% 2.35/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_482,plain,
% 2.35/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.35/0.99      | r2_hidden(sK2(X1,X2,X0),k1_relat_1(X1))
% 2.35/0.99      | ~ v1_relat_1(X1)
% 2.35/0.99      | sK6 != X1 ),
% 2.35/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_483,plain,
% 2.35/0.99      ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
% 2.35/0.99      | r2_hidden(sK2(sK6,X1,X0),k1_relat_1(sK6))
% 2.35/0.99      | ~ v1_relat_1(sK6) ),
% 2.35/0.99      inference(unflattening,[status(thm)],[c_482]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1468,plain,
% 2.35/0.99      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 2.35/0.99      | r2_hidden(sK2(sK6,X1,X0),k1_relat_1(sK6)) = iProver_top
% 2.35/0.99      | v1_relat_1(sK6) != iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_483]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_19,negated_conjecture,
% 2.35/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 2.35/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1472,plain,
% 2.35/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_15,plain,
% 2.35/0.99      ( v4_relat_1(X0,X1)
% 2.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.35/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_5,plain,
% 2.35/0.99      ( ~ v4_relat_1(X0,X1)
% 2.35/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 2.35/0.99      | ~ v1_relat_1(X0) ),
% 2.35/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_286,plain,
% 2.35/0.99      ( r1_tarski(k1_relat_1(X0),X1)
% 2.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.99      | ~ v1_relat_1(X0) ),
% 2.35/0.99      inference(resolution,[status(thm)],[c_15,c_5]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1469,plain,
% 2.35/0.99      ( r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 2.35/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.35/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_286]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2527,plain,
% 2.35/0.99      ( r1_tarski(k1_relat_1(sK6),sK3) = iProver_top
% 2.35/0.99      | v1_relat_1(sK6) != iProver_top ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_1472,c_1469]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_22,plain,
% 2.35/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2,plain,
% 2.35/0.99      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.35/0.99      inference(cnf_transformation,[],[f34]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1627,plain,
% 2.35/0.99      ( r1_tarski(sK6,k2_zfmisc_1(sK3,sK4))
% 2.35/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1628,plain,
% 2.35/0.99      ( r1_tarski(sK6,k2_zfmisc_1(sK3,sK4)) = iProver_top
% 2.35/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1627]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3,plain,
% 2.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.35/0.99      | ~ v1_relat_1(X1)
% 2.35/0.99      | v1_relat_1(X0) ),
% 2.35/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1,plain,
% 2.35/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.35/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_164,plain,
% 2.35/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.35/0.99      inference(prop_impl,[status(thm)],[c_1]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_210,plain,
% 2.35/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.35/0.99      inference(bin_hyper_res,[status(thm)],[c_3,c_164]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1675,plain,
% 2.35/0.99      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 2.35/0.99      | v1_relat_1(X0)
% 2.35/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_210]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1716,plain,
% 2.35/0.99      ( ~ r1_tarski(sK6,k2_zfmisc_1(sK3,sK4))
% 2.35/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
% 2.35/0.99      | v1_relat_1(sK6) ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_1675]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1717,plain,
% 2.35/0.99      ( r1_tarski(sK6,k2_zfmisc_1(sK3,sK4)) != iProver_top
% 2.35/1.00      | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 2.35/1.00      | v1_relat_1(sK6) = iProver_top ),
% 2.35/1.00      inference(predicate_to_equality,[status(thm)],[c_1716]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_6,plain,
% 2.35/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.35/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_1737,plain,
% 2.35/1.00      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
% 2.35/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_1738,plain,
% 2.35/1.00      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 2.35/1.00      inference(predicate_to_equality,[status(thm)],[c_1737]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_2024,plain,
% 2.35/1.00      ( r1_tarski(k1_relat_1(sK6),sK3)
% 2.35/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.35/1.00      | ~ v1_relat_1(sK6) ),
% 2.35/1.00      inference(instantiation,[status(thm)],[c_286]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_2025,plain,
% 2.35/1.00      ( r1_tarski(k1_relat_1(sK6),sK3) = iProver_top
% 2.35/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 2.35/1.00      | v1_relat_1(sK6) != iProver_top ),
% 2.35/1.00      inference(predicate_to_equality,[status(thm)],[c_2024]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_2627,plain,
% 2.35/1.00      ( r1_tarski(k1_relat_1(sK6),sK3) = iProver_top ),
% 2.35/1.00      inference(global_propositional_subsumption,
% 2.35/1.00                [status(thm)],
% 2.35/1.00                [c_2527,c_22,c_1628,c_1717,c_1738,c_2025]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_0,plain,
% 2.35/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.35/1.00      | ~ r2_hidden(X2,X0)
% 2.35/1.00      | r2_hidden(X2,X1) ),
% 2.35/1.00      inference(cnf_transformation,[],[f33]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_207,plain,
% 2.35/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 2.35/1.00      inference(bin_hyper_res,[status(thm)],[c_0,c_164]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_1471,plain,
% 2.35/1.00      ( r1_tarski(X0,X1) != iProver_top
% 2.35/1.00      | r2_hidden(X2,X0) != iProver_top
% 2.35/1.00      | r2_hidden(X2,X1) = iProver_top ),
% 2.35/1.00      inference(predicate_to_equality,[status(thm)],[c_207]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_3227,plain,
% 2.35/1.00      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 2.35/1.00      | r2_hidden(X0,sK3) = iProver_top ),
% 2.35/1.00      inference(superposition,[status(thm)],[c_2627,c_1471]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_3320,plain,
% 2.35/1.00      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 2.35/1.00      | r2_hidden(sK2(sK6,X1,X0),sK3) = iProver_top
% 2.35/1.00      | v1_relat_1(sK6) != iProver_top ),
% 2.35/1.00      inference(superposition,[status(thm)],[c_1468,c_3227]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_3648,plain,
% 2.35/1.00      ( r2_hidden(sK2(sK6,X1,X0),sK3) = iProver_top
% 2.35/1.00      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
% 2.35/1.00      inference(global_propositional_subsumption,
% 2.35/1.00                [status(thm)],
% 2.35/1.00                [c_3320,c_22,c_1628,c_1717,c_1738]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_3649,plain,
% 2.35/1.00      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 2.35/1.00      | r2_hidden(sK2(sK6,X1,X0),sK3) = iProver_top ),
% 2.35/1.00      inference(renaming,[status(thm)],[c_3648]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_16,plain,
% 2.35/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/1.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.35/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_1475,plain,
% 2.35/1.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.35/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.35/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_1934,plain,
% 2.35/1.00      ( k7_relset_1(sK3,sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
% 2.35/1.00      inference(superposition,[status(thm)],[c_1472,c_1475]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_18,negated_conjecture,
% 2.35/1.00      ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
% 2.35/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_1473,plain,
% 2.35/1.00      ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
% 2.35/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_2031,plain,
% 2.35/1.00      ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) = iProver_top ),
% 2.35/1.00      inference(demodulation,[status(thm)],[c_1934,c_1473]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_12,plain,
% 2.35/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.35/1.00      | ~ v1_funct_1(X1)
% 2.35/1.00      | ~ v1_relat_1(X1)
% 2.35/1.00      | k1_funct_1(X1,sK2(X1,X2,X0)) = X0 ),
% 2.35/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_512,plain,
% 2.35/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.35/1.00      | ~ v1_relat_1(X1)
% 2.35/1.00      | k1_funct_1(X1,sK2(X1,X2,X0)) = X0
% 2.35/1.00      | sK6 != X1 ),
% 2.35/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_513,plain,
% 2.35/1.00      ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
% 2.35/1.00      | ~ v1_relat_1(sK6)
% 2.35/1.00      | k1_funct_1(sK6,sK2(sK6,X1,X0)) = X0 ),
% 2.35/1.00      inference(unflattening,[status(thm)],[c_512]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_1466,plain,
% 2.35/1.00      ( k1_funct_1(sK6,sK2(sK6,X0,X1)) = X1
% 2.35/1.00      | r2_hidden(X1,k9_relat_1(sK6,X0)) != iProver_top
% 2.35/1.00      | v1_relat_1(sK6) != iProver_top ),
% 2.35/1.00      inference(predicate_to_equality,[status(thm)],[c_513]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_2035,plain,
% 2.35/1.00      ( k1_funct_1(sK6,sK2(sK6,sK5,sK7)) = sK7
% 2.35/1.00      | v1_relat_1(sK6) != iProver_top ),
% 2.35/1.00      inference(superposition,[status(thm)],[c_2031,c_1466]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_2323,plain,
% 2.35/1.00      ( k1_funct_1(sK6,sK2(sK6,sK5,sK7)) = sK7 ),
% 2.35/1.00      inference(global_propositional_subsumption,
% 2.35/1.00                [status(thm)],
% 2.35/1.00                [c_2035,c_22,c_1628,c_1717,c_1738]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_17,negated_conjecture,
% 2.35/1.00      ( ~ r2_hidden(X0,sK3)
% 2.35/1.00      | ~ r2_hidden(X0,sK5)
% 2.35/1.00      | k1_funct_1(sK6,X0) != sK7 ),
% 2.35/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_1474,plain,
% 2.35/1.00      ( k1_funct_1(sK6,X0) != sK7
% 2.35/1.00      | r2_hidden(X0,sK3) != iProver_top
% 2.35/1.00      | r2_hidden(X0,sK5) != iProver_top ),
% 2.35/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_2327,plain,
% 2.35/1.00      ( r2_hidden(sK2(sK6,sK5,sK7),sK3) != iProver_top
% 2.35/1.00      | r2_hidden(sK2(sK6,sK5,sK7),sK5) != iProver_top ),
% 2.35/1.00      inference(superposition,[status(thm)],[c_2323,c_1474]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_3657,plain,
% 2.35/1.00      ( r2_hidden(sK2(sK6,sK5,sK7),sK5) != iProver_top
% 2.35/1.00      | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top ),
% 2.35/1.00      inference(superposition,[status(thm)],[c_3649,c_2327]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_3675,plain,
% 2.35/1.00      ( r2_hidden(sK2(sK6,sK5,sK7),sK5) != iProver_top ),
% 2.35/1.00      inference(global_propositional_subsumption,
% 2.35/1.00                [status(thm)],
% 2.35/1.00                [c_3657,c_2031]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(c_3680,plain,
% 2.35/1.00      ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
% 2.35/1.00      | v1_relat_1(sK6) != iProver_top ),
% 2.35/1.00      inference(superposition,[status(thm)],[c_1467,c_3675]) ).
% 2.35/1.00  
% 2.35/1.00  cnf(contradiction,plain,
% 2.35/1.00      ( $false ),
% 2.35/1.00      inference(minisat,
% 2.35/1.00                [status(thm)],
% 2.35/1.00                [c_3680,c_2031,c_1738,c_1717,c_1628,c_22]) ).
% 2.35/1.00  
% 2.35/1.00  
% 2.35/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.35/1.00  
% 2.35/1.00  ------                               Statistics
% 2.35/1.00  
% 2.35/1.00  ------ General
% 2.35/1.00  
% 2.35/1.00  abstr_ref_over_cycles:                  0
% 2.35/1.00  abstr_ref_under_cycles:                 0
% 2.35/1.00  gc_basic_clause_elim:                   0
% 2.35/1.00  forced_gc_time:                         0
% 2.35/1.00  parsing_time:                           0.008
% 2.35/1.00  unif_index_cands_time:                  0.
% 2.35/1.00  unif_index_add_time:                    0.
% 2.35/1.00  orderings_time:                         0.
% 2.35/1.00  out_proof_time:                         0.009
% 2.35/1.00  total_time:                             0.136
% 2.35/1.00  num_of_symbols:                         51
% 2.35/1.00  num_of_terms:                           3306
% 2.35/1.00  
% 2.35/1.00  ------ Preprocessing
% 2.35/1.00  
% 2.35/1.00  num_of_splits:                          0
% 2.35/1.00  num_of_split_atoms:                     0
% 2.35/1.00  num_of_reused_defs:                     0
% 2.35/1.00  num_eq_ax_congr_red:                    31
% 2.35/1.00  num_of_sem_filtered_clauses:            1
% 2.35/1.00  num_of_subtypes:                        0
% 2.35/1.00  monotx_restored_types:                  0
% 2.35/1.00  sat_num_of_epr_types:                   0
% 2.35/1.00  sat_num_of_non_cyclic_types:            0
% 2.35/1.00  sat_guarded_non_collapsed_types:        0
% 2.35/1.00  num_pure_diseq_elim:                    0
% 2.35/1.00  simp_replaced_by:                       0
% 2.35/1.00  res_preprocessed:                       106
% 2.35/1.00  prep_upred:                             0
% 2.35/1.00  prep_unflattend:                        30
% 2.35/1.00  smt_new_axioms:                         0
% 2.35/1.00  pred_elim_cands:                        4
% 2.35/1.00  pred_elim:                              2
% 2.35/1.00  pred_elim_cl:                           3
% 2.35/1.00  pred_elim_cycles:                       7
% 2.35/1.00  merged_defs:                            8
% 2.35/1.00  merged_defs_ncl:                        0
% 2.35/1.00  bin_hyper_res:                          10
% 2.35/1.00  prep_cycles:                            4
% 2.35/1.00  pred_elim_time:                         0.009
% 2.35/1.00  splitting_time:                         0.
% 2.35/1.00  sem_filter_time:                        0.
% 2.35/1.00  monotx_time:                            0.
% 2.35/1.00  subtype_inf_time:                       0.
% 2.35/1.00  
% 2.35/1.00  ------ Problem properties
% 2.35/1.00  
% 2.35/1.00  clauses:                                18
% 2.35/1.00  conjectures:                            3
% 2.35/1.00  epr:                                    2
% 2.35/1.00  horn:                                   15
% 2.35/1.00  ground:                                 2
% 2.35/1.00  unary:                                  3
% 2.35/1.00  binary:                                 3
% 2.35/1.00  lits:                                   52
% 2.35/1.00  lits_eq:                                9
% 2.35/1.00  fd_pure:                                0
% 2.35/1.00  fd_pseudo:                              0
% 2.35/1.00  fd_cond:                                0
% 2.35/1.00  fd_pseudo_cond:                         4
% 2.35/1.00  ac_symbols:                             0
% 2.35/1.00  
% 2.35/1.00  ------ Propositional Solver
% 2.35/1.00  
% 2.35/1.00  prop_solver_calls:                      29
% 2.35/1.00  prop_fast_solver_calls:                 836
% 2.35/1.00  smt_solver_calls:                       0
% 2.35/1.00  smt_fast_solver_calls:                  0
% 2.35/1.00  prop_num_of_clauses:                    1186
% 2.35/1.00  prop_preprocess_simplified:             4349
% 2.35/1.00  prop_fo_subsumed:                       16
% 2.35/1.00  prop_solver_time:                       0.
% 2.35/1.00  smt_solver_time:                        0.
% 2.35/1.00  smt_fast_solver_time:                   0.
% 2.35/1.00  prop_fast_solver_time:                  0.
% 2.35/1.00  prop_unsat_core_time:                   0.
% 2.35/1.00  
% 2.35/1.00  ------ QBF
% 2.35/1.00  
% 2.35/1.00  qbf_q_res:                              0
% 2.35/1.00  qbf_num_tautologies:                    0
% 2.35/1.00  qbf_prep_cycles:                        0
% 2.35/1.00  
% 2.35/1.00  ------ BMC1
% 2.35/1.00  
% 2.35/1.00  bmc1_current_bound:                     -1
% 2.35/1.00  bmc1_last_solved_bound:                 -1
% 2.35/1.00  bmc1_unsat_core_size:                   -1
% 2.35/1.00  bmc1_unsat_core_parents_size:           -1
% 2.35/1.00  bmc1_merge_next_fun:                    0
% 2.35/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.35/1.00  
% 2.35/1.00  ------ Instantiation
% 2.35/1.00  
% 2.35/1.00  inst_num_of_clauses:                    319
% 2.35/1.00  inst_num_in_passive:                    150
% 2.35/1.00  inst_num_in_active:                     158
% 2.35/1.00  inst_num_in_unprocessed:                11
% 2.35/1.00  inst_num_of_loops:                      200
% 2.35/1.00  inst_num_of_learning_restarts:          0
% 2.35/1.00  inst_num_moves_active_passive:          38
% 2.35/1.00  inst_lit_activity:                      0
% 2.35/1.00  inst_lit_activity_moves:                0
% 2.35/1.00  inst_num_tautologies:                   0
% 2.35/1.00  inst_num_prop_implied:                  0
% 2.35/1.00  inst_num_existing_simplified:           0
% 2.35/1.00  inst_num_eq_res_simplified:             0
% 2.35/1.00  inst_num_child_elim:                    0
% 2.35/1.00  inst_num_of_dismatching_blockings:      63
% 2.35/1.00  inst_num_of_non_proper_insts:           263
% 2.35/1.00  inst_num_of_duplicates:                 0
% 2.35/1.00  inst_inst_num_from_inst_to_res:         0
% 2.35/1.00  inst_dismatching_checking_time:         0.
% 2.35/1.00  
% 2.35/1.00  ------ Resolution
% 2.35/1.00  
% 2.35/1.00  res_num_of_clauses:                     0
% 2.35/1.00  res_num_in_passive:                     0
% 2.35/1.00  res_num_in_active:                      0
% 2.35/1.00  res_num_of_loops:                       110
% 2.35/1.00  res_forward_subset_subsumed:            10
% 2.35/1.00  res_backward_subset_subsumed:           2
% 2.35/1.00  res_forward_subsumed:                   0
% 2.35/1.00  res_backward_subsumed:                  0
% 2.35/1.00  res_forward_subsumption_resolution:     0
% 2.35/1.00  res_backward_subsumption_resolution:    0
% 2.35/1.00  res_clause_to_clause_subsumption:       126
% 2.35/1.00  res_orphan_elimination:                 0
% 2.35/1.00  res_tautology_del:                      43
% 2.35/1.00  res_num_eq_res_simplified:              0
% 2.35/1.00  res_num_sel_changes:                    0
% 2.35/1.00  res_moves_from_active_to_pass:          0
% 2.35/1.00  
% 2.35/1.00  ------ Superposition
% 2.35/1.00  
% 2.35/1.00  sup_time_total:                         0.
% 2.35/1.00  sup_time_generating:                    0.
% 2.35/1.00  sup_time_sim_full:                      0.
% 2.35/1.00  sup_time_sim_immed:                     0.
% 2.35/1.00  
% 2.35/1.00  sup_num_of_clauses:                     66
% 2.35/1.00  sup_num_in_active:                      39
% 2.35/1.00  sup_num_in_passive:                     27
% 2.35/1.00  sup_num_of_loops:                       39
% 2.35/1.00  sup_fw_superposition:                   35
% 2.35/1.00  sup_bw_superposition:                   20
% 2.35/1.00  sup_immediate_simplified:               4
% 2.35/1.00  sup_given_eliminated:                   0
% 2.35/1.00  comparisons_done:                       0
% 2.35/1.00  comparisons_avoided:                    2
% 2.35/1.00  
% 2.35/1.00  ------ Simplifications
% 2.35/1.00  
% 2.35/1.00  
% 2.35/1.00  sim_fw_subset_subsumed:                 0
% 2.35/1.00  sim_bw_subset_subsumed:                 0
% 2.35/1.00  sim_fw_subsumed:                        0
% 2.35/1.00  sim_bw_subsumed:                        4
% 2.35/1.00  sim_fw_subsumption_res:                 0
% 2.35/1.00  sim_bw_subsumption_res:                 0
% 2.35/1.00  sim_tautology_del:                      2
% 2.35/1.00  sim_eq_tautology_del:                   0
% 2.35/1.00  sim_eq_res_simp:                        0
% 2.35/1.00  sim_fw_demodulated:                     0
% 2.35/1.00  sim_bw_demodulated:                     1
% 2.35/1.00  sim_light_normalised:                   0
% 2.35/1.00  sim_joinable_taut:                      0
% 2.35/1.00  sim_joinable_simp:                      0
% 2.35/1.00  sim_ac_normalised:                      0
% 2.35/1.00  sim_smt_subsumption:                    0
% 2.35/1.00  
%------------------------------------------------------------------------------
