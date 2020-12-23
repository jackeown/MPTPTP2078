%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:57:08 EST 2020

% Result     : Theorem 15.54s
% Output     : CNFRefutation 15.54s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 568 expanded)
%              Number of clauses        :   57 ( 176 expanded)
%              Number of leaves         :   11 ( 136 expanded)
%              Depth                    :   19
%              Number of atoms          :  370 (2791 expanded)
%              Number of equality atoms :  117 ( 543 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( r2_relset_1(X0,X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,X0)
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r2_hidden(k4_tarski(X4,X5),X2)
                    <=> r2_hidden(k4_tarski(X4,X5),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_relset_1(X0,X1,X2,X3)
          <=> ! [X4] :
                ( ! [X5] :
                    ( ( r2_hidden(k4_tarski(X4,X5),X2)
                    <=> r2_hidden(k4_tarski(X4,X5),X3) )
                    | ~ m1_subset_1(X5,X1) )
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_relset_1(X0,X1,X2,X3)
              | ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
                        | ~ r2_hidden(k4_tarski(X4,X5),X2) )
                      & ( r2_hidden(k4_tarski(X4,X5),X3)
                        | r2_hidden(k4_tarski(X4,X5),X2) )
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( ( ( r2_hidden(k4_tarski(X4,X5),X2)
                          | ~ r2_hidden(k4_tarski(X4,X5),X3) )
                        & ( r2_hidden(k4_tarski(X4,X5),X3)
                          | ~ r2_hidden(k4_tarski(X4,X5),X2) ) )
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,X0) )
              | ~ r2_relset_1(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_relset_1(X0,X1,X2,X3)
              | ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
                        | ~ r2_hidden(k4_tarski(X4,X5),X2) )
                      & ( r2_hidden(k4_tarski(X4,X5),X3)
                        | r2_hidden(k4_tarski(X4,X5),X2) )
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( ( ( r2_hidden(k4_tarski(X4,X5),X2)
                          | ~ r2_hidden(k4_tarski(X4,X5),X3) )
                        & ( r2_hidden(k4_tarski(X4,X5),X3)
                          | ~ r2_hidden(k4_tarski(X4,X5),X2) ) )
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,X0) )
              | ~ r2_relset_1(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f18])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_relset_1(X0,X1,X2,X3)
              | ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
                        | ~ r2_hidden(k4_tarski(X4,X5),X2) )
                      & ( r2_hidden(k4_tarski(X4,X5),X3)
                        | r2_hidden(k4_tarski(X4,X5),X2) )
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X6] :
                  ( ! [X7] :
                      ( ( ( r2_hidden(k4_tarski(X6,X7),X2)
                          | ~ r2_hidden(k4_tarski(X6,X7),X3) )
                        & ( r2_hidden(k4_tarski(X6,X7),X3)
                          | ~ r2_hidden(k4_tarski(X6,X7),X2) ) )
                      | ~ m1_subset_1(X7,X1) )
                  | ~ m1_subset_1(X6,X0) )
              | ~ r2_relset_1(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f19])).

fof(f22,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
            | ~ r2_hidden(k4_tarski(X4,X5),X2) )
          & ( r2_hidden(k4_tarski(X4,X5),X3)
            | r2_hidden(k4_tarski(X4,X5),X2) )
          & m1_subset_1(X5,X1) )
     => ( ( ~ r2_hidden(k4_tarski(X4,sK1(X0,X1,X2,X3)),X3)
          | ~ r2_hidden(k4_tarski(X4,sK1(X0,X1,X2,X3)),X2) )
        & ( r2_hidden(k4_tarski(X4,sK1(X0,X1,X2,X3)),X3)
          | r2_hidden(k4_tarski(X4,sK1(X0,X1,X2,X3)),X2) )
        & m1_subset_1(sK1(X0,X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
                | ~ r2_hidden(k4_tarski(X4,X5),X2) )
              & ( r2_hidden(k4_tarski(X4,X5),X3)
                | r2_hidden(k4_tarski(X4,X5),X2) )
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,X0) )
     => ( ? [X5] :
            ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),X5),X3)
              | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),X5),X2) )
            & ( r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),X5),X3)
              | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),X5),X2) )
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK0(X0,X1,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_relset_1(X0,X1,X2,X3)
              | ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3)
                  | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2) )
                & ( r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3)
                  | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2) )
                & m1_subset_1(sK1(X0,X1,X2,X3),X1)
                & m1_subset_1(sK0(X0,X1,X2,X3),X0) ) )
            & ( ! [X6] :
                  ( ! [X7] :
                      ( ( ( r2_hidden(k4_tarski(X6,X7),X2)
                          | ~ r2_hidden(k4_tarski(X6,X7),X3) )
                        & ( r2_hidden(k4_tarski(X6,X7),X3)
                          | ~ r2_hidden(k4_tarski(X6,X7),X2) ) )
                      | ~ m1_subset_1(X7,X1) )
                  | ~ m1_subset_1(X6,X0) )
              | ~ r2_relset_1(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22,f21])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3)
      | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
         => ( ! [X3] :
                ( r2_hidden(X3,X0)
               => k11_relat_1(X1,X3) = k11_relat_1(X2,X3) )
           => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
           => ( ! [X3] :
                  ( r2_hidden(X3,X0)
                 => k11_relat_1(X1,X3) = k11_relat_1(X2,X3) )
             => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & ! [X3] :
              ( k11_relat_1(X1,X3) = k11_relat_1(X2,X3)
              | ~ r2_hidden(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & ! [X3] :
              ( k11_relat_1(X1,X3) = k11_relat_1(X2,X3)
              | ~ r2_hidden(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f13])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & ! [X3] :
              ( k11_relat_1(X1,X3) = k11_relat_1(X2,X3)
              | ~ r2_hidden(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
     => ( ~ r2_relset_1(X0,X0,X1,sK4)
        & ! [X3] :
            ( k11_relat_1(sK4,X3) = k11_relat_1(X1,X3)
            | ~ r2_hidden(X3,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X1,X2)
            & ! [X3] :
                ( k11_relat_1(X1,X3) = k11_relat_1(X2,X3)
                | ~ r2_hidden(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK2,sK2,sK3,X2)
          & ! [X3] :
              ( k11_relat_1(sK3,X3) = k11_relat_1(X2,X3)
              | ~ r2_hidden(X3,sK2) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ~ r2_relset_1(sK2,sK2,sK3,sK4)
    & ! [X3] :
        ( k11_relat_1(sK3,X3) = k11_relat_1(sK4,X3)
        | ~ r2_hidden(X3,sK2) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f14,f25,f24])).

fof(f42,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f15])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f26])).

fof(f43,plain,(
    ! [X3] :
      ( k11_relat_1(sK3,X3) = k11_relat_1(sK4,X3)
      | ~ r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,(
    ~ r2_relset_1(sK2,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3)
      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_9,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_877,plain,
    ( r2_relset_1(X0,X1,X2,X3) = iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) = iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_879,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1658,plain,
    ( r2_relset_1(X0,X1,X2,X3) = iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X2,sK0(X0,X1,X2,X3))) = iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_877,c_879])).

cnf(c_8604,plain,
    ( r2_relset_1(X0,X1,X2,X3) = iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X2,sK0(X0,X1,X2,X3))) = iProver_top
    | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X3,sK0(X0,X1,X2,X3))) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1658,c_879])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_870,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_883,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1237,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK2,sK2)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_870,c_883])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_884,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1883,plain,
    ( r2_hidden(X0,sK2) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_884])).

cnf(c_2110,plain,
    ( r2_relset_1(X0,X1,X2,sK4) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK0(X0,X1,X2,sK4),sK2) = iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X1,X2,sK4),sK1(X0,X1,X2,sK4)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_877,c_1883])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_869,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1238,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK2,sK2)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_869,c_883])).

cnf(c_1979,plain,
    ( r2_hidden(X0,sK2) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1238,c_884])).

cnf(c_6178,plain,
    ( r2_relset_1(X0,X1,sK3,sK4) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK0(X0,X1,sK3,sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2110,c_1979])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | k11_relat_1(sK3,X0) = k11_relat_1(sK4,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_871,plain,
    ( k11_relat_1(sK3,X0) = k11_relat_1(sK4,X0)
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_44376,plain,
    ( k11_relat_1(sK4,sK0(X0,X1,sK3,sK4)) = k11_relat_1(sK3,sK0(X0,X1,sK3,sK4))
    | r2_relset_1(X0,X1,sK3,sK4) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6178,c_871])).

cnf(c_44381,plain,
    ( k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))
    | r2_relset_1(sK2,sK2,sK3,sK4) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_870,c_44376])).

cnf(c_18,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_19,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14,negated_conjecture,
    ( ~ r2_relset_1(sK2,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_23,plain,
    ( r2_relset_1(sK2,sK2,sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3830,plain,
    ( ~ r2_hidden(sK0(sK2,sK2,sK3,sK4),sK2)
    | k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3833,plain,
    ( k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))
    | r2_hidden(sK0(sK2,sK2,sK3,sK4),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3830])).

cnf(c_6198,plain,
    ( r2_relset_1(sK2,sK2,sK3,sK4) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | r2_hidden(sK0(sK2,sK2,sK3,sK4),sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6178])).

cnf(c_44541,plain,
    ( k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_44381,c_18,c_19,c_23,c_3833,c_6198])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_880,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_44543,plain,
    ( r2_hidden(X0,k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4))) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),X0),sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_44541,c_880])).

cnf(c_5,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_44,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_46,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_973,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK2))
    | v1_relat_1(sK4) ),
    inference(resolution,[status(thm)],[c_4,c_16])).

cnf(c_974,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_973])).

cnf(c_44749,plain,
    ( r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),X0),sK4) = iProver_top
    | r2_hidden(X0,k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_44543,c_46,c_974])).

cnf(c_44750,plain,
    ( r2_hidden(X0,k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4))) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),X0),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_44749])).

cnf(c_44763,plain,
    ( r2_relset_1(sK2,sK2,sK3,sK4) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))) = iProver_top
    | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8604,c_44750])).

cnf(c_44617,plain,
    ( r2_relset_1(sK2,sK2,sK3,sK4) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4))) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_44541,c_8604])).

cnf(c_2188,plain,
    ( ~ r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)))
    | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2189,plain,
    ( r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4))) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2188])).

cnf(c_1366,plain,
    ( ~ r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4)))
    | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1367,plain,
    ( r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1366])).

cnf(c_975,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK2))
    | v1_relat_1(sK3) ),
    inference(resolution,[status(thm)],[c_4,c_17])).

cnf(c_976,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_975])).

cnf(c_8,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3)
    | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_436,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(k4_tarski(sK0(X1,X2,X3,X0),sK1(X1,X2,X3,X0)),X0)
    | ~ r2_hidden(k4_tarski(sK0(X1,X2,X3,X0),sK1(X1,X2,X3,X0)),X3)
    | sK4 != X0
    | sK3 != X3
    | sK2 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_14])).

cnf(c_437,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4)
    | ~ r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK3) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_439,plain,
    ( ~ r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4)
    | ~ r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_437,c_17,c_16])).

cnf(c_441,plain,
    ( r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_439])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_44763,c_44617,c_2189,c_1367,c_976,c_974,c_441,c_46,c_23,c_19,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:17:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.54/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.54/2.49  
% 15.54/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.54/2.49  
% 15.54/2.49  ------  iProver source info
% 15.54/2.49  
% 15.54/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.54/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.54/2.49  git: non_committed_changes: false
% 15.54/2.49  git: last_make_outside_of_git: false
% 15.54/2.49  
% 15.54/2.49  ------ 
% 15.54/2.49  ------ Parsing...
% 15.54/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.54/2.49  
% 15.54/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.54/2.49  
% 15.54/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.54/2.49  
% 15.54/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.54/2.49  ------ Proving...
% 15.54/2.49  ------ Problem Properties 
% 15.54/2.49  
% 15.54/2.49  
% 15.54/2.49  clauses                                 18
% 15.54/2.49  conjectures                             4
% 15.54/2.49  EPR                                     1
% 15.54/2.49  Horn                                    15
% 15.54/2.49  unary                                   4
% 15.54/2.49  binary                                  3
% 15.54/2.49  lits                                    57
% 15.54/2.49  lits eq                                 1
% 15.54/2.49  fd_pure                                 0
% 15.54/2.49  fd_pseudo                               0
% 15.54/2.49  fd_cond                                 0
% 15.54/2.49  fd_pseudo_cond                          0
% 15.54/2.49  AC symbols                              0
% 15.54/2.49  
% 15.54/2.49  ------ Input Options Time Limit: Unbounded
% 15.54/2.49  
% 15.54/2.49  
% 15.54/2.49  ------ 
% 15.54/2.49  Current options:
% 15.54/2.49  ------ 
% 15.54/2.49  
% 15.54/2.49  
% 15.54/2.49  
% 15.54/2.49  
% 15.54/2.49  ------ Proving...
% 15.54/2.49  
% 15.54/2.49  
% 15.54/2.49  % SZS status Theorem for theBenchmark.p
% 15.54/2.49  
% 15.54/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.54/2.49  
% 15.54/2.49  fof(f6,axiom,(
% 15.54/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => (r2_hidden(k4_tarski(X4,X5),X2) <=> r2_hidden(k4_tarski(X4,X5),X3)))))))),
% 15.54/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.54/2.49  
% 15.54/2.49  fof(f12,plain,(
% 15.54/2.49    ! [X0,X1,X2] : (! [X3] : ((r2_relset_1(X0,X1,X2,X3) <=> ! [X4] : (! [X5] : ((r2_hidden(k4_tarski(X4,X5),X2) <=> r2_hidden(k4_tarski(X4,X5),X3)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.54/2.49    inference(ennf_transformation,[],[f6])).
% 15.54/2.49  
% 15.54/2.49  fof(f18,plain,(
% 15.54/2.49    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (? [X5] : (((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2))) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X4] : (! [X5] : (((r2_hidden(k4_tarski(X4,X5),X2) | ~r2_hidden(k4_tarski(X4,X5),X3)) & (r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2))) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.54/2.49    inference(nnf_transformation,[],[f12])).
% 15.54/2.49  
% 15.54/2.49  fof(f19,plain,(
% 15.54/2.49    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X4] : (! [X5] : (((r2_hidden(k4_tarski(X4,X5),X2) | ~r2_hidden(k4_tarski(X4,X5),X3)) & (r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2))) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.54/2.49    inference(flattening,[],[f18])).
% 15.54/2.49  
% 15.54/2.49  fof(f20,plain,(
% 15.54/2.49    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X6] : (! [X7] : (((r2_hidden(k4_tarski(X6,X7),X2) | ~r2_hidden(k4_tarski(X6,X7),X3)) & (r2_hidden(k4_tarski(X6,X7),X3) | ~r2_hidden(k4_tarski(X6,X7),X2))) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.54/2.49    inference(rectify,[],[f19])).
% 15.54/2.49  
% 15.54/2.49  fof(f22,plain,(
% 15.54/2.49    ( ! [X4] : (! [X3,X2,X1,X0] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) => ((~r2_hidden(k4_tarski(X4,sK1(X0,X1,X2,X3)),X3) | ~r2_hidden(k4_tarski(X4,sK1(X0,X1,X2,X3)),X2)) & (r2_hidden(k4_tarski(X4,sK1(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(X4,sK1(X0,X1,X2,X3)),X2)) & m1_subset_1(sK1(X0,X1,X2,X3),X1)))) )),
% 15.54/2.49    introduced(choice_axiom,[])).
% 15.54/2.49  
% 15.54/2.49  fof(f21,plain,(
% 15.54/2.49    ! [X3,X2,X1,X0] : (? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) => (? [X5] : ((~r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),X5),X3) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),X5),X2)) & (r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),X5),X3) | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(sK0(X0,X1,X2,X3),X0)))),
% 15.54/2.49    introduced(choice_axiom,[])).
% 15.54/2.49  
% 15.54/2.49  fof(f23,plain,(
% 15.54/2.49    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | (((~r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2)) & (r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2)) & m1_subset_1(sK1(X0,X1,X2,X3),X1)) & m1_subset_1(sK0(X0,X1,X2,X3),X0))) & (! [X6] : (! [X7] : (((r2_hidden(k4_tarski(X6,X7),X2) | ~r2_hidden(k4_tarski(X6,X7),X3)) & (r2_hidden(k4_tarski(X6,X7),X3) | ~r2_hidden(k4_tarski(X6,X7),X2))) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.54/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22,f21])).
% 15.54/2.49  
% 15.54/2.49  fof(f39,plain,(
% 15.54/2.49    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.54/2.49    inference(cnf_transformation,[],[f23])).
% 15.54/2.49  
% 15.54/2.49  fof(f5,axiom,(
% 15.54/2.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 15.54/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.54/2.49  
% 15.54/2.49  fof(f11,plain,(
% 15.54/2.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 15.54/2.49    inference(ennf_transformation,[],[f5])).
% 15.54/2.49  
% 15.54/2.49  fof(f17,plain,(
% 15.54/2.49    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 15.54/2.49    inference(nnf_transformation,[],[f11])).
% 15.54/2.49  
% 15.54/2.49  fof(f33,plain,(
% 15.54/2.49    ( ! [X2,X0,X1] : (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 15.54/2.49    inference(cnf_transformation,[],[f17])).
% 15.54/2.49  
% 15.54/2.49  fof(f7,conjecture,(
% 15.54/2.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (! [X3] : (r2_hidden(X3,X0) => k11_relat_1(X1,X3) = k11_relat_1(X2,X3)) => r2_relset_1(X0,X0,X1,X2))))),
% 15.54/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.54/2.49  
% 15.54/2.49  fof(f8,negated_conjecture,(
% 15.54/2.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (! [X3] : (r2_hidden(X3,X0) => k11_relat_1(X1,X3) = k11_relat_1(X2,X3)) => r2_relset_1(X0,X0,X1,X2))))),
% 15.54/2.49    inference(negated_conjecture,[],[f7])).
% 15.54/2.49  
% 15.54/2.49  fof(f13,plain,(
% 15.54/2.49    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X1,X2) & ! [X3] : (k11_relat_1(X1,X3) = k11_relat_1(X2,X3) | ~r2_hidden(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 15.54/2.49    inference(ennf_transformation,[],[f8])).
% 15.54/2.49  
% 15.54/2.49  fof(f14,plain,(
% 15.54/2.49    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X1,X2) & ! [X3] : (k11_relat_1(X1,X3) = k11_relat_1(X2,X3) | ~r2_hidden(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 15.54/2.49    inference(flattening,[],[f13])).
% 15.54/2.49  
% 15.54/2.49  fof(f25,plain,(
% 15.54/2.49    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X1,X2) & ! [X3] : (k11_relat_1(X1,X3) = k11_relat_1(X2,X3) | ~r2_hidden(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) => (~r2_relset_1(X0,X0,X1,sK4) & ! [X3] : (k11_relat_1(sK4,X3) = k11_relat_1(X1,X3) | ~r2_hidden(X3,X0)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))) )),
% 15.54/2.49    introduced(choice_axiom,[])).
% 15.54/2.49  
% 15.54/2.49  fof(f24,plain,(
% 15.54/2.49    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X1,X2) & ! [X3] : (k11_relat_1(X1,X3) = k11_relat_1(X2,X3) | ~r2_hidden(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) => (? [X2] : (~r2_relset_1(sK2,sK2,sK3,X2) & ! [X3] : (k11_relat_1(sK3,X3) = k11_relat_1(X2,X3) | ~r2_hidden(X3,sK2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))))),
% 15.54/2.49    introduced(choice_axiom,[])).
% 15.54/2.49  
% 15.54/2.49  fof(f26,plain,(
% 15.54/2.49    (~r2_relset_1(sK2,sK2,sK3,sK4) & ! [X3] : (k11_relat_1(sK3,X3) = k11_relat_1(sK4,X3) | ~r2_hidden(X3,sK2)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 15.54/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f14,f25,f24])).
% 15.54/2.49  
% 15.54/2.49  fof(f42,plain,(
% 15.54/2.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 15.54/2.49    inference(cnf_transformation,[],[f26])).
% 15.54/2.49  
% 15.54/2.49  fof(f2,axiom,(
% 15.54/2.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 15.54/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.54/2.49  
% 15.54/2.49  fof(f9,plain,(
% 15.54/2.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.54/2.49    inference(ennf_transformation,[],[f2])).
% 15.54/2.49  
% 15.54/2.49  fof(f30,plain,(
% 15.54/2.49    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.54/2.49    inference(cnf_transformation,[],[f9])).
% 15.54/2.49  
% 15.54/2.49  fof(f1,axiom,(
% 15.54/2.49    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 15.54/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.54/2.49  
% 15.54/2.49  fof(f15,plain,(
% 15.54/2.49    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 15.54/2.49    inference(nnf_transformation,[],[f1])).
% 15.54/2.49  
% 15.54/2.49  fof(f16,plain,(
% 15.54/2.49    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 15.54/2.49    inference(flattening,[],[f15])).
% 15.54/2.49  
% 15.54/2.49  fof(f27,plain,(
% 15.54/2.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 15.54/2.49    inference(cnf_transformation,[],[f16])).
% 15.54/2.49  
% 15.54/2.49  fof(f41,plain,(
% 15.54/2.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 15.54/2.49    inference(cnf_transformation,[],[f26])).
% 15.54/2.49  
% 15.54/2.49  fof(f43,plain,(
% 15.54/2.49    ( ! [X3] : (k11_relat_1(sK3,X3) = k11_relat_1(sK4,X3) | ~r2_hidden(X3,sK2)) )),
% 15.54/2.49    inference(cnf_transformation,[],[f26])).
% 15.54/2.49  
% 15.54/2.49  fof(f44,plain,(
% 15.54/2.49    ~r2_relset_1(sK2,sK2,sK3,sK4)),
% 15.54/2.49    inference(cnf_transformation,[],[f26])).
% 15.54/2.49  
% 15.54/2.49  fof(f34,plain,(
% 15.54/2.49    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 15.54/2.49    inference(cnf_transformation,[],[f17])).
% 15.54/2.49  
% 15.54/2.49  fof(f4,axiom,(
% 15.54/2.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 15.54/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.54/2.49  
% 15.54/2.49  fof(f32,plain,(
% 15.54/2.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 15.54/2.49    inference(cnf_transformation,[],[f4])).
% 15.54/2.49  
% 15.54/2.49  fof(f3,axiom,(
% 15.54/2.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 15.54/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.54/2.49  
% 15.54/2.49  fof(f10,plain,(
% 15.54/2.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 15.54/2.49    inference(ennf_transformation,[],[f3])).
% 15.54/2.49  
% 15.54/2.49  fof(f31,plain,(
% 15.54/2.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 15.54/2.49    inference(cnf_transformation,[],[f10])).
% 15.54/2.49  
% 15.54/2.49  fof(f40,plain,(
% 15.54/2.49    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.54/2.49    inference(cnf_transformation,[],[f23])).
% 15.54/2.49  
% 15.54/2.49  cnf(c_9,plain,
% 15.54/2.49      ( r2_relset_1(X0,X1,X2,X3)
% 15.54/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.54/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.54/2.49      | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3)
% 15.54/2.49      | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2) ),
% 15.54/2.49      inference(cnf_transformation,[],[f39]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_877,plain,
% 15.54/2.49      ( r2_relset_1(X0,X1,X2,X3) = iProver_top
% 15.54/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.54/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.54/2.49      | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) = iProver_top
% 15.54/2.49      | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2) = iProver_top ),
% 15.54/2.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_7,plain,
% 15.54/2.49      ( r2_hidden(X0,k11_relat_1(X1,X2))
% 15.54/2.49      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 15.54/2.49      | ~ v1_relat_1(X1) ),
% 15.54/2.49      inference(cnf_transformation,[],[f33]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_879,plain,
% 15.54/2.49      ( r2_hidden(X0,k11_relat_1(X1,X2)) = iProver_top
% 15.54/2.49      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
% 15.54/2.49      | v1_relat_1(X1) != iProver_top ),
% 15.54/2.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_1658,plain,
% 15.54/2.49      ( r2_relset_1(X0,X1,X2,X3) = iProver_top
% 15.54/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.54/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.54/2.49      | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X2,sK0(X0,X1,X2,X3))) = iProver_top
% 15.54/2.49      | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) = iProver_top
% 15.54/2.49      | v1_relat_1(X2) != iProver_top ),
% 15.54/2.49      inference(superposition,[status(thm)],[c_877,c_879]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_8604,plain,
% 15.54/2.49      ( r2_relset_1(X0,X1,X2,X3) = iProver_top
% 15.54/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.54/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.54/2.49      | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X2,sK0(X0,X1,X2,X3))) = iProver_top
% 15.54/2.49      | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X3,sK0(X0,X1,X2,X3))) = iProver_top
% 15.54/2.49      | v1_relat_1(X2) != iProver_top
% 15.54/2.49      | v1_relat_1(X3) != iProver_top ),
% 15.54/2.49      inference(superposition,[status(thm)],[c_1658,c_879]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_16,negated_conjecture,
% 15.54/2.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 15.54/2.49      inference(cnf_transformation,[],[f42]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_870,plain,
% 15.54/2.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 15.54/2.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_3,plain,
% 15.54/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.54/2.49      | ~ r2_hidden(X2,X0)
% 15.54/2.49      | r2_hidden(X2,X1) ),
% 15.54/2.49      inference(cnf_transformation,[],[f30]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_883,plain,
% 15.54/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.54/2.49      | r2_hidden(X2,X0) != iProver_top
% 15.54/2.49      | r2_hidden(X2,X1) = iProver_top ),
% 15.54/2.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_1237,plain,
% 15.54/2.49      ( r2_hidden(X0,k2_zfmisc_1(sK2,sK2)) = iProver_top
% 15.54/2.49      | r2_hidden(X0,sK4) != iProver_top ),
% 15.54/2.49      inference(superposition,[status(thm)],[c_870,c_883]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_2,plain,
% 15.54/2.49      ( r2_hidden(X0,X1)
% 15.54/2.49      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 15.54/2.49      inference(cnf_transformation,[],[f27]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_884,plain,
% 15.54/2.49      ( r2_hidden(X0,X1) = iProver_top
% 15.54/2.49      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
% 15.54/2.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_1883,plain,
% 15.54/2.49      ( r2_hidden(X0,sK2) = iProver_top
% 15.54/2.49      | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top ),
% 15.54/2.49      inference(superposition,[status(thm)],[c_1237,c_884]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_2110,plain,
% 15.54/2.49      ( r2_relset_1(X0,X1,X2,sK4) = iProver_top
% 15.54/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.54/2.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.54/2.49      | r2_hidden(sK0(X0,X1,X2,sK4),sK2) = iProver_top
% 15.54/2.49      | r2_hidden(k4_tarski(sK0(X0,X1,X2,sK4),sK1(X0,X1,X2,sK4)),X2) = iProver_top ),
% 15.54/2.49      inference(superposition,[status(thm)],[c_877,c_1883]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_17,negated_conjecture,
% 15.54/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 15.54/2.49      inference(cnf_transformation,[],[f41]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_869,plain,
% 15.54/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 15.54/2.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_1238,plain,
% 15.54/2.49      ( r2_hidden(X0,k2_zfmisc_1(sK2,sK2)) = iProver_top
% 15.54/2.49      | r2_hidden(X0,sK3) != iProver_top ),
% 15.54/2.49      inference(superposition,[status(thm)],[c_869,c_883]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_1979,plain,
% 15.54/2.49      ( r2_hidden(X0,sK2) = iProver_top
% 15.54/2.49      | r2_hidden(k4_tarski(X0,X1),sK3) != iProver_top ),
% 15.54/2.49      inference(superposition,[status(thm)],[c_1238,c_884]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_6178,plain,
% 15.54/2.49      ( r2_relset_1(X0,X1,sK3,sK4) = iProver_top
% 15.54/2.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.54/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.54/2.49      | r2_hidden(sK0(X0,X1,sK3,sK4),sK2) = iProver_top ),
% 15.54/2.49      inference(superposition,[status(thm)],[c_2110,c_1979]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_15,negated_conjecture,
% 15.54/2.49      ( ~ r2_hidden(X0,sK2) | k11_relat_1(sK3,X0) = k11_relat_1(sK4,X0) ),
% 15.54/2.49      inference(cnf_transformation,[],[f43]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_871,plain,
% 15.54/2.49      ( k11_relat_1(sK3,X0) = k11_relat_1(sK4,X0)
% 15.54/2.49      | r2_hidden(X0,sK2) != iProver_top ),
% 15.54/2.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_44376,plain,
% 15.54/2.49      ( k11_relat_1(sK4,sK0(X0,X1,sK3,sK4)) = k11_relat_1(sK3,sK0(X0,X1,sK3,sK4))
% 15.54/2.49      | r2_relset_1(X0,X1,sK3,sK4) = iProver_top
% 15.54/2.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.54/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.54/2.49      inference(superposition,[status(thm)],[c_6178,c_871]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_44381,plain,
% 15.54/2.49      ( k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))
% 15.54/2.49      | r2_relset_1(sK2,sK2,sK3,sK4) = iProver_top
% 15.54/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
% 15.54/2.49      inference(superposition,[status(thm)],[c_870,c_44376]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_18,plain,
% 15.54/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 15.54/2.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_19,plain,
% 15.54/2.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 15.54/2.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_14,negated_conjecture,
% 15.54/2.49      ( ~ r2_relset_1(sK2,sK2,sK3,sK4) ),
% 15.54/2.49      inference(cnf_transformation,[],[f44]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_23,plain,
% 15.54/2.49      ( r2_relset_1(sK2,sK2,sK3,sK4) != iProver_top ),
% 15.54/2.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_3830,plain,
% 15.54/2.49      ( ~ r2_hidden(sK0(sK2,sK2,sK3,sK4),sK2)
% 15.54/2.49      | k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4)) ),
% 15.54/2.49      inference(instantiation,[status(thm)],[c_15]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_3833,plain,
% 15.54/2.49      ( k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))
% 15.54/2.49      | r2_hidden(sK0(sK2,sK2,sK3,sK4),sK2) != iProver_top ),
% 15.54/2.49      inference(predicate_to_equality,[status(thm)],[c_3830]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_6198,plain,
% 15.54/2.49      ( r2_relset_1(sK2,sK2,sK3,sK4) = iProver_top
% 15.54/2.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 15.54/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 15.54/2.49      | r2_hidden(sK0(sK2,sK2,sK3,sK4),sK2) = iProver_top ),
% 15.54/2.49      inference(instantiation,[status(thm)],[c_6178]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_44541,plain,
% 15.54/2.49      ( k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4)) ),
% 15.54/2.49      inference(global_propositional_subsumption,
% 15.54/2.49                [status(thm)],
% 15.54/2.49                [c_44381,c_18,c_19,c_23,c_3833,c_6198]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_6,plain,
% 15.54/2.49      ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
% 15.54/2.49      | r2_hidden(k4_tarski(X2,X0),X1)
% 15.54/2.49      | ~ v1_relat_1(X1) ),
% 15.54/2.49      inference(cnf_transformation,[],[f34]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_880,plain,
% 15.54/2.49      ( r2_hidden(X0,k11_relat_1(X1,X2)) != iProver_top
% 15.54/2.49      | r2_hidden(k4_tarski(X2,X0),X1) = iProver_top
% 15.54/2.49      | v1_relat_1(X1) != iProver_top ),
% 15.54/2.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_44543,plain,
% 15.54/2.49      ( r2_hidden(X0,k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4))) != iProver_top
% 15.54/2.49      | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),X0),sK4) = iProver_top
% 15.54/2.49      | v1_relat_1(sK4) != iProver_top ),
% 15.54/2.49      inference(superposition,[status(thm)],[c_44541,c_880]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_5,plain,
% 15.54/2.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 15.54/2.49      inference(cnf_transformation,[],[f32]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_44,plain,
% 15.54/2.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 15.54/2.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_46,plain,
% 15.54/2.49      ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) = iProver_top ),
% 15.54/2.49      inference(instantiation,[status(thm)],[c_44]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_4,plain,
% 15.54/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.54/2.49      | ~ v1_relat_1(X1)
% 15.54/2.49      | v1_relat_1(X0) ),
% 15.54/2.49      inference(cnf_transformation,[],[f31]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_973,plain,
% 15.54/2.49      ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK2)) | v1_relat_1(sK4) ),
% 15.54/2.49      inference(resolution,[status(thm)],[c_4,c_16]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_974,plain,
% 15.54/2.49      ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) != iProver_top
% 15.54/2.49      | v1_relat_1(sK4) = iProver_top ),
% 15.54/2.49      inference(predicate_to_equality,[status(thm)],[c_973]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_44749,plain,
% 15.54/2.49      ( r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),X0),sK4) = iProver_top
% 15.54/2.49      | r2_hidden(X0,k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4))) != iProver_top ),
% 15.54/2.49      inference(global_propositional_subsumption,
% 15.54/2.49                [status(thm)],
% 15.54/2.49                [c_44543,c_46,c_974]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_44750,plain,
% 15.54/2.49      ( r2_hidden(X0,k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4))) != iProver_top
% 15.54/2.49      | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),X0),sK4) = iProver_top ),
% 15.54/2.49      inference(renaming,[status(thm)],[c_44749]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_44763,plain,
% 15.54/2.49      ( r2_relset_1(sK2,sK2,sK3,sK4) = iProver_top
% 15.54/2.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 15.54/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 15.54/2.49      | r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))) = iProver_top
% 15.54/2.49      | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4) = iProver_top
% 15.54/2.49      | v1_relat_1(sK4) != iProver_top
% 15.54/2.49      | v1_relat_1(sK3) != iProver_top ),
% 15.54/2.49      inference(superposition,[status(thm)],[c_8604,c_44750]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_44617,plain,
% 15.54/2.49      ( r2_relset_1(sK2,sK2,sK3,sK4) = iProver_top
% 15.54/2.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 15.54/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 15.54/2.49      | r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4))) = iProver_top
% 15.54/2.49      | v1_relat_1(sK4) != iProver_top
% 15.54/2.49      | v1_relat_1(sK3) != iProver_top ),
% 15.54/2.49      inference(superposition,[status(thm)],[c_44541,c_8604]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_2188,plain,
% 15.54/2.49      ( ~ r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)))
% 15.54/2.49      | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK3)
% 15.54/2.49      | ~ v1_relat_1(sK3) ),
% 15.54/2.49      inference(instantiation,[status(thm)],[c_6]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_2189,plain,
% 15.54/2.49      ( r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4))) != iProver_top
% 15.54/2.49      | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK3) = iProver_top
% 15.54/2.49      | v1_relat_1(sK3) != iProver_top ),
% 15.54/2.49      inference(predicate_to_equality,[status(thm)],[c_2188]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_1366,plain,
% 15.54/2.49      ( ~ r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4)))
% 15.54/2.49      | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4)
% 15.54/2.49      | ~ v1_relat_1(sK4) ),
% 15.54/2.49      inference(instantiation,[status(thm)],[c_6]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_1367,plain,
% 15.54/2.49      ( r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))) != iProver_top
% 15.54/2.49      | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4) = iProver_top
% 15.54/2.49      | v1_relat_1(sK4) != iProver_top ),
% 15.54/2.49      inference(predicate_to_equality,[status(thm)],[c_1366]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_975,plain,
% 15.54/2.49      ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK2)) | v1_relat_1(sK3) ),
% 15.54/2.49      inference(resolution,[status(thm)],[c_4,c_17]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_976,plain,
% 15.54/2.49      ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) != iProver_top
% 15.54/2.49      | v1_relat_1(sK3) = iProver_top ),
% 15.54/2.49      inference(predicate_to_equality,[status(thm)],[c_975]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_8,plain,
% 15.54/2.49      ( r2_relset_1(X0,X1,X2,X3)
% 15.54/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.54/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.54/2.49      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3)
% 15.54/2.49      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2) ),
% 15.54/2.49      inference(cnf_transformation,[],[f40]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_436,plain,
% 15.54/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.54/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.54/2.49      | ~ r2_hidden(k4_tarski(sK0(X1,X2,X3,X0),sK1(X1,X2,X3,X0)),X0)
% 15.54/2.49      | ~ r2_hidden(k4_tarski(sK0(X1,X2,X3,X0),sK1(X1,X2,X3,X0)),X3)
% 15.54/2.49      | sK4 != X0
% 15.54/2.49      | sK3 != X3
% 15.54/2.49      | sK2 != X2
% 15.54/2.49      | sK2 != X1 ),
% 15.54/2.49      inference(resolution_lifted,[status(thm)],[c_8,c_14]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_437,plain,
% 15.54/2.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 15.54/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 15.54/2.49      | ~ r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4)
% 15.54/2.49      | ~ r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK3) ),
% 15.54/2.49      inference(unflattening,[status(thm)],[c_436]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_439,plain,
% 15.54/2.49      ( ~ r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4)
% 15.54/2.49      | ~ r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK3) ),
% 15.54/2.49      inference(global_propositional_subsumption,
% 15.54/2.49                [status(thm)],
% 15.54/2.49                [c_437,c_17,c_16]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(c_441,plain,
% 15.54/2.49      ( r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4) != iProver_top
% 15.54/2.49      | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK3) != iProver_top ),
% 15.54/2.49      inference(predicate_to_equality,[status(thm)],[c_439]) ).
% 15.54/2.49  
% 15.54/2.49  cnf(contradiction,plain,
% 15.54/2.49      ( $false ),
% 15.54/2.49      inference(minisat,
% 15.54/2.49                [status(thm)],
% 15.54/2.49                [c_44763,c_44617,c_2189,c_1367,c_976,c_974,c_441,c_46,
% 15.54/2.49                 c_23,c_19,c_18]) ).
% 15.54/2.49  
% 15.54/2.49  
% 15.54/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.54/2.49  
% 15.54/2.49  ------                               Statistics
% 15.54/2.49  
% 15.54/2.49  ------ Selected
% 15.54/2.49  
% 15.54/2.49  total_time:                             1.655
% 15.54/2.49  
%------------------------------------------------------------------------------
