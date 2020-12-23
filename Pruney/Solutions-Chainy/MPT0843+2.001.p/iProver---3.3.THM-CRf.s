%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:57:07 EST 2020

% Result     : Theorem 15.07s
% Output     : CNFRefutation 15.07s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 655 expanded)
%              Number of clauses        :   64 ( 201 expanded)
%              Number of leaves         :   10 ( 154 expanded)
%              Depth                    :   19
%              Number of atoms          :  405 (3526 expanded)
%              Number of equality atoms :  126 ( 548 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f11])).

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
    inference(flattening,[],[f17])).

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
    inference(rectify,[],[f18])).

fof(f21,plain,(
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

fof(f20,plain,(
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

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21,f20])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3)
      | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3)
      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
         => ( ! [X3] :
                ( r2_hidden(X3,X0)
               => k11_relat_1(X1,X3) = k11_relat_1(X2,X3) )
           => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
           => ( ! [X3] :
                  ( r2_hidden(X3,X0)
                 => k11_relat_1(X1,X3) = k11_relat_1(X2,X3) )
             => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & ! [X3] :
              ( k11_relat_1(X1,X3) = k11_relat_1(X2,X3)
              | ~ r2_hidden(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & ! [X3] :
              ( k11_relat_1(X1,X3) = k11_relat_1(X2,X3)
              | ~ r2_hidden(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f12])).

fof(f24,plain,(
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

fof(f23,plain,
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

fof(f25,plain,
    ( ~ r2_relset_1(sK2,sK2,sK3,sK4)
    & ! [X3] :
        ( k11_relat_1(sK3,X3) = k11_relat_1(sK4,X3)
        | ~ r2_hidden(X3,sK2) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f13,f24,f23])).

fof(f40,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f14])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f39,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,(
    ! [X3] :
      ( k11_relat_1(sK3,X3) = k11_relat_1(sK4,X3)
      | ~ r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
    ~ r2_relset_1(sK2,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_8,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_875,plain,
    ( r2_relset_1(X0,X1,X2,X3) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) = iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_878,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1599,plain,
    ( r2_relset_1(X0,X1,X2,X3) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X2,sK0(X0,X1,X2,X3))) = iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_875,c_878])).

cnf(c_7766,plain,
    ( r2_relset_1(X0,X1,X2,X3) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X2,sK0(X0,X1,X2,X3))) = iProver_top
    | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X3,sK0(X0,X1,X2,X3))) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1599,c_878])).

cnf(c_4102,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X3,sK0(X0,X1,X2,X3)))
    | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2)
    | ~ v1_relat_1(X3) ),
    inference(resolution,[status(thm)],[c_5,c_8])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_10590,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X3,sK0(X0,X1,X2,X3)))
    | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4102,c_6])).

cnf(c_7,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3)
    | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_11443,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X3,sK0(X0,X1,X2,X3)))
    | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) ),
    inference(resolution,[status(thm)],[c_10590,c_7])).

cnf(c_11444,plain,
    ( r2_relset_1(X0,X1,X2,X3) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X3,sK0(X0,X1,X2,X3))) = iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11443])).

cnf(c_4104,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X2,sK0(X0,X1,X2,X3)))
    | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3)
    | ~ v1_relat_1(X2) ),
    inference(resolution,[status(thm)],[c_5,c_8])).

cnf(c_11506,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X2,sK0(X0,X1,X2,X3)))
    | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4104,c_6])).

cnf(c_11507,plain,
    ( r2_relset_1(X0,X1,X2,X3) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X2,sK0(X0,X1,X2,X3))) = iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11506])).

cnf(c_32126,plain,
    ( r2_relset_1(X0,X1,X2,X3) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X2,sK0(X0,X1,X2,X3))) = iProver_top
    | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X3,sK0(X0,X1,X2,X3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7766,c_11444,c_11507])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_868,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_880,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1220,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK2,sK2)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_868,c_880])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_881,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1703,plain,
    ( r2_hidden(X0,sK2) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1220,c_881])).

cnf(c_1959,plain,
    ( r2_relset_1(X0,X1,X2,sK4) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK0(X0,X1,X2,sK4),sK2) = iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X1,X2,sK4),sK1(X0,X1,X2,sK4)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_875,c_1703])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_867,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1221,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK2,sK2)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_867,c_880])).

cnf(c_1839,plain,
    ( r2_hidden(X0,sK2) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1221,c_881])).

cnf(c_5301,plain,
    ( r2_relset_1(X0,X1,sK3,sK4) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK0(X0,X1,sK3,sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1959,c_1839])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | k11_relat_1(sK3,X0) = k11_relat_1(sK4,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_869,plain,
    ( k11_relat_1(sK3,X0) = k11_relat_1(sK4,X0)
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_40817,plain,
    ( k11_relat_1(sK3,sK0(X0,X1,sK3,sK4)) = k11_relat_1(sK4,sK0(X0,X1,sK3,sK4))
    | r2_relset_1(X0,X1,sK3,sK4) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5301,c_869])).

cnf(c_40822,plain,
    ( k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))
    | r2_relset_1(sK2,sK2,sK3,sK4) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_868,c_40817])).

cnf(c_17,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_18,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_13,negated_conjecture,
    ( ~ r2_relset_1(sK2,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_22,plain,
    ( r2_relset_1(sK2,sK2,sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3054,plain,
    ( ~ r2_hidden(sK0(sK2,sK2,sK3,sK4),sK2)
    | k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_3055,plain,
    ( k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))
    | r2_hidden(sK0(sK2,sK2,sK3,sK4),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3054])).

cnf(c_5321,plain,
    ( r2_relset_1(sK2,sK2,sK3,sK4) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | r2_hidden(sK0(sK2,sK2,sK3,sK4),sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5301])).

cnf(c_40992,plain,
    ( k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_40822,c_17,c_18,c_22,c_3055,c_5321])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_879,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_40994,plain,
    ( r2_hidden(X0,k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4))) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),X0),sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_40992,c_879])).

cnf(c_933,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_934,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_933])).

cnf(c_41150,plain,
    ( r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),X0),sK4) = iProver_top
    | r2_hidden(X0,k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_40994,c_18,c_934])).

cnf(c_41151,plain,
    ( r2_hidden(X0,k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4))) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),X0),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_41150])).

cnf(c_41164,plain,
    ( r2_relset_1(sK2,sK2,sK3,sK4) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))) = iProver_top
    | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_32126,c_41151])).

cnf(c_41046,plain,
    ( r2_relset_1(sK2,sK2,sK3,sK4) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_40992,c_32126])).

cnf(c_1016,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK4,X1))
    | r2_hidden(k4_tarski(X1,X0),sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2031,plain,
    ( ~ r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4)))
    | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1016])).

cnf(c_2032,plain,
    ( r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2031])).

cnf(c_1026,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK3,X1))
    | r2_hidden(k4_tarski(X1,X0),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1946,plain,
    ( ~ r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)))
    | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1026])).

cnf(c_1947,plain,
    ( r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4))) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1946])).

cnf(c_936,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_937,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_936])).

cnf(c_463,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(k4_tarski(sK0(X1,X2,X0,X3),sK1(X1,X2,X0,X3)),X3)
    | ~ r2_hidden(k4_tarski(sK0(X1,X2,X0,X3),sK1(X1,X2,X0,X3)),X0)
    | sK4 != X3
    | sK3 != X0
    | sK2 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_13])).

cnf(c_464,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4)
    | ~ r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK3) ),
    inference(unflattening,[status(thm)],[c_463])).

cnf(c_466,plain,
    ( ~ r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4)
    | ~ r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_464,c_16,c_15])).

cnf(c_468,plain,
    ( r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_466])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_41164,c_41046,c_2032,c_1947,c_937,c_934,c_468,c_22,c_18,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:09:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.07/2.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.07/2.49  
% 15.07/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.07/2.49  
% 15.07/2.49  ------  iProver source info
% 15.07/2.49  
% 15.07/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.07/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.07/2.49  git: non_committed_changes: false
% 15.07/2.49  git: last_make_outside_of_git: false
% 15.07/2.49  
% 15.07/2.49  ------ 
% 15.07/2.49  ------ Parsing...
% 15.07/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.07/2.49  
% 15.07/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.07/2.49  
% 15.07/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.07/2.49  
% 15.07/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.07/2.49  ------ Proving...
% 15.07/2.49  ------ Problem Properties 
% 15.07/2.49  
% 15.07/2.49  
% 15.07/2.49  clauses                                 17
% 15.07/2.49  conjectures                             4
% 15.07/2.49  EPR                                     1
% 15.07/2.49  Horn                                    14
% 15.07/2.49  unary                                   3
% 15.07/2.49  binary                                  4
% 15.07/2.49  lits                                    55
% 15.07/2.49  lits eq                                 1
% 15.07/2.49  fd_pure                                 0
% 15.07/2.49  fd_pseudo                               0
% 15.07/2.49  fd_cond                                 0
% 15.07/2.49  fd_pseudo_cond                          0
% 15.07/2.49  AC symbols                              0
% 15.07/2.49  
% 15.07/2.49  ------ Input Options Time Limit: Unbounded
% 15.07/2.49  
% 15.07/2.49  
% 15.07/2.49  ------ 
% 15.07/2.49  Current options:
% 15.07/2.49  ------ 
% 15.07/2.49  
% 15.07/2.49  
% 15.07/2.49  
% 15.07/2.49  
% 15.07/2.49  ------ Proving...
% 15.07/2.49  
% 15.07/2.49  
% 15.07/2.49  % SZS status Theorem for theBenchmark.p
% 15.07/2.49  
% 15.07/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.07/2.49  
% 15.07/2.49  fof(f5,axiom,(
% 15.07/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => (r2_hidden(k4_tarski(X4,X5),X2) <=> r2_hidden(k4_tarski(X4,X5),X3)))))))),
% 15.07/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.49  
% 15.07/2.49  fof(f11,plain,(
% 15.07/2.49    ! [X0,X1,X2] : (! [X3] : ((r2_relset_1(X0,X1,X2,X3) <=> ! [X4] : (! [X5] : ((r2_hidden(k4_tarski(X4,X5),X2) <=> r2_hidden(k4_tarski(X4,X5),X3)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.07/2.49    inference(ennf_transformation,[],[f5])).
% 15.07/2.49  
% 15.07/2.49  fof(f17,plain,(
% 15.07/2.49    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (? [X5] : (((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2))) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X4] : (! [X5] : (((r2_hidden(k4_tarski(X4,X5),X2) | ~r2_hidden(k4_tarski(X4,X5),X3)) & (r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2))) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.07/2.49    inference(nnf_transformation,[],[f11])).
% 15.07/2.49  
% 15.07/2.49  fof(f18,plain,(
% 15.07/2.49    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X4] : (! [X5] : (((r2_hidden(k4_tarski(X4,X5),X2) | ~r2_hidden(k4_tarski(X4,X5),X3)) & (r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2))) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.07/2.49    inference(flattening,[],[f17])).
% 15.07/2.49  
% 15.07/2.49  fof(f19,plain,(
% 15.07/2.49    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X6] : (! [X7] : (((r2_hidden(k4_tarski(X6,X7),X2) | ~r2_hidden(k4_tarski(X6,X7),X3)) & (r2_hidden(k4_tarski(X6,X7),X3) | ~r2_hidden(k4_tarski(X6,X7),X2))) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.07/2.49    inference(rectify,[],[f18])).
% 15.07/2.49  
% 15.07/2.49  fof(f21,plain,(
% 15.07/2.49    ( ! [X4] : (! [X3,X2,X1,X0] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) => ((~r2_hidden(k4_tarski(X4,sK1(X0,X1,X2,X3)),X3) | ~r2_hidden(k4_tarski(X4,sK1(X0,X1,X2,X3)),X2)) & (r2_hidden(k4_tarski(X4,sK1(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(X4,sK1(X0,X1,X2,X3)),X2)) & m1_subset_1(sK1(X0,X1,X2,X3),X1)))) )),
% 15.07/2.49    introduced(choice_axiom,[])).
% 15.07/2.49  
% 15.07/2.49  fof(f20,plain,(
% 15.07/2.49    ! [X3,X2,X1,X0] : (? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) => (? [X5] : ((~r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),X5),X3) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),X5),X2)) & (r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),X5),X3) | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(sK0(X0,X1,X2,X3),X0)))),
% 15.07/2.49    introduced(choice_axiom,[])).
% 15.07/2.49  
% 15.07/2.49  fof(f22,plain,(
% 15.07/2.49    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | (((~r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2)) & (r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2)) & m1_subset_1(sK1(X0,X1,X2,X3),X1)) & m1_subset_1(sK0(X0,X1,X2,X3),X0))) & (! [X6] : (! [X7] : (((r2_hidden(k4_tarski(X6,X7),X2) | ~r2_hidden(k4_tarski(X6,X7),X3)) & (r2_hidden(k4_tarski(X6,X7),X3) | ~r2_hidden(k4_tarski(X6,X7),X2))) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.07/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21,f20])).
% 15.07/2.49  
% 15.07/2.49  fof(f37,plain,(
% 15.07/2.49    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.07/2.49    inference(cnf_transformation,[],[f22])).
% 15.07/2.49  
% 15.07/2.49  fof(f3,axiom,(
% 15.07/2.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 15.07/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.49  
% 15.07/2.49  fof(f9,plain,(
% 15.07/2.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 15.07/2.49    inference(ennf_transformation,[],[f3])).
% 15.07/2.49  
% 15.07/2.49  fof(f16,plain,(
% 15.07/2.49    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 15.07/2.49    inference(nnf_transformation,[],[f9])).
% 15.07/2.49  
% 15.07/2.49  fof(f30,plain,(
% 15.07/2.49    ( ! [X2,X0,X1] : (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 15.07/2.49    inference(cnf_transformation,[],[f16])).
% 15.07/2.49  
% 15.07/2.49  fof(f4,axiom,(
% 15.07/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 15.07/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.50  
% 15.07/2.50  fof(f10,plain,(
% 15.07/2.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.07/2.50    inference(ennf_transformation,[],[f4])).
% 15.07/2.50  
% 15.07/2.50  fof(f32,plain,(
% 15.07/2.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.07/2.50    inference(cnf_transformation,[],[f10])).
% 15.07/2.50  
% 15.07/2.50  fof(f38,plain,(
% 15.07/2.50    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.07/2.50    inference(cnf_transformation,[],[f22])).
% 15.07/2.50  
% 15.07/2.50  fof(f6,conjecture,(
% 15.07/2.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (! [X3] : (r2_hidden(X3,X0) => k11_relat_1(X1,X3) = k11_relat_1(X2,X3)) => r2_relset_1(X0,X0,X1,X2))))),
% 15.07/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.50  
% 15.07/2.50  fof(f7,negated_conjecture,(
% 15.07/2.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (! [X3] : (r2_hidden(X3,X0) => k11_relat_1(X1,X3) = k11_relat_1(X2,X3)) => r2_relset_1(X0,X0,X1,X2))))),
% 15.07/2.50    inference(negated_conjecture,[],[f6])).
% 15.07/2.50  
% 15.07/2.50  fof(f12,plain,(
% 15.07/2.50    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X1,X2) & ! [X3] : (k11_relat_1(X1,X3) = k11_relat_1(X2,X3) | ~r2_hidden(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 15.07/2.50    inference(ennf_transformation,[],[f7])).
% 15.07/2.50  
% 15.07/2.50  fof(f13,plain,(
% 15.07/2.50    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X1,X2) & ! [X3] : (k11_relat_1(X1,X3) = k11_relat_1(X2,X3) | ~r2_hidden(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 15.07/2.50    inference(flattening,[],[f12])).
% 15.07/2.50  
% 15.07/2.50  fof(f24,plain,(
% 15.07/2.50    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X1,X2) & ! [X3] : (k11_relat_1(X1,X3) = k11_relat_1(X2,X3) | ~r2_hidden(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) => (~r2_relset_1(X0,X0,X1,sK4) & ! [X3] : (k11_relat_1(sK4,X3) = k11_relat_1(X1,X3) | ~r2_hidden(X3,X0)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))) )),
% 15.07/2.50    introduced(choice_axiom,[])).
% 15.07/2.50  
% 15.07/2.50  fof(f23,plain,(
% 15.07/2.50    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X1,X2) & ! [X3] : (k11_relat_1(X1,X3) = k11_relat_1(X2,X3) | ~r2_hidden(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) => (? [X2] : (~r2_relset_1(sK2,sK2,sK3,X2) & ! [X3] : (k11_relat_1(sK3,X3) = k11_relat_1(X2,X3) | ~r2_hidden(X3,sK2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))))),
% 15.07/2.50    introduced(choice_axiom,[])).
% 15.07/2.50  
% 15.07/2.50  fof(f25,plain,(
% 15.07/2.50    (~r2_relset_1(sK2,sK2,sK3,sK4) & ! [X3] : (k11_relat_1(sK3,X3) = k11_relat_1(sK4,X3) | ~r2_hidden(X3,sK2)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 15.07/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f13,f24,f23])).
% 15.07/2.50  
% 15.07/2.50  fof(f40,plain,(
% 15.07/2.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 15.07/2.50    inference(cnf_transformation,[],[f25])).
% 15.07/2.50  
% 15.07/2.50  fof(f2,axiom,(
% 15.07/2.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 15.07/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.50  
% 15.07/2.50  fof(f8,plain,(
% 15.07/2.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.07/2.50    inference(ennf_transformation,[],[f2])).
% 15.07/2.50  
% 15.07/2.50  fof(f29,plain,(
% 15.07/2.50    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.07/2.50    inference(cnf_transformation,[],[f8])).
% 15.07/2.50  
% 15.07/2.50  fof(f1,axiom,(
% 15.07/2.50    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 15.07/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.50  
% 15.07/2.50  fof(f14,plain,(
% 15.07/2.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 15.07/2.50    inference(nnf_transformation,[],[f1])).
% 15.07/2.50  
% 15.07/2.50  fof(f15,plain,(
% 15.07/2.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 15.07/2.50    inference(flattening,[],[f14])).
% 15.07/2.50  
% 15.07/2.50  fof(f26,plain,(
% 15.07/2.50    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 15.07/2.50    inference(cnf_transformation,[],[f15])).
% 15.07/2.50  
% 15.07/2.50  fof(f39,plain,(
% 15.07/2.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 15.07/2.50    inference(cnf_transformation,[],[f25])).
% 15.07/2.50  
% 15.07/2.50  fof(f41,plain,(
% 15.07/2.50    ( ! [X3] : (k11_relat_1(sK3,X3) = k11_relat_1(sK4,X3) | ~r2_hidden(X3,sK2)) )),
% 15.07/2.50    inference(cnf_transformation,[],[f25])).
% 15.07/2.50  
% 15.07/2.50  fof(f42,plain,(
% 15.07/2.50    ~r2_relset_1(sK2,sK2,sK3,sK4)),
% 15.07/2.50    inference(cnf_transformation,[],[f25])).
% 15.07/2.50  
% 15.07/2.50  fof(f31,plain,(
% 15.07/2.50    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 15.07/2.50    inference(cnf_transformation,[],[f16])).
% 15.07/2.50  
% 15.07/2.50  cnf(c_8,plain,
% 15.07/2.50      ( r2_relset_1(X0,X1,X2,X3)
% 15.07/2.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.07/2.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.07/2.50      | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3)
% 15.07/2.50      | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2) ),
% 15.07/2.50      inference(cnf_transformation,[],[f37]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_875,plain,
% 15.07/2.50      ( r2_relset_1(X0,X1,X2,X3) = iProver_top
% 15.07/2.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.07/2.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.07/2.50      | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) = iProver_top
% 15.07/2.50      | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2) = iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_5,plain,
% 15.07/2.50      ( r2_hidden(X0,k11_relat_1(X1,X2))
% 15.07/2.50      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 15.07/2.50      | ~ v1_relat_1(X1) ),
% 15.07/2.50      inference(cnf_transformation,[],[f30]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_878,plain,
% 15.07/2.50      ( r2_hidden(X0,k11_relat_1(X1,X2)) = iProver_top
% 15.07/2.50      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
% 15.07/2.50      | v1_relat_1(X1) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_1599,plain,
% 15.07/2.50      ( r2_relset_1(X0,X1,X2,X3) = iProver_top
% 15.07/2.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.07/2.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.07/2.50      | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X2,sK0(X0,X1,X2,X3))) = iProver_top
% 15.07/2.50      | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) = iProver_top
% 15.07/2.50      | v1_relat_1(X2) != iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_875,c_878]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_7766,plain,
% 15.07/2.50      ( r2_relset_1(X0,X1,X2,X3) = iProver_top
% 15.07/2.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.07/2.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.07/2.50      | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X2,sK0(X0,X1,X2,X3))) = iProver_top
% 15.07/2.50      | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X3,sK0(X0,X1,X2,X3))) = iProver_top
% 15.07/2.50      | v1_relat_1(X2) != iProver_top
% 15.07/2.50      | v1_relat_1(X3) != iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_1599,c_878]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_4102,plain,
% 15.07/2.50      ( r2_relset_1(X0,X1,X2,X3)
% 15.07/2.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.07/2.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.07/2.50      | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X3,sK0(X0,X1,X2,X3)))
% 15.07/2.50      | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2)
% 15.07/2.50      | ~ v1_relat_1(X3) ),
% 15.07/2.50      inference(resolution,[status(thm)],[c_5,c_8]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_6,plain,
% 15.07/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.07/2.50      | v1_relat_1(X0) ),
% 15.07/2.50      inference(cnf_transformation,[],[f32]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_10590,plain,
% 15.07/2.50      ( r2_relset_1(X0,X1,X2,X3)
% 15.07/2.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.07/2.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.07/2.50      | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X3,sK0(X0,X1,X2,X3)))
% 15.07/2.50      | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2) ),
% 15.07/2.50      inference(forward_subsumption_resolution,
% 15.07/2.50                [status(thm)],
% 15.07/2.50                [c_4102,c_6]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_7,plain,
% 15.07/2.50      ( r2_relset_1(X0,X1,X2,X3)
% 15.07/2.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.07/2.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.07/2.50      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3)
% 15.07/2.50      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2) ),
% 15.07/2.50      inference(cnf_transformation,[],[f38]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_11443,plain,
% 15.07/2.50      ( r2_relset_1(X0,X1,X2,X3)
% 15.07/2.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.07/2.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.07/2.50      | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X3,sK0(X0,X1,X2,X3)))
% 15.07/2.50      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) ),
% 15.07/2.50      inference(resolution,[status(thm)],[c_10590,c_7]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_11444,plain,
% 15.07/2.50      ( r2_relset_1(X0,X1,X2,X3) = iProver_top
% 15.07/2.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.07/2.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.07/2.50      | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X3,sK0(X0,X1,X2,X3))) = iProver_top
% 15.07/2.50      | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_11443]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_4104,plain,
% 15.07/2.50      ( r2_relset_1(X0,X1,X2,X3)
% 15.07/2.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.07/2.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.07/2.50      | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X2,sK0(X0,X1,X2,X3)))
% 15.07/2.50      | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3)
% 15.07/2.50      | ~ v1_relat_1(X2) ),
% 15.07/2.50      inference(resolution,[status(thm)],[c_5,c_8]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_11506,plain,
% 15.07/2.50      ( r2_relset_1(X0,X1,X2,X3)
% 15.07/2.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.07/2.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.07/2.50      | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X2,sK0(X0,X1,X2,X3)))
% 15.07/2.50      | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) ),
% 15.07/2.50      inference(forward_subsumption_resolution,
% 15.07/2.50                [status(thm)],
% 15.07/2.50                [c_4104,c_6]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_11507,plain,
% 15.07/2.50      ( r2_relset_1(X0,X1,X2,X3) = iProver_top
% 15.07/2.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.07/2.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.07/2.50      | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X2,sK0(X0,X1,X2,X3))) = iProver_top
% 15.07/2.50      | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) = iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_11506]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_32126,plain,
% 15.07/2.50      ( r2_relset_1(X0,X1,X2,X3) = iProver_top
% 15.07/2.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.07/2.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.07/2.50      | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X2,sK0(X0,X1,X2,X3))) = iProver_top
% 15.07/2.50      | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X3,sK0(X0,X1,X2,X3))) = iProver_top ),
% 15.07/2.50      inference(global_propositional_subsumption,
% 15.07/2.50                [status(thm)],
% 15.07/2.50                [c_7766,c_11444,c_11507]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_15,negated_conjecture,
% 15.07/2.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 15.07/2.50      inference(cnf_transformation,[],[f40]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_868,plain,
% 15.07/2.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_3,plain,
% 15.07/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.07/2.50      | ~ r2_hidden(X2,X0)
% 15.07/2.50      | r2_hidden(X2,X1) ),
% 15.07/2.50      inference(cnf_transformation,[],[f29]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_880,plain,
% 15.07/2.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.07/2.50      | r2_hidden(X2,X0) != iProver_top
% 15.07/2.50      | r2_hidden(X2,X1) = iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_1220,plain,
% 15.07/2.50      ( r2_hidden(X0,k2_zfmisc_1(sK2,sK2)) = iProver_top
% 15.07/2.50      | r2_hidden(X0,sK4) != iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_868,c_880]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_2,plain,
% 15.07/2.50      ( r2_hidden(X0,X1)
% 15.07/2.50      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 15.07/2.50      inference(cnf_transformation,[],[f26]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_881,plain,
% 15.07/2.50      ( r2_hidden(X0,X1) = iProver_top
% 15.07/2.50      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_1703,plain,
% 15.07/2.50      ( r2_hidden(X0,sK2) = iProver_top
% 15.07/2.50      | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_1220,c_881]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_1959,plain,
% 15.07/2.50      ( r2_relset_1(X0,X1,X2,sK4) = iProver_top
% 15.07/2.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.07/2.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.07/2.50      | r2_hidden(sK0(X0,X1,X2,sK4),sK2) = iProver_top
% 15.07/2.50      | r2_hidden(k4_tarski(sK0(X0,X1,X2,sK4),sK1(X0,X1,X2,sK4)),X2) = iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_875,c_1703]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_16,negated_conjecture,
% 15.07/2.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 15.07/2.50      inference(cnf_transformation,[],[f39]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_867,plain,
% 15.07/2.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_1221,plain,
% 15.07/2.50      ( r2_hidden(X0,k2_zfmisc_1(sK2,sK2)) = iProver_top
% 15.07/2.50      | r2_hidden(X0,sK3) != iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_867,c_880]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_1839,plain,
% 15.07/2.50      ( r2_hidden(X0,sK2) = iProver_top
% 15.07/2.50      | r2_hidden(k4_tarski(X0,X1),sK3) != iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_1221,c_881]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_5301,plain,
% 15.07/2.50      ( r2_relset_1(X0,X1,sK3,sK4) = iProver_top
% 15.07/2.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.07/2.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.07/2.50      | r2_hidden(sK0(X0,X1,sK3,sK4),sK2) = iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_1959,c_1839]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_14,negated_conjecture,
% 15.07/2.50      ( ~ r2_hidden(X0,sK2) | k11_relat_1(sK3,X0) = k11_relat_1(sK4,X0) ),
% 15.07/2.50      inference(cnf_transformation,[],[f41]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_869,plain,
% 15.07/2.50      ( k11_relat_1(sK3,X0) = k11_relat_1(sK4,X0)
% 15.07/2.50      | r2_hidden(X0,sK2) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_40817,plain,
% 15.07/2.50      ( k11_relat_1(sK3,sK0(X0,X1,sK3,sK4)) = k11_relat_1(sK4,sK0(X0,X1,sK3,sK4))
% 15.07/2.50      | r2_relset_1(X0,X1,sK3,sK4) = iProver_top
% 15.07/2.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.07/2.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_5301,c_869]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_40822,plain,
% 15.07/2.50      ( k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))
% 15.07/2.50      | r2_relset_1(sK2,sK2,sK3,sK4) = iProver_top
% 15.07/2.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_868,c_40817]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_17,plain,
% 15.07/2.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_18,plain,
% 15.07/2.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_13,negated_conjecture,
% 15.07/2.50      ( ~ r2_relset_1(sK2,sK2,sK3,sK4) ),
% 15.07/2.50      inference(cnf_transformation,[],[f42]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_22,plain,
% 15.07/2.50      ( r2_relset_1(sK2,sK2,sK3,sK4) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_3054,plain,
% 15.07/2.50      ( ~ r2_hidden(sK0(sK2,sK2,sK3,sK4),sK2)
% 15.07/2.50      | k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4)) ),
% 15.07/2.50      inference(instantiation,[status(thm)],[c_14]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_3055,plain,
% 15.07/2.50      ( k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))
% 15.07/2.50      | r2_hidden(sK0(sK2,sK2,sK3,sK4),sK2) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_3054]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_5321,plain,
% 15.07/2.50      ( r2_relset_1(sK2,sK2,sK3,sK4) = iProver_top
% 15.07/2.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 15.07/2.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 15.07/2.50      | r2_hidden(sK0(sK2,sK2,sK3,sK4),sK2) = iProver_top ),
% 15.07/2.50      inference(instantiation,[status(thm)],[c_5301]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_40992,plain,
% 15.07/2.50      ( k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4)) ),
% 15.07/2.50      inference(global_propositional_subsumption,
% 15.07/2.50                [status(thm)],
% 15.07/2.50                [c_40822,c_17,c_18,c_22,c_3055,c_5321]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_4,plain,
% 15.07/2.50      ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
% 15.07/2.50      | r2_hidden(k4_tarski(X2,X0),X1)
% 15.07/2.50      | ~ v1_relat_1(X1) ),
% 15.07/2.50      inference(cnf_transformation,[],[f31]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_879,plain,
% 15.07/2.50      ( r2_hidden(X0,k11_relat_1(X1,X2)) != iProver_top
% 15.07/2.50      | r2_hidden(k4_tarski(X2,X0),X1) = iProver_top
% 15.07/2.50      | v1_relat_1(X1) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_40994,plain,
% 15.07/2.50      ( r2_hidden(X0,k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4))) != iProver_top
% 15.07/2.50      | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),X0),sK4) = iProver_top
% 15.07/2.50      | v1_relat_1(sK4) != iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_40992,c_879]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_933,plain,
% 15.07/2.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 15.07/2.50      | v1_relat_1(sK4) ),
% 15.07/2.50      inference(instantiation,[status(thm)],[c_6]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_934,plain,
% 15.07/2.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 15.07/2.50      | v1_relat_1(sK4) = iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_933]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_41150,plain,
% 15.07/2.50      ( r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),X0),sK4) = iProver_top
% 15.07/2.50      | r2_hidden(X0,k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4))) != iProver_top ),
% 15.07/2.50      inference(global_propositional_subsumption,
% 15.07/2.50                [status(thm)],
% 15.07/2.50                [c_40994,c_18,c_934]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_41151,plain,
% 15.07/2.50      ( r2_hidden(X0,k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4))) != iProver_top
% 15.07/2.50      | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),X0),sK4) = iProver_top ),
% 15.07/2.50      inference(renaming,[status(thm)],[c_41150]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_41164,plain,
% 15.07/2.50      ( r2_relset_1(sK2,sK2,sK3,sK4) = iProver_top
% 15.07/2.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 15.07/2.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 15.07/2.50      | r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))) = iProver_top
% 15.07/2.50      | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4) = iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_32126,c_41151]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_41046,plain,
% 15.07/2.50      ( r2_relset_1(sK2,sK2,sK3,sK4) = iProver_top
% 15.07/2.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 15.07/2.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 15.07/2.50      | r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4))) = iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_40992,c_32126]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_1016,plain,
% 15.07/2.50      ( ~ r2_hidden(X0,k11_relat_1(sK4,X1))
% 15.07/2.50      | r2_hidden(k4_tarski(X1,X0),sK4)
% 15.07/2.50      | ~ v1_relat_1(sK4) ),
% 15.07/2.50      inference(instantiation,[status(thm)],[c_4]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_2031,plain,
% 15.07/2.50      ( ~ r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4)))
% 15.07/2.50      | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4)
% 15.07/2.50      | ~ v1_relat_1(sK4) ),
% 15.07/2.50      inference(instantiation,[status(thm)],[c_1016]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_2032,plain,
% 15.07/2.50      ( r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))) != iProver_top
% 15.07/2.50      | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4) = iProver_top
% 15.07/2.50      | v1_relat_1(sK4) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_2031]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_1026,plain,
% 15.07/2.50      ( ~ r2_hidden(X0,k11_relat_1(sK3,X1))
% 15.07/2.50      | r2_hidden(k4_tarski(X1,X0),sK3)
% 15.07/2.50      | ~ v1_relat_1(sK3) ),
% 15.07/2.50      inference(instantiation,[status(thm)],[c_4]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_1946,plain,
% 15.07/2.50      ( ~ r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)))
% 15.07/2.50      | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK3)
% 15.07/2.50      | ~ v1_relat_1(sK3) ),
% 15.07/2.50      inference(instantiation,[status(thm)],[c_1026]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_1947,plain,
% 15.07/2.50      ( r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4))) != iProver_top
% 15.07/2.50      | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK3) = iProver_top
% 15.07/2.50      | v1_relat_1(sK3) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_1946]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_936,plain,
% 15.07/2.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 15.07/2.50      | v1_relat_1(sK3) ),
% 15.07/2.50      inference(instantiation,[status(thm)],[c_6]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_937,plain,
% 15.07/2.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 15.07/2.50      | v1_relat_1(sK3) = iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_936]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_463,plain,
% 15.07/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.07/2.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.07/2.50      | ~ r2_hidden(k4_tarski(sK0(X1,X2,X0,X3),sK1(X1,X2,X0,X3)),X3)
% 15.07/2.50      | ~ r2_hidden(k4_tarski(sK0(X1,X2,X0,X3),sK1(X1,X2,X0,X3)),X0)
% 15.07/2.50      | sK4 != X3
% 15.07/2.50      | sK3 != X0
% 15.07/2.50      | sK2 != X2
% 15.07/2.50      | sK2 != X1 ),
% 15.07/2.50      inference(resolution_lifted,[status(thm)],[c_7,c_13]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_464,plain,
% 15.07/2.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 15.07/2.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 15.07/2.50      | ~ r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4)
% 15.07/2.50      | ~ r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK3) ),
% 15.07/2.50      inference(unflattening,[status(thm)],[c_463]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_466,plain,
% 15.07/2.50      ( ~ r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4)
% 15.07/2.50      | ~ r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK3) ),
% 15.07/2.50      inference(global_propositional_subsumption,
% 15.07/2.50                [status(thm)],
% 15.07/2.50                [c_464,c_16,c_15]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_468,plain,
% 15.07/2.50      ( r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4) != iProver_top
% 15.07/2.50      | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK3) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_466]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(contradiction,plain,
% 15.07/2.50      ( $false ),
% 15.07/2.50      inference(minisat,
% 15.07/2.50                [status(thm)],
% 15.07/2.50                [c_41164,c_41046,c_2032,c_1947,c_937,c_934,c_468,c_22,
% 15.07/2.50                 c_18,c_17]) ).
% 15.07/2.50  
% 15.07/2.50  
% 15.07/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.07/2.50  
% 15.07/2.50  ------                               Statistics
% 15.07/2.50  
% 15.07/2.50  ------ Selected
% 15.07/2.50  
% 15.07/2.50  total_time:                             1.524
% 15.07/2.50  
%------------------------------------------------------------------------------
