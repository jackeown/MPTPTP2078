%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0419+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:15 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 186 expanded)
%              Number of clauses        :   57 (  69 expanded)
%              Number of leaves         :   13 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :  352 ( 743 expanded)
%              Number of equality atoms :   65 (  88 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f20])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( ( ~ r2_hidden(k3_subset_1(X0,sK1(X0,X1,X2)),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( r2_hidden(k3_subset_1(X0,sK1(X0,X1,X2)),X1)
          | r2_hidden(sK1(X0,X1,X2),X2) )
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k3_subset_1(X0,sK1(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK1(X0,X1,X2),X2) )
                & ( r2_hidden(k3_subset_1(X0,sK1(X0,X1,X2)),X1)
                  | r2_hidden(sK1(X0,X1,X2),X2) )
                & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f32])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
             => r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f14])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ~ r1_tarski(X1,sK4)
        & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,sK4))
        & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X1,X2)
            & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(sK3,X2)
          & r1_tarski(k7_setfam_1(sK2,sK3),k7_setfam_1(sK2,X2))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK2))) )
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ r1_tarski(sK3,sK4)
    & r1_tarski(k7_setfam_1(sK2,sK3),k7_setfam_1(sK2,sK4))
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f15,f26,f25])).

fof(f39,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f40,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f27])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    ~ r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    r1_tarski(k7_setfam_1(sK2,sK3),k7_setfam_1(sK2,sK4)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_706,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k7_setfam_1(X2,X3))
    | ~ r1_tarski(k7_setfam_1(X2,X3),X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1033,plain,
    ( r2_hidden(k3_subset_1(X0,X1),X2)
    | ~ r2_hidden(k3_subset_1(X0,X1),k7_setfam_1(X3,X4))
    | ~ r1_tarski(k7_setfam_1(X3,X4),X2) ),
    inference(instantiation,[status(thm)],[c_706])).

cnf(c_1466,plain,
    ( r2_hidden(k3_subset_1(X0,X1),k7_setfam_1(sK2,sK4))
    | ~ r2_hidden(k3_subset_1(X0,X1),k7_setfam_1(sK2,sK3))
    | ~ r1_tarski(k7_setfam_1(sK2,sK3),k7_setfam_1(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_1033])).

cnf(c_8035,plain,
    ( r2_hidden(k3_subset_1(sK2,sK0(sK3,sK4)),k7_setfam_1(sK2,sK4))
    | ~ r2_hidden(k3_subset_1(sK2,sK0(sK3,sK4)),k7_setfam_1(sK2,sK3))
    | ~ r1_tarski(k7_setfam_1(sK2,sK3),k7_setfam_1(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_1466])).

cnf(c_243,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_606,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(sK3,sK4),X2)
    | X2 != X1
    | sK0(sK3,sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_243])).

cnf(c_676,plain,
    ( ~ r2_hidden(sK0(sK3,sK4),X0)
    | r2_hidden(sK0(sK3,sK4),X1)
    | X1 != X0
    | sK0(sK3,sK4) != sK0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_606])).

cnf(c_826,plain,
    ( ~ r2_hidden(sK0(sK3,sK4),X0)
    | r2_hidden(sK0(sK3,sK4),k7_setfam_1(X1,X2))
    | k7_setfam_1(X1,X2) != X0
    | sK0(sK3,sK4) != sK0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_676])).

cnf(c_1341,plain,
    ( ~ r2_hidden(sK0(sK3,sK4),X0)
    | r2_hidden(sK0(sK3,sK4),k7_setfam_1(X1,k7_setfam_1(X1,X0)))
    | k7_setfam_1(X1,k7_setfam_1(X1,X0)) != X0
    | sK0(sK3,sK4) != sK0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_826])).

cnf(c_3796,plain,
    ( r2_hidden(sK0(sK3,sK4),k7_setfam_1(sK2,k7_setfam_1(sK2,sK3)))
    | ~ r2_hidden(sK0(sK3,sK4),sK3)
    | k7_setfam_1(sK2,k7_setfam_1(sK2,sK3)) != sK3
    | sK0(sK3,sK4) != sK0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1341])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_3212,plain,
    ( m1_subset_1(k7_setfam_1(X0,k7_setfam_1(X0,sK4)),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ m1_subset_1(k7_setfam_1(X0,sK4),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3217,plain,
    ( m1_subset_1(k7_setfam_1(sK2,k7_setfam_1(sK2,sK4)),k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | ~ m1_subset_1(k7_setfam_1(sK2,sK4),k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_3212])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r2_hidden(X0,k7_setfam_1(X1,X2))
    | ~ r2_hidden(k3_subset_1(X1,X0),X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_753,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(sK0(sK3,sK4),k1_zfmisc_1(X1))
    | ~ r2_hidden(k3_subset_1(X1,sK0(sK3,sK4)),X0)
    | r2_hidden(sK0(sK3,sK4),k7_setfam_1(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2778,plain,
    ( ~ m1_subset_1(k7_setfam_1(X0,k7_setfam_1(X0,sK4)),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ m1_subset_1(k7_setfam_1(X0,sK4),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ m1_subset_1(sK0(sK3,sK4),k1_zfmisc_1(X0))
    | ~ r2_hidden(k3_subset_1(X0,sK0(sK3,sK4)),k7_setfam_1(X0,sK4))
    | r2_hidden(sK0(sK3,sK4),k7_setfam_1(X0,k7_setfam_1(X0,sK4))) ),
    inference(instantiation,[status(thm)],[c_753])).

cnf(c_2780,plain,
    ( ~ m1_subset_1(k7_setfam_1(sK2,k7_setfam_1(sK2,sK4)),k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | ~ m1_subset_1(k7_setfam_1(sK2,sK4),k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | ~ m1_subset_1(sK0(sK3,sK4),k1_zfmisc_1(sK2))
    | ~ r2_hidden(k3_subset_1(sK2,sK0(sK3,sK4)),k7_setfam_1(sK2,sK4))
    | r2_hidden(sK0(sK3,sK4),k7_setfam_1(sK2,k7_setfam_1(sK2,sK4))) ),
    inference(instantiation,[status(thm)],[c_2778])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X0,k7_setfam_1(X1,X2))
    | r2_hidden(k3_subset_1(X1,X0),X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1620,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | ~ m1_subset_1(k7_setfam_1(sK2,X0),k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | ~ m1_subset_1(sK0(sK3,sK4),k1_zfmisc_1(sK2))
    | r2_hidden(k3_subset_1(sK2,sK0(sK3,sK4)),X0)
    | ~ r2_hidden(sK0(sK3,sK4),k7_setfam_1(sK2,X0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2169,plain,
    ( ~ m1_subset_1(k7_setfam_1(sK2,k7_setfam_1(sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | ~ m1_subset_1(k7_setfam_1(sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | ~ m1_subset_1(sK0(sK3,sK4),k1_zfmisc_1(sK2))
    | r2_hidden(k3_subset_1(sK2,sK0(sK3,sK4)),k7_setfam_1(sK2,sK3))
    | ~ r2_hidden(sK0(sK3,sK4),k7_setfam_1(sK2,k7_setfam_1(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_1620])).

cnf(c_1888,plain,
    ( m1_subset_1(k7_setfam_1(sK2,k7_setfam_1(sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | ~ m1_subset_1(k7_setfam_1(sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1740,plain,
    ( m1_subset_1(k7_setfam_1(sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1543,plain,
    ( m1_subset_1(k7_setfam_1(X0,sK4),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1545,plain,
    ( m1_subset_1(k7_setfam_1(sK2,sK4),k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_1543])).

cnf(c_10,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_870,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(sK0(sK3,sK4),k1_zfmisc_1(X1))
    | ~ r2_hidden(sK0(sK3,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1389,plain,
    ( m1_subset_1(sK0(sK3,sK4),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | ~ r2_hidden(sK0(sK3,sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_870])).

cnf(c_820,plain,
    ( ~ r2_hidden(sK0(sK3,sK4),X0)
    | r2_hidden(sK0(sK3,sK4),sK4)
    | sK0(sK3,sK4) != sK0(sK3,sK4)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_676])).

cnf(c_1205,plain,
    ( ~ r2_hidden(sK0(sK3,sK4),k7_setfam_1(X0,k7_setfam_1(X0,sK4)))
    | r2_hidden(sK0(sK3,sK4),sK4)
    | sK0(sK3,sK4) != sK0(sK3,sK4)
    | sK4 != k7_setfam_1(X0,k7_setfam_1(X0,sK4)) ),
    inference(instantiation,[status(thm)],[c_820])).

cnf(c_1207,plain,
    ( ~ r2_hidden(sK0(sK3,sK4),k7_setfam_1(sK2,k7_setfam_1(sK2,sK4)))
    | r2_hidden(sK0(sK3,sK4),sK4)
    | sK0(sK3,sK4) != sK0(sK3,sK4)
    | sK4 != k7_setfam_1(sK2,k7_setfam_1(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_1205])).

cnf(c_240,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1088,plain,
    ( sK0(sK3,sK4) = sK0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_240])).

cnf(c_241,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_559,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_241])).

cnf(c_588,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_559])).

cnf(c_633,plain,
    ( k7_setfam_1(X0,X1) != sK4
    | sK4 = k7_setfam_1(X0,X1)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_588])).

cnf(c_747,plain,
    ( k7_setfam_1(X0,k7_setfam_1(X0,sK4)) != sK4
    | sK4 = k7_setfam_1(X0,k7_setfam_1(X0,sK4))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_633])).

cnf(c_748,plain,
    ( k7_setfam_1(sK2,k7_setfam_1(sK2,sK4)) != sK4
    | sK4 = k7_setfam_1(sK2,k7_setfam_1(sK2,sK4))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_747])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_499,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_504,plain,
    ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_717,plain,
    ( k7_setfam_1(sK2,k7_setfam_1(sK2,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_499,c_504])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_500,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_716,plain,
    ( k7_setfam_1(sK2,k7_setfam_1(sK2,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_500,c_504])).

cnf(c_578,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_240])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_201,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_11])).

cnf(c_202,plain,
    ( ~ r2_hidden(sK0(sK3,sK4),sK4) ),
    inference(unflattening,[status(thm)],[c_201])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_194,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_11])).

cnf(c_195,plain,
    ( r2_hidden(sK0(sK3,sK4),sK3) ),
    inference(unflattening,[status(thm)],[c_194])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(k7_setfam_1(sK2,sK3),k7_setfam_1(sK2,sK4)) ),
    inference(cnf_transformation,[],[f41])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8035,c_3796,c_3217,c_2780,c_2169,c_1888,c_1740,c_1545,c_1389,c_1207,c_1088,c_748,c_717,c_716,c_578,c_202,c_195,c_12,c_13,c_14])).


%------------------------------------------------------------------------------
