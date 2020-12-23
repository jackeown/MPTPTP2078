%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0419+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:15 EST 2020

% Result     : Theorem 20.11s
% Output     : CNFRefutation 20.11s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 191 expanded)
%              Number of clauses        :   63 (  78 expanded)
%              Number of leaves         :   15 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :  384 ( 728 expanded)
%              Number of equality atoms :   60 (  74 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f45])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f46])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
             => r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f25])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ~ r1_tarski(X1,sK5)
        & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,sK5))
        & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X1,X2)
            & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(sK4,X2)
          & r1_tarski(k7_setfam_1(sK3,sK4),k7_setfam_1(sK3,X2))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK3))) )
      & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ~ r1_tarski(sK4,sK5)
    & r1_tarski(k7_setfam_1(sK3,sK4),k7_setfam_1(sK3,sK5))
    & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3)))
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f26,f40,f39])).

fof(f63,plain,(
    ~ r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f62,plain,(
    r1_tarski(k7_setfam_1(sK3,sK4),k7_setfam_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f41])).

fof(f61,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(cnf_transformation,[],[f41])).

fof(f60,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_801,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_10149,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(sK4,sK5),sK5)
    | sK0(sK4,sK5) != X0
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_33652,plain,
    ( ~ r2_hidden(k3_subset_1(X0,k3_subset_1(X0,sK0(sK4,sK5))),X1)
    | r2_hidden(sK0(sK4,sK5),sK5)
    | sK0(sK4,sK5) != k3_subset_1(X0,k3_subset_1(X0,sK0(sK4,sK5)))
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_10149])).

cnf(c_79787,plain,
    ( ~ r2_hidden(k3_subset_1(X0,k3_subset_1(X0,sK0(sK4,sK5))),sK5)
    | r2_hidden(sK0(sK4,sK5),sK5)
    | sK0(sK4,sK5) != k3_subset_1(X0,k3_subset_1(X0,sK0(sK4,sK5)))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_33652])).

cnf(c_79789,plain,
    ( ~ r2_hidden(k3_subset_1(sK3,k3_subset_1(sK3,sK0(sK4,sK5))),sK5)
    | r2_hidden(sK0(sK4,sK5),sK5)
    | sK0(sK4,sK5) != k3_subset_1(sK3,k3_subset_1(sK3,sK0(sK4,sK5)))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_79787])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X0,k7_setfam_1(X1,X2))
    | r2_hidden(k3_subset_1(X1,X0),X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_14,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_176,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_177,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_176])).

cnf(c_217,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X2,k7_setfam_1(X1,X0))
    | r2_hidden(k3_subset_1(X1,X2),X0)
    | ~ r1_tarski(X2,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_177])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_268,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X2,k7_setfam_1(X1,X0))
    | r2_hidden(k3_subset_1(X1,X2),X0)
    | ~ r1_tarski(X2,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_217,c_9])).

cnf(c_31043,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | ~ r2_hidden(X0,k7_setfam_1(sK3,sK5))
    | r2_hidden(k3_subset_1(sK3,X0),sK5)
    | ~ r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_268])).

cnf(c_54701,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | r2_hidden(k3_subset_1(sK3,k3_subset_1(sK3,sK0(sK4,sK5))),sK5)
    | ~ r2_hidden(k3_subset_1(sK3,sK0(sK4,sK5)),k7_setfam_1(sK3,sK5))
    | ~ r1_tarski(k3_subset_1(sK3,sK0(sK4,sK5)),sK3) ),
    inference(instantiation,[status(thm)],[c_31043])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_9497,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k7_setfam_1(X2,X3))
    | ~ r1_tarski(X1,k7_setfam_1(X2,X3)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_43430,plain,
    ( r2_hidden(X0,k7_setfam_1(sK3,sK5))
    | ~ r2_hidden(X0,k7_setfam_1(sK3,sK4))
    | ~ r1_tarski(k7_setfam_1(sK3,sK4),k7_setfam_1(sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_9497])).

cnf(c_49707,plain,
    ( r2_hidden(k3_subset_1(sK3,sK0(sK4,sK5)),k7_setfam_1(sK3,sK5))
    | ~ r2_hidden(k3_subset_1(sK3,sK0(sK4,sK5)),k7_setfam_1(sK3,sK4))
    | ~ r1_tarski(k7_setfam_1(sK3,sK4),k7_setfam_1(sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_43430])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_218,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_177])).

cnf(c_39019,plain,
    ( m1_subset_1(k3_subset_1(X0,sK0(sK4,sK5)),k1_zfmisc_1(X0))
    | ~ r1_tarski(sK0(sK4,sK5),X0) ),
    inference(instantiation,[status(thm)],[c_218])).

cnf(c_39021,plain,
    ( m1_subset_1(k3_subset_1(sK3,sK0(sK4,sK5)),k1_zfmisc_1(sK3))
    | ~ r1_tarski(sK0(sK4,sK5),sK3) ),
    inference(instantiation,[status(thm)],[c_39019])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_16309,plain,
    ( ~ m1_subset_1(k3_subset_1(X0,sK0(sK4,sK5)),k1_zfmisc_1(X0))
    | r1_tarski(k3_subset_1(X0,sK0(sK4,sK5)),X0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_16311,plain,
    ( ~ m1_subset_1(k3_subset_1(sK3,sK0(sK4,sK5)),k1_zfmisc_1(sK3))
    | r1_tarski(k3_subset_1(sK3,sK0(sK4,sK5)),sK3) ),
    inference(instantiation,[status(thm)],[c_16309])).

cnf(c_799,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2969,plain,
    ( X0 != X1
    | sK0(sK4,sK5) != X1
    | sK0(sK4,sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_799])).

cnf(c_5717,plain,
    ( X0 != sK0(sK4,sK5)
    | sK0(sK4,sK5) = X0
    | sK0(sK4,sK5) != sK0(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2969])).

cnf(c_13651,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,sK0(sK4,sK5))) != sK0(sK4,sK5)
    | sK0(sK4,sK5) = k3_subset_1(X0,k3_subset_1(X0,sK0(sK4,sK5)))
    | sK0(sK4,sK5) != sK0(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_5717])).

cnf(c_13652,plain,
    ( k3_subset_1(sK3,k3_subset_1(sK3,sK0(sK4,sK5))) != sK0(sK4,sK5)
    | sK0(sK4,sK5) = k3_subset_1(sK3,k3_subset_1(sK3,sK0(sK4,sK5)))
    | sK0(sK4,sK5) != sK0(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_13651])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r2_hidden(X0,k7_setfam_1(X1,X2))
    | ~ r2_hidden(k3_subset_1(X1,X0),X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_216,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r2_hidden(X2,k7_setfam_1(X1,X0))
    | ~ r2_hidden(k3_subset_1(X1,X2),X0)
    | ~ r1_tarski(X2,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_177])).

cnf(c_279,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r2_hidden(X2,k7_setfam_1(X1,X0))
    | ~ r2_hidden(k3_subset_1(X1,X2),X0)
    | ~ r1_tarski(X2,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_216,c_9])).

cnf(c_5339,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ r2_hidden(k3_subset_1(X0,k3_subset_1(X0,sK0(sK4,sK5))),sK4)
    | r2_hidden(k3_subset_1(X0,sK0(sK4,sK5)),k7_setfam_1(X0,sK4))
    | ~ r1_tarski(k3_subset_1(X0,sK0(sK4,sK5)),X0) ),
    inference(instantiation,[status(thm)],[c_279])).

cnf(c_5341,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | ~ r2_hidden(k3_subset_1(sK3,k3_subset_1(sK3,sK0(sK4,sK5))),sK4)
    | r2_hidden(k3_subset_1(sK3,sK0(sK4,sK5)),k7_setfam_1(sK3,sK4))
    | ~ r1_tarski(k3_subset_1(sK3,sK0(sK4,sK5)),sK3) ),
    inference(instantiation,[status(thm)],[c_5339])).

cnf(c_1678,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(sK4,sK5),sK4)
    | X0 != sK0(sK4,sK5)
    | X1 != sK4 ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_2108,plain,
    ( r2_hidden(k3_subset_1(X0,k3_subset_1(X0,sK0(sK4,sK5))),X1)
    | ~ r2_hidden(sK0(sK4,sK5),sK4)
    | X1 != sK4
    | k3_subset_1(X0,k3_subset_1(X0,sK0(sK4,sK5))) != sK0(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1678])).

cnf(c_3705,plain,
    ( r2_hidden(k3_subset_1(X0,k3_subset_1(X0,sK0(sK4,sK5))),sK4)
    | ~ r2_hidden(sK0(sK4,sK5),sK4)
    | k3_subset_1(X0,k3_subset_1(X0,sK0(sK4,sK5))) != sK0(sK4,sK5)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2108])).

cnf(c_3707,plain,
    ( r2_hidden(k3_subset_1(sK3,k3_subset_1(sK3,sK0(sK4,sK5))),sK4)
    | ~ r2_hidden(sK0(sK4,sK5),sK4)
    | k3_subset_1(sK3,k3_subset_1(sK3,sK0(sK4,sK5))) != sK0(sK4,sK5)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3705])).

cnf(c_798,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2965,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_798])).

cnf(c_2771,plain,
    ( ~ m1_subset_1(sK0(sK4,sK5),k1_zfmisc_1(X0))
    | r1_tarski(sK0(sK4,sK5),X0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2773,plain,
    ( ~ m1_subset_1(sK0(sK4,sK5),k1_zfmisc_1(sK3))
    | r1_tarski(sK0(sK4,sK5),sK3) ),
    inference(instantiation,[status(thm)],[c_2771])).

cnf(c_2119,plain,
    ( sK0(sK4,sK5) = sK0(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_798])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_219,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_177])).

cnf(c_2109,plain,
    ( ~ r1_tarski(sK0(sK4,sK5),X0)
    | k3_subset_1(X0,k3_subset_1(X0,sK0(sK4,sK5))) = sK0(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_219])).

cnf(c_2115,plain,
    ( ~ r1_tarski(sK0(sK4,sK5),sK3)
    | k3_subset_1(sK3,k3_subset_1(sK3,sK0(sK4,sK5))) = sK0(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2109])).

cnf(c_16,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1691,plain,
    ( m1_subset_1(sK0(sK4,sK5),X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | ~ r2_hidden(sK0(sK4,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1918,plain,
    ( m1_subset_1(sK0(sK4,sK5),k1_zfmisc_1(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | ~ r2_hidden(sK0(sK4,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_1691])).

cnf(c_1727,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_798])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_492,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_18])).

cnf(c_493,plain,
    ( ~ r2_hidden(sK0(sK4,sK5),sK5) ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_485,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_18])).

cnf(c_486,plain,
    ( r2_hidden(sK0(sK4,sK5),sK4) ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(k7_setfam_1(sK3,sK4),k7_setfam_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(cnf_transformation,[],[f60])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_79789,c_54701,c_49707,c_39021,c_16311,c_13652,c_5341,c_3707,c_2965,c_2773,c_2119,c_2115,c_1918,c_1727,c_493,c_486,c_19,c_20,c_21])).


%------------------------------------------------------------------------------
