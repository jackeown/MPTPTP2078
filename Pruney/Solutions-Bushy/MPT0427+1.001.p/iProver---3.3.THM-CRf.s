%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0427+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:16 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 131 expanded)
%              Number of clauses        :   31 (  33 expanded)
%              Number of leaves         :    9 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  232 ( 546 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( r2_hidden(X1,X0)
       => ( r2_hidden(X1,k8_setfam_1(X0,X2))
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
             => r2_hidden(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <=> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <=> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f9])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
          | ? [X3] :
              ( ~ r2_hidden(X1,X3)
              & r2_hidden(X3,X2) ) )
        & ( ! [X3] :
              ( r2_hidden(X1,X3)
              | ~ r2_hidden(X3,X2) )
          | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) ) )
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
          | ? [X3] :
              ( ~ r2_hidden(X1,X3)
              & r2_hidden(X3,X2) ) )
        & ( ! [X4] :
              ( r2_hidden(X1,X4)
              | ~ r2_hidden(X4,X2) )
          | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) ) )
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(X1,X3)
          & r2_hidden(X3,X2) )
     => ( ~ r2_hidden(X1,sK1(X1,X2))
        & r2_hidden(sK1(X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
          | ( ~ r2_hidden(X1,sK1(X1,X2))
            & r2_hidden(sK1(X1,X2),X2) ) )
        & ( ! [X4] :
              ( r2_hidden(X1,X4)
              | ~ r2_hidden(X4,X2) )
          | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) ) )
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k8_setfam_1(X0,X2))
      | r2_hidden(sK1(X1,X2),X2)
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X1,X4)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X1,k8_setfam_1(X0,X2))
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k8_setfam_1(X0,X2))
      | ~ r2_hidden(X1,sK1(X1,X2))
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f11])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ~ r1_tarski(k8_setfam_1(X0,sK4),k8_setfam_1(X0,X1))
        & r1_tarski(X1,sK4)
        & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(sK2,X2),k8_setfam_1(sK2,sK3))
          & r1_tarski(sK3,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK2))) )
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))
    & r1_tarski(sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f12,f23,f22])).

fof(f37,plain,(
    ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f24])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f36,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f35,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f34,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_534,plain,
    ( ~ r2_hidden(sK1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),X0),X0)
    | r2_hidden(sK1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),X0),X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2925,plain,
    ( ~ r2_hidden(sK1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK3),sK3)
    | r2_hidden(sK1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK3),sK4)
    | ~ r1_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_534])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X2,X1)
    | r2_hidden(X2,k8_setfam_1(X1,X0))
    | r2_hidden(sK1(X2,X0),X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_409,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r2_hidden(sK1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),X0),X0)
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),X1)
    | r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),k8_setfam_1(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2903,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | r2_hidden(sK1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK3),sK3)
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),X0)
    | r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),k8_setfam_1(X0,sK3)) ),
    inference(instantiation,[status(thm)],[c_409])).

cnf(c_2905,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | r2_hidden(sK1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK3),sK3)
    | r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),k8_setfam_1(sK2,sK3))
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK2) ),
    inference(instantiation,[status(thm)],[c_2903])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X3,X0)
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k8_setfam_1(X1,X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_408,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),X1)
    | r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),X2)
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),k8_setfam_1(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_559,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(sK1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),X2),X0)
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),X1)
    | r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),X2))
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),k8_setfam_1(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_408])).

cnf(c_739,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | ~ r2_hidden(sK1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),X0),sK4)
    | r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),X0))
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),k8_setfam_1(sK2,sK4))
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK2) ),
    inference(instantiation,[status(thm)],[c_559])).

cnf(c_1614,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | ~ r2_hidden(sK1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK3),sK4)
    | r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK3))
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),k8_setfam_1(sK2,sK4))
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK2) ),
    inference(instantiation,[status(thm)],[c_739])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,sK1(X2,X0))
    | r2_hidden(X2,k8_setfam_1(X1,X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_410,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),X1)
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),X0))
    | r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),k8_setfam_1(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1028,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK3))
    | r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),k8_setfam_1(sK2,sK3))
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK2) ),
    inference(instantiation,[status(thm)],[c_410])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_387,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(X0))
    | r1_tarski(k8_setfam_1(sK2,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_389,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2))
    | r1_tarski(k8_setfam_1(sK2,sK4),sK2) ),
    inference(instantiation,[status(thm)],[c_387])).

cnf(c_350,plain,
    ( r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),X0)
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),k8_setfam_1(sK2,sK4))
    | ~ r1_tarski(k8_setfam_1(sK2,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_352,plain,
    ( ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),k8_setfam_1(sK2,sK4))
    | r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK2)
    | ~ r1_tarski(k8_setfam_1(sK2,sK4),sK2) ),
    inference(instantiation,[status(thm)],[c_350])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_343,plain,
    ( m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_235,plain,
    ( ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),k8_setfam_1(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_0,c_9])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_229,plain,
    ( r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),k8_setfam_1(sK2,sK4)) ),
    inference(resolution,[status(thm)],[c_1,c_9])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f34])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2925,c_2905,c_1614,c_1028,c_389,c_352,c_343,c_235,c_229,c_10,c_11,c_12])).


%------------------------------------------------------------------------------
