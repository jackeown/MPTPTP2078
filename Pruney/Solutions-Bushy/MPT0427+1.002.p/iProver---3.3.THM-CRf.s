%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0427+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:16 EST 2020

% Result     : Theorem 1.47s
% Output     : CNFRefutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 134 expanded)
%              Number of clauses        :   34 (  35 expanded)
%              Number of leaves         :   11 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  268 ( 548 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( r2_hidden(X1,X0)
       => ( r2_hidden(X1,k8_setfam_1(X0,X2))
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
             => r2_hidden(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <=> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <=> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f15])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(X1,X3)
          & r2_hidden(X3,X2) )
     => ( ~ r2_hidden(X1,sK1(X1,X2))
        & r2_hidden(sK1(X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X1,X4)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X1,k8_setfam_1(X0,X2))
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k8_setfam_1(X0,X2))
      | ~ r2_hidden(X1,sK1(X1,X2))
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k8_setfam_1(X0,X2))
      | r2_hidden(sK1(X1,X2),X2)
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f18])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ~ r1_tarski(k8_setfam_1(X0,sK4),k8_setfam_1(X0,X1))
        & r1_tarski(X1,sK4)
        & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
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

fof(f30,plain,
    ( ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))
    & r1_tarski(sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f29,f28])).

fof(f44,plain,(
    ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f42,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f30])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X3,X0)
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k8_setfam_1(X1,X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_346,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),X1)
    | r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),X2)
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),k8_setfam_1(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_902,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(sK1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),X2),X0)
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),X1)
    | r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),X2))
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),k8_setfam_1(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_346])).

cnf(c_1539,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(sK1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK3),X0)
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),X1)
    | r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK3))
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),k8_setfam_1(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_902])).

cnf(c_2295,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | ~ r2_hidden(sK1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK3),sK4)
    | r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK3))
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),k8_setfam_1(sK2,sK4))
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK2) ),
    inference(instantiation,[status(thm)],[c_1539])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,sK1(X2,X0))
    | r2_hidden(X2,k8_setfam_1(X1,X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_348,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),X1)
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),X0))
    | r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),k8_setfam_1(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1284,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK3))
    | r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),k8_setfam_1(sK2,sK3))
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK2) ),
    inference(instantiation,[status(thm)],[c_348])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_786,plain,
    ( r2_hidden(sK1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK3),X0)
    | ~ r2_hidden(sK1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK3),sK3)
    | ~ r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1112,plain,
    ( ~ r2_hidden(sK1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK3),sK3)
    | r2_hidden(sK1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK3),sK4)
    | ~ r1_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_786])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_717,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(X0))
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),k8_setfam_1(sK2,sK4))
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_719,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2))
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),k8_setfam_1(sK2,sK4))
    | ~ v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_717])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X2,X1)
    | r2_hidden(X2,k8_setfam_1(X1,X0))
    | r2_hidden(sK1(X2,X0),X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_347,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r2_hidden(sK1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),X0),X0)
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),X1)
    | r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),k8_setfam_1(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_595,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | r2_hidden(sK1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK3),sK3)
    | r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),k8_setfam_1(sK2,sK3))
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK2) ),
    inference(instantiation,[status(thm)],[c_347])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_376,plain,
    ( ~ m1_subset_1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),X0)
    | r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),X0)
    | v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_378,plain,
    ( ~ m1_subset_1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK2)
    | r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK2)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_376])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_300,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(X0))
    | m1_subset_1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),X0)
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),k8_setfam_1(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_302,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2))
    | m1_subset_1(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),sK2)
    | ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),k8_setfam_1(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_300])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_283,plain,
    ( m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_194,plain,
    ( ~ r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),k8_setfam_1(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_0,c_10])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_188,plain,
    ( r2_hidden(sK0(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)),k8_setfam_1(sK2,sK4)) ),
    inference(resolution,[status(thm)],[c_1,c_10])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f41])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2295,c_1284,c_1112,c_719,c_595,c_378,c_302,c_283,c_194,c_188,c_11,c_12,c_13])).


%------------------------------------------------------------------------------
