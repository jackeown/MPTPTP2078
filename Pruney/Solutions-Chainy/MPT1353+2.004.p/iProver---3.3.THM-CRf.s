%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:53 EST 2020

% Result     : Theorem 0.96s
% Output     : CNFRefutation 0.96s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 251 expanded)
%              Number of clauses        :   66 (  76 expanded)
%              Number of leaves         :   11 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :  431 (1263 expanded)
%              Number of equality atoms :   54 (  54 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v1_tops_2(X1,X0)
            <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_2(X1,X0)
          <~> r1_tarski(X1,u1_pre_topc(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,u1_pre_topc(X0))
            | ~ v1_tops_2(X1,X0) )
          & ( r1_tarski(X1,u1_pre_topc(X0))
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,u1_pre_topc(X0))
            | ~ v1_tops_2(X1,X0) )
          & ( r1_tarski(X1,u1_pre_topc(X0))
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,u1_pre_topc(X0))
            | ~ v1_tops_2(X1,X0) )
          & ( r1_tarski(X1,u1_pre_topc(X0))
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ( ~ r1_tarski(sK3,u1_pre_topc(X0))
          | ~ v1_tops_2(sK3,X0) )
        & ( r1_tarski(sK3,u1_pre_topc(X0))
          | v1_tops_2(sK3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | v1_tops_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(X1,u1_pre_topc(sK2))
            | ~ v1_tops_2(X1,sK2) )
          & ( r1_tarski(X1,u1_pre_topc(sK2))
            | v1_tops_2(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( ~ r1_tarski(sK3,u1_pre_topc(sK2))
      | ~ v1_tops_2(sK3,sK2) )
    & ( r1_tarski(sK3,u1_pre_topc(sK2))
      | v1_tops_2(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f28,f27])).

fof(f43,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
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
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK1(X0,X1),X0)
        & r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ( ~ v3_pre_topc(sK1(X0,X1),X0)
                & r2_hidden(sK1(X0,X1),X1)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f10])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK0(X0,X1,X2),X2)
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK0(X0,X1,X2),X2)
            & r2_hidden(sK0(X0,X1,X2),X1)
            & m1_subset_1(sK0(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f17])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,
    ( ~ r1_tarski(sK3,u1_pre_topc(sK2))
    | ~ v1_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | r2_hidden(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v3_pre_topc(sK1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2))
    | v1_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_7,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_284,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0,u1_pre_topc(sK2)) ),
    inference(resolution,[status(thm)],[c_7,c_16])).

cnf(c_1402,plain,
    ( ~ v3_pre_topc(X0_41,sK2)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0_41,u1_pre_topc(sK2)) ),
    inference(subtyping,[status(esa)],[c_284])).

cnf(c_2136,plain,
    ( ~ v3_pre_topc(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),sK2)
    | ~ m1_subset_1(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_1402])).

cnf(c_2137,plain,
    ( v3_pre_topc(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),sK2) != iProver_top
    | m1_subset_1(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),u1_pre_topc(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2136])).

cnf(c_6,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_298,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,u1_pre_topc(sK2)) ),
    inference(resolution,[status(thm)],[c_6,c_16])).

cnf(c_1401,plain,
    ( v3_pre_topc(X0_41,sK2)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0_41,u1_pre_topc(sK2)) ),
    inference(subtyping,[status(esa)],[c_298])).

cnf(c_1955,plain,
    ( v3_pre_topc(sK1(sK2,X0_41),sK2)
    | ~ m1_subset_1(sK1(sK2,X0_41),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK1(sK2,X0_41),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_1401])).

cnf(c_1960,plain,
    ( v3_pre_topc(sK1(sK2,X0_41),sK2) = iProver_top
    | m1_subset_1(sK1(sK2,X0_41),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK1(sK2,X0_41),u1_pre_topc(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1955])).

cnf(c_1962,plain,
    ( v3_pre_topc(sK1(sK2,sK3),sK2) = iProver_top
    | m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK1(sK2,sK3),u1_pre_topc(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1960])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_127,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_166,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_0,c_127])).

cnf(c_1407,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | ~ r2_hidden(X2_41,X0_41)
    | r2_hidden(X2_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_166])).

cnf(c_1818,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | ~ r2_hidden(sK1(sK2,X0_41),X0_41)
    | r2_hidden(sK1(sK2,X0_41),X1_41) ),
    inference(instantiation,[status(thm)],[c_1407])).

cnf(c_1954,plain,
    ( ~ r1_tarski(X0_41,u1_pre_topc(sK2))
    | ~ r2_hidden(sK1(sK2,X0_41),X0_41)
    | r2_hidden(sK1(sK2,X0_41),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_1818])).

cnf(c_1956,plain,
    ( r1_tarski(X0_41,u1_pre_topc(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,X0_41),X0_41) != iProver_top
    | r2_hidden(sK1(sK2,X0_41),u1_pre_topc(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1954])).

cnf(c_1958,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,sK3),u1_pre_topc(sK2)) = iProver_top
    | r2_hidden(sK1(sK2,sK3),sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1956])).

cnf(c_12,plain,
    ( ~ v1_tops_2(X0,X1)
    | v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r2_hidden(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_222,plain,
    ( ~ v1_tops_2(X0,sK2)
    | v3_pre_topc(X1,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ r2_hidden(X1,X0) ),
    inference(resolution,[status(thm)],[c_12,c_16])).

cnf(c_1406,plain,
    ( ~ v1_tops_2(X0_41,sK2)
    | v3_pre_topc(X1_41,sK2)
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ r2_hidden(X1_41,X0_41) ),
    inference(subtyping,[status(esa)],[c_222])).

cnf(c_1544,plain,
    ( ~ v1_tops_2(X0_41,sK2)
    | v3_pre_topc(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,X1_41),sK2)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ m1_subset_1(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,X1_41),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,X1_41),X0_41) ),
    inference(instantiation,[status(thm)],[c_1406])).

cnf(c_1711,plain,
    ( ~ v1_tops_2(X0_41,sK2)
    | v3_pre_topc(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),sK2)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ m1_subset_1(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),X0_41) ),
    inference(instantiation,[status(thm)],[c_1544])).

cnf(c_1712,plain,
    ( v1_tops_2(X0_41,sK2) != iProver_top
    | v3_pre_topc(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),sK2) = iProver_top
    | m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1711])).

cnf(c_1714,plain,
    ( v1_tops_2(sK3,sK2) != iProver_top
    | v3_pre_topc(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),sK2) = iProver_top
    | m1_subset_1(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | r2_hidden(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1712])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | r2_hidden(sK0(X2,X0,X1),X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1414,plain,
    ( r1_tarski(X0_41,X1_41)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(X2_41))
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(X2_41))
    | r2_hidden(sK0(X2_41,X0_41,X1_41),X0_41) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1518,plain,
    ( r1_tarski(sK3,X0_41)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | r2_hidden(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,X0_41),sK3) ),
    inference(instantiation,[status(thm)],[c_1414])).

cnf(c_1606,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2))
    | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | r2_hidden(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),sK3) ),
    inference(instantiation,[status(thm)],[c_1518])).

cnf(c_1607,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2)) = iProver_top
    | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | r2_hidden(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1606])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | m1_subset_1(sK0(X2,X0,X1),X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1413,plain,
    ( r1_tarski(X0_41,X1_41)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(X2_41))
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(X2_41))
    | m1_subset_1(sK0(X2_41,X0_41,X1_41),X2_41) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1580,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2))
    | m1_subset_1(sK0(X0_41,sK3,u1_pre_topc(sK2)),X0_41)
    | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(X0_41))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X0_41)) ),
    inference(instantiation,[status(thm)],[c_1413])).

cnf(c_1598,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2))
    | m1_subset_1(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(instantiation,[status(thm)],[c_1580])).

cnf(c_1599,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2)) = iProver_top
    | m1_subset_1(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1598])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(sK0(X2,X0,X1),X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1415,plain,
    ( r1_tarski(X0_41,X1_41)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(X2_41))
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(X2_41))
    | ~ r2_hidden(sK0(X2_41,X0_41,X1_41),X1_41) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1528,plain,
    ( r1_tarski(sK3,X0_41)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ r2_hidden(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,X0_41),X0_41) ),
    inference(instantiation,[status(thm)],[c_1415])).

cnf(c_1569,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2))
    | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ r2_hidden(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_1528])).

cnf(c_1570,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2)) = iProver_top
    | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | r2_hidden(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),u1_pre_topc(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1569])).

cnf(c_13,negated_conjecture,
    ( ~ v1_tops_2(sK3,sK2)
    | ~ r1_tarski(sK3,u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_129,plain,
    ( ~ v1_tops_2(sK3,sK2)
    | ~ r1_tarski(sK3,u1_pre_topc(sK2)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_11,plain,
    ( v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_242,plain,
    ( v1_tops_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[status(thm)],[c_11,c_16])).

cnf(c_531,plain,
    ( ~ r1_tarski(sK3,u1_pre_topc(sK2))
    | m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(resolution,[status(thm)],[c_129,c_242])).

cnf(c_532,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_531])).

cnf(c_10,plain,
    ( v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(sK1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_256,plain,
    ( v1_tops_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | r2_hidden(sK1(sK2,X0),X0) ),
    inference(resolution,[status(thm)],[c_10,c_16])).

cnf(c_518,plain,
    ( ~ r1_tarski(sK3,u1_pre_topc(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | r2_hidden(sK1(sK2,sK3),sK3) ),
    inference(resolution,[status(thm)],[c_129,c_256])).

cnf(c_519,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | r2_hidden(sK1(sK2,sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_518])).

cnf(c_9,plain,
    ( v1_tops_2(X0,X1)
    | ~ v3_pre_topc(sK1(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_270,plain,
    ( v1_tops_2(X0,sK2)
    | ~ v3_pre_topc(sK1(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(resolution,[status(thm)],[c_9,c_16])).

cnf(c_505,plain,
    ( ~ v3_pre_topc(sK1(sK2,sK3),sK2)
    | ~ r1_tarski(sK3,u1_pre_topc(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(resolution,[status(thm)],[c_129,c_270])).

cnf(c_506,plain,
    ( v3_pre_topc(sK1(sK2,sK3),sK2) != iProver_top
    | r1_tarski(sK3,u1_pre_topc(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_505])).

cnf(c_8,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_33,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_35,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_14,negated_conjecture,
    ( v1_tops_2(sK3,sK2)
    | r1_tarski(sK3,u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_19,plain,
    ( v1_tops_2(sK3,sK2) = iProver_top
    | r1_tarski(sK3,u1_pre_topc(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_18,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_17,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2137,c_1962,c_1958,c_1714,c_1607,c_1599,c_1570,c_532,c_519,c_506,c_35,c_19,c_18,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:07:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 0.96/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.96/0.99  
% 0.96/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.96/0.99  
% 0.96/0.99  ------  iProver source info
% 0.96/0.99  
% 0.96/0.99  git: date: 2020-06-30 10:37:57 +0100
% 0.96/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.96/0.99  git: non_committed_changes: false
% 0.96/0.99  git: last_make_outside_of_git: false
% 0.96/0.99  
% 0.96/0.99  ------ 
% 0.96/0.99  
% 0.96/0.99  ------ Input Options
% 0.96/0.99  
% 0.96/0.99  --out_options                           all
% 0.96/0.99  --tptp_safe_out                         true
% 0.96/0.99  --problem_path                          ""
% 0.96/0.99  --include_path                          ""
% 0.96/0.99  --clausifier                            res/vclausify_rel
% 0.96/0.99  --clausifier_options                    --mode clausify
% 0.96/0.99  --stdin                                 false
% 0.96/0.99  --stats_out                             all
% 0.96/0.99  
% 0.96/0.99  ------ General Options
% 0.96/0.99  
% 0.96/0.99  --fof                                   false
% 0.96/0.99  --time_out_real                         305.
% 0.96/0.99  --time_out_virtual                      -1.
% 0.96/0.99  --symbol_type_check                     false
% 0.96/0.99  --clausify_out                          false
% 0.96/0.99  --sig_cnt_out                           false
% 0.96/0.99  --trig_cnt_out                          false
% 0.96/0.99  --trig_cnt_out_tolerance                1.
% 0.96/0.99  --trig_cnt_out_sk_spl                   false
% 0.96/0.99  --abstr_cl_out                          false
% 0.96/0.99  
% 0.96/0.99  ------ Global Options
% 0.96/0.99  
% 0.96/0.99  --schedule                              default
% 0.96/0.99  --add_important_lit                     false
% 0.96/0.99  --prop_solver_per_cl                    1000
% 0.96/0.99  --min_unsat_core                        false
% 0.96/0.99  --soft_assumptions                      false
% 0.96/0.99  --soft_lemma_size                       3
% 0.96/0.99  --prop_impl_unit_size                   0
% 0.96/0.99  --prop_impl_unit                        []
% 0.96/0.99  --share_sel_clauses                     true
% 0.96/0.99  --reset_solvers                         false
% 0.96/0.99  --bc_imp_inh                            [conj_cone]
% 0.96/0.99  --conj_cone_tolerance                   3.
% 0.96/0.99  --extra_neg_conj                        none
% 0.96/0.99  --large_theory_mode                     true
% 0.96/0.99  --prolific_symb_bound                   200
% 0.96/0.99  --lt_threshold                          2000
% 0.96/0.99  --clause_weak_htbl                      true
% 0.96/0.99  --gc_record_bc_elim                     false
% 0.96/0.99  
% 0.96/0.99  ------ Preprocessing Options
% 0.96/0.99  
% 0.96/0.99  --preprocessing_flag                    true
% 0.96/0.99  --time_out_prep_mult                    0.1
% 0.96/0.99  --splitting_mode                        input
% 0.96/0.99  --splitting_grd                         true
% 0.96/0.99  --splitting_cvd                         false
% 0.96/0.99  --splitting_cvd_svl                     false
% 0.96/0.99  --splitting_nvd                         32
% 0.96/0.99  --sub_typing                            true
% 0.96/0.99  --prep_gs_sim                           true
% 0.96/0.99  --prep_unflatten                        true
% 0.96/0.99  --prep_res_sim                          true
% 0.96/0.99  --prep_upred                            true
% 0.96/0.99  --prep_sem_filter                       exhaustive
% 0.96/0.99  --prep_sem_filter_out                   false
% 0.96/0.99  --pred_elim                             true
% 0.96/0.99  --res_sim_input                         true
% 0.96/0.99  --eq_ax_congr_red                       true
% 0.96/0.99  --pure_diseq_elim                       true
% 0.96/0.99  --brand_transform                       false
% 0.96/0.99  --non_eq_to_eq                          false
% 0.96/0.99  --prep_def_merge                        true
% 0.96/0.99  --prep_def_merge_prop_impl              false
% 0.96/0.99  --prep_def_merge_mbd                    true
% 0.96/0.99  --prep_def_merge_tr_red                 false
% 0.96/0.99  --prep_def_merge_tr_cl                  false
% 0.96/0.99  --smt_preprocessing                     true
% 0.96/0.99  --smt_ac_axioms                         fast
% 0.96/0.99  --preprocessed_out                      false
% 0.96/0.99  --preprocessed_stats                    false
% 0.96/0.99  
% 0.96/0.99  ------ Abstraction refinement Options
% 0.96/0.99  
% 0.96/0.99  --abstr_ref                             []
% 0.96/0.99  --abstr_ref_prep                        false
% 0.96/0.99  --abstr_ref_until_sat                   false
% 0.96/0.99  --abstr_ref_sig_restrict                funpre
% 0.96/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 0.96/0.99  --abstr_ref_under                       []
% 0.96/0.99  
% 0.96/0.99  ------ SAT Options
% 0.96/0.99  
% 0.96/0.99  --sat_mode                              false
% 0.96/0.99  --sat_fm_restart_options                ""
% 0.96/0.99  --sat_gr_def                            false
% 0.96/0.99  --sat_epr_types                         true
% 0.96/0.99  --sat_non_cyclic_types                  false
% 0.96/0.99  --sat_finite_models                     false
% 0.96/0.99  --sat_fm_lemmas                         false
% 0.96/0.99  --sat_fm_prep                           false
% 0.96/0.99  --sat_fm_uc_incr                        true
% 0.96/0.99  --sat_out_model                         small
% 0.96/0.99  --sat_out_clauses                       false
% 0.96/0.99  
% 0.96/0.99  ------ QBF Options
% 0.96/0.99  
% 0.96/0.99  --qbf_mode                              false
% 0.96/0.99  --qbf_elim_univ                         false
% 0.96/0.99  --qbf_dom_inst                          none
% 0.96/0.99  --qbf_dom_pre_inst                      false
% 0.96/0.99  --qbf_sk_in                             false
% 0.96/0.99  --qbf_pred_elim                         true
% 0.96/0.99  --qbf_split                             512
% 0.96/0.99  
% 0.96/0.99  ------ BMC1 Options
% 0.96/0.99  
% 0.96/0.99  --bmc1_incremental                      false
% 0.96/0.99  --bmc1_axioms                           reachable_all
% 0.96/0.99  --bmc1_min_bound                        0
% 0.96/0.99  --bmc1_max_bound                        -1
% 0.96/0.99  --bmc1_max_bound_default                -1
% 0.96/0.99  --bmc1_symbol_reachability              true
% 0.96/0.99  --bmc1_property_lemmas                  false
% 0.96/0.99  --bmc1_k_induction                      false
% 0.96/0.99  --bmc1_non_equiv_states                 false
% 0.96/0.99  --bmc1_deadlock                         false
% 0.96/0.99  --bmc1_ucm                              false
% 0.96/0.99  --bmc1_add_unsat_core                   none
% 0.96/0.99  --bmc1_unsat_core_children              false
% 0.96/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 0.96/0.99  --bmc1_out_stat                         full
% 0.96/0.99  --bmc1_ground_init                      false
% 0.96/0.99  --bmc1_pre_inst_next_state              false
% 0.96/0.99  --bmc1_pre_inst_state                   false
% 0.96/0.99  --bmc1_pre_inst_reach_state             false
% 0.96/0.99  --bmc1_out_unsat_core                   false
% 0.96/0.99  --bmc1_aig_witness_out                  false
% 0.96/0.99  --bmc1_verbose                          false
% 0.96/0.99  --bmc1_dump_clauses_tptp                false
% 0.96/0.99  --bmc1_dump_unsat_core_tptp             false
% 0.96/0.99  --bmc1_dump_file                        -
% 0.96/0.99  --bmc1_ucm_expand_uc_limit              128
% 0.96/0.99  --bmc1_ucm_n_expand_iterations          6
% 0.96/0.99  --bmc1_ucm_extend_mode                  1
% 0.96/0.99  --bmc1_ucm_init_mode                    2
% 0.96/0.99  --bmc1_ucm_cone_mode                    none
% 0.96/0.99  --bmc1_ucm_reduced_relation_type        0
% 0.96/0.99  --bmc1_ucm_relax_model                  4
% 0.96/0.99  --bmc1_ucm_full_tr_after_sat            true
% 0.96/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 0.96/0.99  --bmc1_ucm_layered_model                none
% 0.96/0.99  --bmc1_ucm_max_lemma_size               10
% 0.96/0.99  
% 0.96/0.99  ------ AIG Options
% 0.96/0.99  
% 0.96/0.99  --aig_mode                              false
% 0.96/0.99  
% 0.96/0.99  ------ Instantiation Options
% 0.96/0.99  
% 0.96/0.99  --instantiation_flag                    true
% 0.96/0.99  --inst_sos_flag                         false
% 0.96/0.99  --inst_sos_phase                        true
% 0.96/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.96/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.96/0.99  --inst_lit_sel_side                     num_symb
% 0.96/0.99  --inst_solver_per_active                1400
% 0.96/0.99  --inst_solver_calls_frac                1.
% 0.96/0.99  --inst_passive_queue_type               priority_queues
% 0.96/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.96/0.99  --inst_passive_queues_freq              [25;2]
% 0.96/0.99  --inst_dismatching                      true
% 0.96/0.99  --inst_eager_unprocessed_to_passive     true
% 0.96/0.99  --inst_prop_sim_given                   true
% 0.96/0.99  --inst_prop_sim_new                     false
% 0.96/0.99  --inst_subs_new                         false
% 0.96/0.99  --inst_eq_res_simp                      false
% 0.96/0.99  --inst_subs_given                       false
% 0.96/0.99  --inst_orphan_elimination               true
% 0.96/0.99  --inst_learning_loop_flag               true
% 0.96/0.99  --inst_learning_start                   3000
% 0.96/0.99  --inst_learning_factor                  2
% 0.96/0.99  --inst_start_prop_sim_after_learn       3
% 0.96/0.99  --inst_sel_renew                        solver
% 0.96/0.99  --inst_lit_activity_flag                true
% 0.96/0.99  --inst_restr_to_given                   false
% 0.96/0.99  --inst_activity_threshold               500
% 0.96/0.99  --inst_out_proof                        true
% 0.96/0.99  
% 0.96/0.99  ------ Resolution Options
% 0.96/0.99  
% 0.96/0.99  --resolution_flag                       true
% 0.96/0.99  --res_lit_sel                           adaptive
% 0.96/0.99  --res_lit_sel_side                      none
% 0.96/0.99  --res_ordering                          kbo
% 0.96/0.99  --res_to_prop_solver                    active
% 0.96/0.99  --res_prop_simpl_new                    false
% 0.96/0.99  --res_prop_simpl_given                  true
% 0.96/0.99  --res_passive_queue_type                priority_queues
% 0.96/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.96/0.99  --res_passive_queues_freq               [15;5]
% 0.96/0.99  --res_forward_subs                      full
% 0.96/0.99  --res_backward_subs                     full
% 0.96/0.99  --res_forward_subs_resolution           true
% 0.96/0.99  --res_backward_subs_resolution          true
% 0.96/0.99  --res_orphan_elimination                true
% 0.96/0.99  --res_time_limit                        2.
% 0.96/0.99  --res_out_proof                         true
% 0.96/0.99  
% 0.96/0.99  ------ Superposition Options
% 0.96/0.99  
% 0.96/0.99  --superposition_flag                    true
% 0.96/0.99  --sup_passive_queue_type                priority_queues
% 0.96/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.96/0.99  --sup_passive_queues_freq               [8;1;4]
% 0.96/0.99  --demod_completeness_check              fast
% 0.96/0.99  --demod_use_ground                      true
% 0.96/0.99  --sup_to_prop_solver                    passive
% 0.96/0.99  --sup_prop_simpl_new                    true
% 0.96/0.99  --sup_prop_simpl_given                  true
% 0.96/0.99  --sup_fun_splitting                     false
% 0.96/0.99  --sup_smt_interval                      50000
% 0.96/0.99  
% 0.96/0.99  ------ Superposition Simplification Setup
% 0.96/0.99  
% 0.96/0.99  --sup_indices_passive                   []
% 0.96/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 0.96/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/0.99  --sup_full_bw                           [BwDemod]
% 0.96/0.99  --sup_immed_triv                        [TrivRules]
% 0.96/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.96/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/0.99  --sup_immed_bw_main                     []
% 0.96/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.96/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 0.96/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.96/0.99  
% 0.96/0.99  ------ Combination Options
% 0.96/0.99  
% 0.96/0.99  --comb_res_mult                         3
% 0.96/0.99  --comb_sup_mult                         2
% 0.96/0.99  --comb_inst_mult                        10
% 0.96/0.99  
% 0.96/0.99  ------ Debug Options
% 0.96/0.99  
% 0.96/0.99  --dbg_backtrace                         false
% 0.96/0.99  --dbg_dump_prop_clauses                 false
% 0.96/0.99  --dbg_dump_prop_clauses_file            -
% 0.96/0.99  --dbg_out_stat                          false
% 0.96/0.99  ------ Parsing...
% 0.96/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.96/0.99  
% 0.96/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 0.96/0.99  
% 0.96/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.96/0.99  ------ Proving...
% 0.96/0.99  ------ Problem Properties 
% 0.96/0.99  
% 0.96/0.99  
% 0.96/0.99  clauses                                 16
% 0.96/0.99  conjectures                             3
% 0.96/0.99  EPR                                     1
% 0.96/0.99  Horn                                    11
% 0.96/0.99  unary                                   2
% 0.96/0.99  binary                                  4
% 0.96/0.99  lits                                    45
% 0.96/0.99  lits eq                                 0
% 0.96/0.99  fd_pure                                 0
% 0.96/0.99  fd_pseudo                               0
% 0.96/0.99  fd_cond                                 0
% 0.96/0.99  fd_pseudo_cond                          0
% 0.96/0.99  AC symbols                              0
% 0.96/0.99  
% 0.96/0.99  ------ Schedule dynamic 5 is on 
% 0.96/0.99  
% 0.96/0.99  ------ no equalities: superposition off 
% 0.96/0.99  
% 0.96/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.96/0.99  
% 0.96/0.99  
% 0.96/0.99  ------ 
% 0.96/0.99  Current options:
% 0.96/0.99  ------ 
% 0.96/0.99  
% 0.96/0.99  ------ Input Options
% 0.96/0.99  
% 0.96/0.99  --out_options                           all
% 0.96/0.99  --tptp_safe_out                         true
% 0.96/0.99  --problem_path                          ""
% 0.96/0.99  --include_path                          ""
% 0.96/0.99  --clausifier                            res/vclausify_rel
% 0.96/0.99  --clausifier_options                    --mode clausify
% 0.96/0.99  --stdin                                 false
% 0.96/0.99  --stats_out                             all
% 0.96/0.99  
% 0.96/0.99  ------ General Options
% 0.96/0.99  
% 0.96/0.99  --fof                                   false
% 0.96/0.99  --time_out_real                         305.
% 0.96/0.99  --time_out_virtual                      -1.
% 0.96/0.99  --symbol_type_check                     false
% 0.96/0.99  --clausify_out                          false
% 0.96/0.99  --sig_cnt_out                           false
% 0.96/0.99  --trig_cnt_out                          false
% 0.96/0.99  --trig_cnt_out_tolerance                1.
% 0.96/0.99  --trig_cnt_out_sk_spl                   false
% 0.96/0.99  --abstr_cl_out                          false
% 0.96/0.99  
% 0.96/0.99  ------ Global Options
% 0.96/0.99  
% 0.96/0.99  --schedule                              default
% 0.96/0.99  --add_important_lit                     false
% 0.96/0.99  --prop_solver_per_cl                    1000
% 0.96/0.99  --min_unsat_core                        false
% 0.96/0.99  --soft_assumptions                      false
% 0.96/0.99  --soft_lemma_size                       3
% 0.96/0.99  --prop_impl_unit_size                   0
% 0.96/0.99  --prop_impl_unit                        []
% 0.96/0.99  --share_sel_clauses                     true
% 0.96/0.99  --reset_solvers                         false
% 0.96/0.99  --bc_imp_inh                            [conj_cone]
% 0.96/0.99  --conj_cone_tolerance                   3.
% 0.96/0.99  --extra_neg_conj                        none
% 0.96/0.99  --large_theory_mode                     true
% 0.96/0.99  --prolific_symb_bound                   200
% 0.96/0.99  --lt_threshold                          2000
% 0.96/0.99  --clause_weak_htbl                      true
% 0.96/0.99  --gc_record_bc_elim                     false
% 0.96/0.99  
% 0.96/0.99  ------ Preprocessing Options
% 0.96/0.99  
% 0.96/0.99  --preprocessing_flag                    true
% 0.96/0.99  --time_out_prep_mult                    0.1
% 0.96/0.99  --splitting_mode                        input
% 0.96/0.99  --splitting_grd                         true
% 0.96/0.99  --splitting_cvd                         false
% 0.96/0.99  --splitting_cvd_svl                     false
% 0.96/0.99  --splitting_nvd                         32
% 0.96/0.99  --sub_typing                            true
% 0.96/0.99  --prep_gs_sim                           true
% 0.96/0.99  --prep_unflatten                        true
% 0.96/0.99  --prep_res_sim                          true
% 0.96/0.99  --prep_upred                            true
% 0.96/0.99  --prep_sem_filter                       exhaustive
% 0.96/0.99  --prep_sem_filter_out                   false
% 0.96/0.99  --pred_elim                             true
% 0.96/0.99  --res_sim_input                         true
% 0.96/0.99  --eq_ax_congr_red                       true
% 0.96/0.99  --pure_diseq_elim                       true
% 0.96/0.99  --brand_transform                       false
% 0.96/0.99  --non_eq_to_eq                          false
% 0.96/0.99  --prep_def_merge                        true
% 0.96/0.99  --prep_def_merge_prop_impl              false
% 0.96/0.99  --prep_def_merge_mbd                    true
% 0.96/0.99  --prep_def_merge_tr_red                 false
% 0.96/0.99  --prep_def_merge_tr_cl                  false
% 0.96/0.99  --smt_preprocessing                     true
% 0.96/0.99  --smt_ac_axioms                         fast
% 0.96/0.99  --preprocessed_out                      false
% 0.96/0.99  --preprocessed_stats                    false
% 0.96/0.99  
% 0.96/0.99  ------ Abstraction refinement Options
% 0.96/0.99  
% 0.96/0.99  --abstr_ref                             []
% 0.96/0.99  --abstr_ref_prep                        false
% 0.96/0.99  --abstr_ref_until_sat                   false
% 0.96/0.99  --abstr_ref_sig_restrict                funpre
% 0.96/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 0.96/0.99  --abstr_ref_under                       []
% 0.96/0.99  
% 0.96/0.99  ------ SAT Options
% 0.96/0.99  
% 0.96/0.99  --sat_mode                              false
% 0.96/0.99  --sat_fm_restart_options                ""
% 0.96/0.99  --sat_gr_def                            false
% 0.96/0.99  --sat_epr_types                         true
% 0.96/0.99  --sat_non_cyclic_types                  false
% 0.96/0.99  --sat_finite_models                     false
% 0.96/0.99  --sat_fm_lemmas                         false
% 0.96/0.99  --sat_fm_prep                           false
% 0.96/0.99  --sat_fm_uc_incr                        true
% 0.96/0.99  --sat_out_model                         small
% 0.96/0.99  --sat_out_clauses                       false
% 0.96/0.99  
% 0.96/0.99  ------ QBF Options
% 0.96/0.99  
% 0.96/0.99  --qbf_mode                              false
% 0.96/0.99  --qbf_elim_univ                         false
% 0.96/0.99  --qbf_dom_inst                          none
% 0.96/0.99  --qbf_dom_pre_inst                      false
% 0.96/0.99  --qbf_sk_in                             false
% 0.96/0.99  --qbf_pred_elim                         true
% 0.96/0.99  --qbf_split                             512
% 0.96/0.99  
% 0.96/0.99  ------ BMC1 Options
% 0.96/0.99  
% 0.96/0.99  --bmc1_incremental                      false
% 0.96/0.99  --bmc1_axioms                           reachable_all
% 0.96/0.99  --bmc1_min_bound                        0
% 0.96/0.99  --bmc1_max_bound                        -1
% 0.96/0.99  --bmc1_max_bound_default                -1
% 0.96/0.99  --bmc1_symbol_reachability              true
% 0.96/0.99  --bmc1_property_lemmas                  false
% 0.96/0.99  --bmc1_k_induction                      false
% 0.96/0.99  --bmc1_non_equiv_states                 false
% 0.96/0.99  --bmc1_deadlock                         false
% 0.96/0.99  --bmc1_ucm                              false
% 0.96/0.99  --bmc1_add_unsat_core                   none
% 0.96/0.99  --bmc1_unsat_core_children              false
% 0.96/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 0.96/0.99  --bmc1_out_stat                         full
% 0.96/0.99  --bmc1_ground_init                      false
% 0.96/0.99  --bmc1_pre_inst_next_state              false
% 0.96/0.99  --bmc1_pre_inst_state                   false
% 0.96/0.99  --bmc1_pre_inst_reach_state             false
% 0.96/0.99  --bmc1_out_unsat_core                   false
% 0.96/0.99  --bmc1_aig_witness_out                  false
% 0.96/0.99  --bmc1_verbose                          false
% 0.96/0.99  --bmc1_dump_clauses_tptp                false
% 0.96/0.99  --bmc1_dump_unsat_core_tptp             false
% 0.96/0.99  --bmc1_dump_file                        -
% 0.96/0.99  --bmc1_ucm_expand_uc_limit              128
% 0.96/0.99  --bmc1_ucm_n_expand_iterations          6
% 0.96/0.99  --bmc1_ucm_extend_mode                  1
% 0.96/0.99  --bmc1_ucm_init_mode                    2
% 0.96/0.99  --bmc1_ucm_cone_mode                    none
% 0.96/0.99  --bmc1_ucm_reduced_relation_type        0
% 0.96/0.99  --bmc1_ucm_relax_model                  4
% 0.96/0.99  --bmc1_ucm_full_tr_after_sat            true
% 0.96/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 0.96/0.99  --bmc1_ucm_layered_model                none
% 0.96/0.99  --bmc1_ucm_max_lemma_size               10
% 0.96/0.99  
% 0.96/0.99  ------ AIG Options
% 0.96/0.99  
% 0.96/0.99  --aig_mode                              false
% 0.96/0.99  
% 0.96/0.99  ------ Instantiation Options
% 0.96/0.99  
% 0.96/0.99  --instantiation_flag                    true
% 0.96/0.99  --inst_sos_flag                         false
% 0.96/0.99  --inst_sos_phase                        true
% 0.96/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.96/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.96/0.99  --inst_lit_sel_side                     none
% 0.96/0.99  --inst_solver_per_active                1400
% 0.96/0.99  --inst_solver_calls_frac                1.
% 0.96/0.99  --inst_passive_queue_type               priority_queues
% 0.96/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.96/0.99  --inst_passive_queues_freq              [25;2]
% 0.96/0.99  --inst_dismatching                      true
% 0.96/0.99  --inst_eager_unprocessed_to_passive     true
% 0.96/0.99  --inst_prop_sim_given                   true
% 0.96/0.99  --inst_prop_sim_new                     false
% 0.96/0.99  --inst_subs_new                         false
% 0.96/0.99  --inst_eq_res_simp                      false
% 0.96/0.99  --inst_subs_given                       false
% 0.96/0.99  --inst_orphan_elimination               true
% 0.96/0.99  --inst_learning_loop_flag               true
% 0.96/0.99  --inst_learning_start                   3000
% 0.96/0.99  --inst_learning_factor                  2
% 0.96/0.99  --inst_start_prop_sim_after_learn       3
% 0.96/0.99  --inst_sel_renew                        solver
% 0.96/0.99  --inst_lit_activity_flag                true
% 0.96/0.99  --inst_restr_to_given                   false
% 0.96/0.99  --inst_activity_threshold               500
% 0.96/0.99  --inst_out_proof                        true
% 0.96/0.99  
% 0.96/0.99  ------ Resolution Options
% 0.96/0.99  
% 0.96/0.99  --resolution_flag                       false
% 0.96/0.99  --res_lit_sel                           adaptive
% 0.96/0.99  --res_lit_sel_side                      none
% 0.96/0.99  --res_ordering                          kbo
% 0.96/0.99  --res_to_prop_solver                    active
% 0.96/0.99  --res_prop_simpl_new                    false
% 0.96/0.99  --res_prop_simpl_given                  true
% 0.96/0.99  --res_passive_queue_type                priority_queues
% 0.96/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.96/0.99  --res_passive_queues_freq               [15;5]
% 0.96/0.99  --res_forward_subs                      full
% 0.96/0.99  --res_backward_subs                     full
% 0.96/0.99  --res_forward_subs_resolution           true
% 0.96/0.99  --res_backward_subs_resolution          true
% 0.96/0.99  --res_orphan_elimination                true
% 0.96/0.99  --res_time_limit                        2.
% 0.96/0.99  --res_out_proof                         true
% 0.96/0.99  
% 0.96/0.99  ------ Superposition Options
% 0.96/0.99  
% 0.96/0.99  --superposition_flag                    false
% 0.96/0.99  --sup_passive_queue_type                priority_queues
% 0.96/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.96/0.99  --sup_passive_queues_freq               [8;1;4]
% 0.96/0.99  --demod_completeness_check              fast
% 0.96/0.99  --demod_use_ground                      true
% 0.96/0.99  --sup_to_prop_solver                    passive
% 0.96/0.99  --sup_prop_simpl_new                    true
% 0.96/0.99  --sup_prop_simpl_given                  true
% 0.96/0.99  --sup_fun_splitting                     false
% 0.96/0.99  --sup_smt_interval                      50000
% 0.96/0.99  
% 0.96/0.99  ------ Superposition Simplification Setup
% 0.96/0.99  
% 0.96/0.99  --sup_indices_passive                   []
% 0.96/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 0.96/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/0.99  --sup_full_bw                           [BwDemod]
% 0.96/0.99  --sup_immed_triv                        [TrivRules]
% 0.96/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.96/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/0.99  --sup_immed_bw_main                     []
% 0.96/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.96/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 0.96/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.96/0.99  
% 0.96/0.99  ------ Combination Options
% 0.96/0.99  
% 0.96/0.99  --comb_res_mult                         3
% 0.96/0.99  --comb_sup_mult                         2
% 0.96/0.99  --comb_inst_mult                        10
% 0.96/0.99  
% 0.96/0.99  ------ Debug Options
% 0.96/0.99  
% 0.96/0.99  --dbg_backtrace                         false
% 0.96/0.99  --dbg_dump_prop_clauses                 false
% 0.96/0.99  --dbg_dump_prop_clauses_file            -
% 0.96/0.99  --dbg_out_stat                          false
% 0.96/0.99  
% 0.96/0.99  
% 0.96/0.99  
% 0.96/0.99  
% 0.96/0.99  ------ Proving...
% 0.96/0.99  
% 0.96/0.99  
% 0.96/0.99  % SZS status Theorem for theBenchmark.p
% 0.96/0.99  
% 0.96/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 0.96/0.99  
% 0.96/0.99  fof(f4,axiom,(
% 0.96/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.96/0.99  
% 0.96/0.99  fof(f12,plain,(
% 0.96/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.96/0.99    inference(ennf_transformation,[],[f4])).
% 0.96/0.99  
% 0.96/0.99  fof(f20,plain,(
% 0.96/0.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.96/0.99    inference(nnf_transformation,[],[f12])).
% 0.96/0.99  
% 0.96/0.99  fof(f36,plain,(
% 0.96/0.99    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.96/0.99    inference(cnf_transformation,[],[f20])).
% 0.96/0.99  
% 0.96/0.99  fof(f7,conjecture,(
% 0.96/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 0.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.96/0.99  
% 0.96/0.99  fof(f8,negated_conjecture,(
% 0.96/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 0.96/0.99    inference(negated_conjecture,[],[f7])).
% 0.96/0.99  
% 0.96/0.99  fof(f16,plain,(
% 0.96/0.99    ? [X0] : (? [X1] : ((v1_tops_2(X1,X0) <~> r1_tarski(X1,u1_pre_topc(X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.96/0.99    inference(ennf_transformation,[],[f8])).
% 0.96/0.99  
% 0.96/0.99  fof(f25,plain,(
% 0.96/0.99    ? [X0] : (? [X1] : (((~r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0)) & (r1_tarski(X1,u1_pre_topc(X0)) | v1_tops_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.96/0.99    inference(nnf_transformation,[],[f16])).
% 0.96/0.99  
% 0.96/0.99  fof(f26,plain,(
% 0.96/0.99    ? [X0] : (? [X1] : ((~r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0)) & (r1_tarski(X1,u1_pre_topc(X0)) | v1_tops_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.96/0.99    inference(flattening,[],[f25])).
% 0.96/0.99  
% 0.96/0.99  fof(f28,plain,(
% 0.96/0.99    ( ! [X0] : (? [X1] : ((~r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0)) & (r1_tarski(X1,u1_pre_topc(X0)) | v1_tops_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => ((~r1_tarski(sK3,u1_pre_topc(X0)) | ~v1_tops_2(sK3,X0)) & (r1_tarski(sK3,u1_pre_topc(X0)) | v1_tops_2(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 0.96/0.99    introduced(choice_axiom,[])).
% 0.96/0.99  
% 0.96/0.99  fof(f27,plain,(
% 0.96/0.99    ? [X0] : (? [X1] : ((~r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0)) & (r1_tarski(X1,u1_pre_topc(X0)) | v1_tops_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : ((~r1_tarski(X1,u1_pre_topc(sK2)) | ~v1_tops_2(X1,sK2)) & (r1_tarski(X1,u1_pre_topc(sK2)) | v1_tops_2(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & l1_pre_topc(sK2))),
% 0.96/0.99    introduced(choice_axiom,[])).
% 0.96/0.99  
% 0.96/0.99  fof(f29,plain,(
% 0.96/0.99    ((~r1_tarski(sK3,u1_pre_topc(sK2)) | ~v1_tops_2(sK3,sK2)) & (r1_tarski(sK3,u1_pre_topc(sK2)) | v1_tops_2(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & l1_pre_topc(sK2)),
% 0.96/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f28,f27])).
% 0.96/0.99  
% 0.96/0.99  fof(f43,plain,(
% 0.96/0.99    l1_pre_topc(sK2)),
% 0.96/0.99    inference(cnf_transformation,[],[f29])).
% 0.96/0.99  
% 0.96/0.99  fof(f37,plain,(
% 0.96/0.99    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.96/0.99    inference(cnf_transformation,[],[f20])).
% 0.96/0.99  
% 0.96/0.99  fof(f1,axiom,(
% 0.96/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.96/0.99  
% 0.96/0.99  fof(f9,plain,(
% 0.96/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.96/0.99    inference(ennf_transformation,[],[f1])).
% 0.96/0.99  
% 0.96/0.99  fof(f30,plain,(
% 0.96/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.96/0.99    inference(cnf_transformation,[],[f9])).
% 0.96/0.99  
% 0.96/0.99  fof(f3,axiom,(
% 0.96/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.96/0.99  
% 0.96/0.99  fof(f19,plain,(
% 0.96/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.96/0.99    inference(nnf_transformation,[],[f3])).
% 0.96/0.99  
% 0.96/0.99  fof(f35,plain,(
% 0.96/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.96/0.99    inference(cnf_transformation,[],[f19])).
% 0.96/0.99  
% 0.96/0.99  fof(f6,axiom,(
% 0.96/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v3_pre_topc(X2,X0))))))),
% 0.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.96/0.99  
% 0.96/0.99  fof(f14,plain,(
% 0.96/0.99    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.96/0.99    inference(ennf_transformation,[],[f6])).
% 0.96/0.99  
% 0.96/0.99  fof(f15,plain,(
% 0.96/0.99    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.96/0.99    inference(flattening,[],[f14])).
% 0.96/0.99  
% 0.96/0.99  fof(f21,plain,(
% 0.96/0.99    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.96/0.99    inference(nnf_transformation,[],[f15])).
% 0.96/0.99  
% 0.96/0.99  fof(f22,plain,(
% 0.96/0.99    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.96/0.99    inference(rectify,[],[f21])).
% 0.96/0.99  
% 0.96/0.99  fof(f23,plain,(
% 0.96/0.99    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK1(X0,X1),X0) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.96/0.99    introduced(choice_axiom,[])).
% 0.96/0.99  
% 0.96/0.99  fof(f24,plain,(
% 0.96/0.99    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | (~v3_pre_topc(sK1(X0,X1),X0) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.96/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).
% 0.96/0.99  
% 0.96/0.99  fof(f39,plain,(
% 0.96/0.99    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.96/0.99    inference(cnf_transformation,[],[f24])).
% 0.96/0.99  
% 0.96/0.99  fof(f2,axiom,(
% 0.96/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.96/0.99  
% 0.96/0.99  fof(f10,plain,(
% 0.96/0.99    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.96/0.99    inference(ennf_transformation,[],[f2])).
% 0.96/0.99  
% 0.96/0.99  fof(f11,plain,(
% 0.96/0.99    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.96/0.99    inference(flattening,[],[f10])).
% 0.96/0.99  
% 0.96/0.99  fof(f17,plain,(
% 0.96/0.99    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),X0)))),
% 0.96/0.99    introduced(choice_axiom,[])).
% 0.96/0.99  
% 0.96/0.99  fof(f18,plain,(
% 0.96/0.99    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.96/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f17])).
% 0.96/0.99  
% 0.96/0.99  fof(f32,plain,(
% 0.96/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.96/0.99    inference(cnf_transformation,[],[f18])).
% 0.96/0.99  
% 0.96/0.99  fof(f31,plain,(
% 0.96/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | m1_subset_1(sK0(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.96/0.99    inference(cnf_transformation,[],[f18])).
% 0.96/0.99  
% 0.96/0.99  fof(f33,plain,(
% 0.96/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.96/0.99    inference(cnf_transformation,[],[f18])).
% 0.96/0.99  
% 0.96/0.99  fof(f46,plain,(
% 0.96/0.99    ~r1_tarski(sK3,u1_pre_topc(sK2)) | ~v1_tops_2(sK3,sK2)),
% 0.96/0.99    inference(cnf_transformation,[],[f29])).
% 0.96/0.99  
% 0.96/0.99  fof(f40,plain,(
% 0.96/0.99    ( ! [X0,X1] : (v1_tops_2(X1,X0) | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.96/0.99    inference(cnf_transformation,[],[f24])).
% 0.96/0.99  
% 0.96/0.99  fof(f41,plain,(
% 0.96/0.99    ( ! [X0,X1] : (v1_tops_2(X1,X0) | r2_hidden(sK1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.96/0.99    inference(cnf_transformation,[],[f24])).
% 0.96/0.99  
% 0.96/0.99  fof(f42,plain,(
% 0.96/0.99    ( ! [X0,X1] : (v1_tops_2(X1,X0) | ~v3_pre_topc(sK1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.96/0.99    inference(cnf_transformation,[],[f24])).
% 0.96/0.99  
% 0.96/0.99  fof(f5,axiom,(
% 0.96/0.99    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.96/0.99  
% 0.96/0.99  fof(f13,plain,(
% 0.96/0.99    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.96/0.99    inference(ennf_transformation,[],[f5])).
% 0.96/0.99  
% 0.96/0.99  fof(f38,plain,(
% 0.96/0.99    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.96/0.99    inference(cnf_transformation,[],[f13])).
% 0.96/0.99  
% 0.96/0.99  fof(f45,plain,(
% 0.96/0.99    r1_tarski(sK3,u1_pre_topc(sK2)) | v1_tops_2(sK3,sK2)),
% 0.96/0.99    inference(cnf_transformation,[],[f29])).
% 0.96/0.99  
% 0.96/0.99  fof(f44,plain,(
% 0.96/0.99    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.96/0.99    inference(cnf_transformation,[],[f29])).
% 0.96/0.99  
% 0.96/0.99  cnf(c_7,plain,
% 0.96/0.99      ( ~ v3_pre_topc(X0,X1)
% 0.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.96/0.99      | r2_hidden(X0,u1_pre_topc(X1))
% 0.96/0.99      | ~ l1_pre_topc(X1) ),
% 0.96/0.99      inference(cnf_transformation,[],[f36]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_16,negated_conjecture,
% 0.96/0.99      ( l1_pre_topc(sK2) ),
% 0.96/0.99      inference(cnf_transformation,[],[f43]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_284,plain,
% 0.96/0.99      ( ~ v3_pre_topc(X0,sK2)
% 0.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.96/0.99      | r2_hidden(X0,u1_pre_topc(sK2)) ),
% 0.96/0.99      inference(resolution,[status(thm)],[c_7,c_16]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_1402,plain,
% 0.96/0.99      ( ~ v3_pre_topc(X0_41,sK2)
% 0.96/0.99      | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.96/0.99      | r2_hidden(X0_41,u1_pre_topc(sK2)) ),
% 0.96/0.99      inference(subtyping,[status(esa)],[c_284]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_2136,plain,
% 0.96/0.99      ( ~ v3_pre_topc(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),sK2)
% 0.96/0.99      | ~ m1_subset_1(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.96/0.99      | r2_hidden(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),u1_pre_topc(sK2)) ),
% 0.96/0.99      inference(instantiation,[status(thm)],[c_1402]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_2137,plain,
% 0.96/0.99      ( v3_pre_topc(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),sK2) != iProver_top
% 0.96/0.99      | m1_subset_1(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 0.96/0.99      | r2_hidden(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),u1_pre_topc(sK2)) = iProver_top ),
% 0.96/0.99      inference(predicate_to_equality,[status(thm)],[c_2136]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_6,plain,
% 0.96/0.99      ( v3_pre_topc(X0,X1)
% 0.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.96/0.99      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 0.96/0.99      | ~ l1_pre_topc(X1) ),
% 0.96/0.99      inference(cnf_transformation,[],[f37]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_298,plain,
% 0.96/0.99      ( v3_pre_topc(X0,sK2)
% 0.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.96/0.99      | ~ r2_hidden(X0,u1_pre_topc(sK2)) ),
% 0.96/0.99      inference(resolution,[status(thm)],[c_6,c_16]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_1401,plain,
% 0.96/0.99      ( v3_pre_topc(X0_41,sK2)
% 0.96/0.99      | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.96/0.99      | ~ r2_hidden(X0_41,u1_pre_topc(sK2)) ),
% 0.96/0.99      inference(subtyping,[status(esa)],[c_298]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_1955,plain,
% 0.96/0.99      ( v3_pre_topc(sK1(sK2,X0_41),sK2)
% 0.96/0.99      | ~ m1_subset_1(sK1(sK2,X0_41),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.96/0.99      | ~ r2_hidden(sK1(sK2,X0_41),u1_pre_topc(sK2)) ),
% 0.96/0.99      inference(instantiation,[status(thm)],[c_1401]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_1960,plain,
% 0.96/0.99      ( v3_pre_topc(sK1(sK2,X0_41),sK2) = iProver_top
% 0.96/0.99      | m1_subset_1(sK1(sK2,X0_41),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 0.96/0.99      | r2_hidden(sK1(sK2,X0_41),u1_pre_topc(sK2)) != iProver_top ),
% 0.96/0.99      inference(predicate_to_equality,[status(thm)],[c_1955]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_1962,plain,
% 0.96/0.99      ( v3_pre_topc(sK1(sK2,sK3),sK2) = iProver_top
% 0.96/0.99      | m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 0.96/0.99      | r2_hidden(sK1(sK2,sK3),u1_pre_topc(sK2)) != iProver_top ),
% 0.96/0.99      inference(instantiation,[status(thm)],[c_1960]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_0,plain,
% 0.96/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.96/0.99      | ~ r2_hidden(X2,X0)
% 0.96/0.99      | r2_hidden(X2,X1) ),
% 0.96/0.99      inference(cnf_transformation,[],[f30]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_4,plain,
% 0.96/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 0.96/0.99      inference(cnf_transformation,[],[f35]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_127,plain,
% 0.96/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 0.96/0.99      inference(prop_impl,[status(thm)],[c_4]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_166,plain,
% 0.96/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 0.96/0.99      inference(bin_hyper_res,[status(thm)],[c_0,c_127]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_1407,plain,
% 0.96/0.99      ( ~ r1_tarski(X0_41,X1_41)
% 0.96/0.99      | ~ r2_hidden(X2_41,X0_41)
% 0.96/0.99      | r2_hidden(X2_41,X1_41) ),
% 0.96/0.99      inference(subtyping,[status(esa)],[c_166]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_1818,plain,
% 0.96/0.99      ( ~ r1_tarski(X0_41,X1_41)
% 0.96/0.99      | ~ r2_hidden(sK1(sK2,X0_41),X0_41)
% 0.96/0.99      | r2_hidden(sK1(sK2,X0_41),X1_41) ),
% 0.96/0.99      inference(instantiation,[status(thm)],[c_1407]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_1954,plain,
% 0.96/0.99      ( ~ r1_tarski(X0_41,u1_pre_topc(sK2))
% 0.96/0.99      | ~ r2_hidden(sK1(sK2,X0_41),X0_41)
% 0.96/0.99      | r2_hidden(sK1(sK2,X0_41),u1_pre_topc(sK2)) ),
% 0.96/0.99      inference(instantiation,[status(thm)],[c_1818]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_1956,plain,
% 0.96/0.99      ( r1_tarski(X0_41,u1_pre_topc(sK2)) != iProver_top
% 0.96/0.99      | r2_hidden(sK1(sK2,X0_41),X0_41) != iProver_top
% 0.96/0.99      | r2_hidden(sK1(sK2,X0_41),u1_pre_topc(sK2)) = iProver_top ),
% 0.96/0.99      inference(predicate_to_equality,[status(thm)],[c_1954]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_1958,plain,
% 0.96/0.99      ( r1_tarski(sK3,u1_pre_topc(sK2)) != iProver_top
% 0.96/0.99      | r2_hidden(sK1(sK2,sK3),u1_pre_topc(sK2)) = iProver_top
% 0.96/0.99      | r2_hidden(sK1(sK2,sK3),sK3) != iProver_top ),
% 0.96/0.99      inference(instantiation,[status(thm)],[c_1956]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_12,plain,
% 0.96/0.99      ( ~ v1_tops_2(X0,X1)
% 0.96/0.99      | v3_pre_topc(X2,X1)
% 0.96/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 0.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 0.96/0.99      | ~ r2_hidden(X2,X0)
% 0.96/0.99      | ~ l1_pre_topc(X1) ),
% 0.96/0.99      inference(cnf_transformation,[],[f39]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_222,plain,
% 0.96/0.99      ( ~ v1_tops_2(X0,sK2)
% 0.96/0.99      | v3_pre_topc(X1,sK2)
% 0.96/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 0.96/0.99      | ~ r2_hidden(X1,X0) ),
% 0.96/0.99      inference(resolution,[status(thm)],[c_12,c_16]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_1406,plain,
% 0.96/0.99      ( ~ v1_tops_2(X0_41,sK2)
% 0.96/0.99      | v3_pre_topc(X1_41,sK2)
% 0.96/0.99      | ~ m1_subset_1(X1_41,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.96/0.99      | ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 0.96/0.99      | ~ r2_hidden(X1_41,X0_41) ),
% 0.96/0.99      inference(subtyping,[status(esa)],[c_222]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_1544,plain,
% 0.96/0.99      ( ~ v1_tops_2(X0_41,sK2)
% 0.96/0.99      | v3_pre_topc(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,X1_41),sK2)
% 0.96/0.99      | ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 0.96/0.99      | ~ m1_subset_1(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,X1_41),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.96/0.99      | ~ r2_hidden(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,X1_41),X0_41) ),
% 0.96/0.99      inference(instantiation,[status(thm)],[c_1406]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_1711,plain,
% 0.96/0.99      ( ~ v1_tops_2(X0_41,sK2)
% 0.96/0.99      | v3_pre_topc(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),sK2)
% 0.96/0.99      | ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 0.96/0.99      | ~ m1_subset_1(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.96/0.99      | ~ r2_hidden(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),X0_41) ),
% 0.96/0.99      inference(instantiation,[status(thm)],[c_1544]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_1712,plain,
% 0.96/0.99      ( v1_tops_2(X0_41,sK2) != iProver_top
% 0.96/0.99      | v3_pre_topc(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),sK2) = iProver_top
% 0.96/0.99      | m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 0.96/0.99      | m1_subset_1(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 0.96/0.99      | r2_hidden(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),X0_41) != iProver_top ),
% 0.96/0.99      inference(predicate_to_equality,[status(thm)],[c_1711]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_1714,plain,
% 0.96/0.99      ( v1_tops_2(sK3,sK2) != iProver_top
% 0.96/0.99      | v3_pre_topc(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),sK2) = iProver_top
% 0.96/0.99      | m1_subset_1(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 0.96/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 0.96/0.99      | r2_hidden(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),sK3) != iProver_top ),
% 0.96/0.99      inference(instantiation,[status(thm)],[c_1712]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_2,plain,
% 0.96/0.99      ( r1_tarski(X0,X1)
% 0.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
% 0.96/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 0.96/0.99      | r2_hidden(sK0(X2,X0,X1),X0) ),
% 0.96/0.99      inference(cnf_transformation,[],[f32]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_1414,plain,
% 0.96/0.99      ( r1_tarski(X0_41,X1_41)
% 0.96/0.99      | ~ m1_subset_1(X0_41,k1_zfmisc_1(X2_41))
% 0.96/0.99      | ~ m1_subset_1(X1_41,k1_zfmisc_1(X2_41))
% 0.96/0.99      | r2_hidden(sK0(X2_41,X0_41,X1_41),X0_41) ),
% 0.96/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_1518,plain,
% 0.96/0.99      ( r1_tarski(sK3,X0_41)
% 0.96/0.99      | ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 0.96/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 0.96/0.99      | r2_hidden(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,X0_41),sK3) ),
% 0.96/0.99      inference(instantiation,[status(thm)],[c_1414]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_1606,plain,
% 0.96/0.99      ( r1_tarski(sK3,u1_pre_topc(sK2))
% 0.96/0.99      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 0.96/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 0.96/0.99      | r2_hidden(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),sK3) ),
% 0.96/0.99      inference(instantiation,[status(thm)],[c_1518]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_1607,plain,
% 0.96/0.99      ( r1_tarski(sK3,u1_pre_topc(sK2)) = iProver_top
% 0.96/0.99      | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 0.96/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 0.96/0.99      | r2_hidden(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),sK3) = iProver_top ),
% 0.96/0.99      inference(predicate_to_equality,[status(thm)],[c_1606]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_3,plain,
% 0.96/0.99      ( r1_tarski(X0,X1)
% 0.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
% 0.96/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 0.96/0.99      | m1_subset_1(sK0(X2,X0,X1),X2) ),
% 0.96/0.99      inference(cnf_transformation,[],[f31]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_1413,plain,
% 0.96/0.99      ( r1_tarski(X0_41,X1_41)
% 0.96/0.99      | ~ m1_subset_1(X0_41,k1_zfmisc_1(X2_41))
% 0.96/0.99      | ~ m1_subset_1(X1_41,k1_zfmisc_1(X2_41))
% 0.96/0.99      | m1_subset_1(sK0(X2_41,X0_41,X1_41),X2_41) ),
% 0.96/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_1580,plain,
% 0.96/0.99      ( r1_tarski(sK3,u1_pre_topc(sK2))
% 0.96/0.99      | m1_subset_1(sK0(X0_41,sK3,u1_pre_topc(sK2)),X0_41)
% 0.96/0.99      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(X0_41))
% 0.96/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0_41)) ),
% 0.96/0.99      inference(instantiation,[status(thm)],[c_1413]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_1598,plain,
% 0.96/0.99      ( r1_tarski(sK3,u1_pre_topc(sK2))
% 0.96/0.99      | m1_subset_1(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.96/0.99      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 0.96/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
% 0.96/0.99      inference(instantiation,[status(thm)],[c_1580]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_1599,plain,
% 0.96/0.99      ( r1_tarski(sK3,u1_pre_topc(sK2)) = iProver_top
% 0.96/0.99      | m1_subset_1(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 0.96/0.99      | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 0.96/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
% 0.96/0.99      inference(predicate_to_equality,[status(thm)],[c_1598]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_1,plain,
% 0.96/0.99      ( r1_tarski(X0,X1)
% 0.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
% 0.96/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 0.96/0.99      | ~ r2_hidden(sK0(X2,X0,X1),X1) ),
% 0.96/0.99      inference(cnf_transformation,[],[f33]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_1415,plain,
% 0.96/0.99      ( r1_tarski(X0_41,X1_41)
% 0.96/0.99      | ~ m1_subset_1(X0_41,k1_zfmisc_1(X2_41))
% 0.96/0.99      | ~ m1_subset_1(X1_41,k1_zfmisc_1(X2_41))
% 0.96/0.99      | ~ r2_hidden(sK0(X2_41,X0_41,X1_41),X1_41) ),
% 0.96/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_1528,plain,
% 0.96/0.99      ( r1_tarski(sK3,X0_41)
% 0.96/0.99      | ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 0.96/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 0.96/0.99      | ~ r2_hidden(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,X0_41),X0_41) ),
% 0.96/0.99      inference(instantiation,[status(thm)],[c_1415]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_1569,plain,
% 0.96/0.99      ( r1_tarski(sK3,u1_pre_topc(sK2))
% 0.96/0.99      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 0.96/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 0.96/0.99      | ~ r2_hidden(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),u1_pre_topc(sK2)) ),
% 0.96/0.99      inference(instantiation,[status(thm)],[c_1528]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_1570,plain,
% 0.96/0.99      ( r1_tarski(sK3,u1_pre_topc(sK2)) = iProver_top
% 0.96/0.99      | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 0.96/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 0.96/0.99      | r2_hidden(sK0(k1_zfmisc_1(u1_struct_0(sK2)),sK3,u1_pre_topc(sK2)),u1_pre_topc(sK2)) != iProver_top ),
% 0.96/0.99      inference(predicate_to_equality,[status(thm)],[c_1569]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_13,negated_conjecture,
% 0.96/0.99      ( ~ v1_tops_2(sK3,sK2) | ~ r1_tarski(sK3,u1_pre_topc(sK2)) ),
% 0.96/0.99      inference(cnf_transformation,[],[f46]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_129,plain,
% 0.96/0.99      ( ~ v1_tops_2(sK3,sK2) | ~ r1_tarski(sK3,u1_pre_topc(sK2)) ),
% 0.96/0.99      inference(prop_impl,[status(thm)],[c_13]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_11,plain,
% 0.96/0.99      ( v1_tops_2(X0,X1)
% 0.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 0.96/0.99      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 0.96/0.99      | ~ l1_pre_topc(X1) ),
% 0.96/0.99      inference(cnf_transformation,[],[f40]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_242,plain,
% 0.96/0.99      ( v1_tops_2(X0,sK2)
% 0.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 0.96/0.99      | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 0.96/0.99      inference(resolution,[status(thm)],[c_11,c_16]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_531,plain,
% 0.96/0.99      ( ~ r1_tarski(sK3,u1_pre_topc(sK2))
% 0.96/0.99      | m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.96/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
% 0.96/0.99      inference(resolution,[status(thm)],[c_129,c_242]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_532,plain,
% 0.96/0.99      ( r1_tarski(sK3,u1_pre_topc(sK2)) != iProver_top
% 0.96/0.99      | m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 0.96/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
% 0.96/0.99      inference(predicate_to_equality,[status(thm)],[c_531]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_10,plain,
% 0.96/0.99      ( v1_tops_2(X0,X1)
% 0.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 0.96/0.99      | r2_hidden(sK1(X1,X0),X0)
% 0.96/0.99      | ~ l1_pre_topc(X1) ),
% 0.96/0.99      inference(cnf_transformation,[],[f41]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_256,plain,
% 0.96/0.99      ( v1_tops_2(X0,sK2)
% 0.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 0.96/0.99      | r2_hidden(sK1(sK2,X0),X0) ),
% 0.96/0.99      inference(resolution,[status(thm)],[c_10,c_16]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_518,plain,
% 0.96/0.99      ( ~ r1_tarski(sK3,u1_pre_topc(sK2))
% 0.96/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 0.96/0.99      | r2_hidden(sK1(sK2,sK3),sK3) ),
% 0.96/0.99      inference(resolution,[status(thm)],[c_129,c_256]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_519,plain,
% 0.96/0.99      ( r1_tarski(sK3,u1_pre_topc(sK2)) != iProver_top
% 0.96/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 0.96/0.99      | r2_hidden(sK1(sK2,sK3),sK3) = iProver_top ),
% 0.96/0.99      inference(predicate_to_equality,[status(thm)],[c_518]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_9,plain,
% 0.96/0.99      ( v1_tops_2(X0,X1)
% 0.96/0.99      | ~ v3_pre_topc(sK1(X1,X0),X1)
% 0.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 0.96/0.99      | ~ l1_pre_topc(X1) ),
% 0.96/0.99      inference(cnf_transformation,[],[f42]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_270,plain,
% 0.96/0.99      ( v1_tops_2(X0,sK2)
% 0.96/0.99      | ~ v3_pre_topc(sK1(sK2,X0),sK2)
% 0.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
% 0.96/0.99      inference(resolution,[status(thm)],[c_9,c_16]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_505,plain,
% 0.96/0.99      ( ~ v3_pre_topc(sK1(sK2,sK3),sK2)
% 0.96/0.99      | ~ r1_tarski(sK3,u1_pre_topc(sK2))
% 0.96/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
% 0.96/0.99      inference(resolution,[status(thm)],[c_129,c_270]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_506,plain,
% 0.96/0.99      ( v3_pre_topc(sK1(sK2,sK3),sK2) != iProver_top
% 0.96/0.99      | r1_tarski(sK3,u1_pre_topc(sK2)) != iProver_top
% 0.96/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
% 0.96/0.99      inference(predicate_to_equality,[status(thm)],[c_505]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_8,plain,
% 0.96/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 0.96/0.99      | ~ l1_pre_topc(X0) ),
% 0.96/0.99      inference(cnf_transformation,[],[f38]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_33,plain,
% 0.96/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 0.96/0.99      | l1_pre_topc(X0) != iProver_top ),
% 0.96/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_35,plain,
% 0.96/0.99      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 0.96/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 0.96/0.99      inference(instantiation,[status(thm)],[c_33]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_14,negated_conjecture,
% 0.96/0.99      ( v1_tops_2(sK3,sK2) | r1_tarski(sK3,u1_pre_topc(sK2)) ),
% 0.96/0.99      inference(cnf_transformation,[],[f45]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_19,plain,
% 0.96/0.99      ( v1_tops_2(sK3,sK2) = iProver_top
% 0.96/0.99      | r1_tarski(sK3,u1_pre_topc(sK2)) = iProver_top ),
% 0.96/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_15,negated_conjecture,
% 0.96/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
% 0.96/0.99      inference(cnf_transformation,[],[f44]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_18,plain,
% 0.96/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
% 0.96/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(c_17,plain,
% 0.96/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 0.96/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 0.96/0.99  
% 0.96/0.99  cnf(contradiction,plain,
% 0.96/0.99      ( $false ),
% 0.96/0.99      inference(minisat,
% 0.96/0.99                [status(thm)],
% 0.96/0.99                [c_2137,c_1962,c_1958,c_1714,c_1607,c_1599,c_1570,c_532,
% 0.96/0.99                 c_519,c_506,c_35,c_19,c_18,c_17]) ).
% 0.96/0.99  
% 0.96/0.99  
% 0.96/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 0.96/0.99  
% 0.96/0.99  ------                               Statistics
% 0.96/0.99  
% 0.96/0.99  ------ General
% 0.96/0.99  
% 0.96/0.99  abstr_ref_over_cycles:                  0
% 0.96/0.99  abstr_ref_under_cycles:                 0
% 0.96/0.99  gc_basic_clause_elim:                   0
% 0.96/0.99  forced_gc_time:                         0
% 0.96/0.99  parsing_time:                           0.007
% 0.96/0.99  unif_index_cands_time:                  0.
% 0.96/0.99  unif_index_add_time:                    0.
% 0.96/0.99  orderings_time:                         0.
% 0.96/0.99  out_proof_time:                         0.008
% 0.96/0.99  total_time:                             0.079
% 0.96/0.99  num_of_symbols:                         43
% 0.96/0.99  num_of_terms:                           1497
% 0.96/0.99  
% 0.96/0.99  ------ Preprocessing
% 0.96/0.99  
% 0.96/0.99  num_of_splits:                          0
% 0.96/0.99  num_of_split_atoms:                     0
% 0.96/0.99  num_of_reused_defs:                     0
% 0.96/0.99  num_eq_ax_congr_red:                    0
% 0.96/0.99  num_of_sem_filtered_clauses:            0
% 0.96/0.99  num_of_subtypes:                        2
% 0.96/0.99  monotx_restored_types:                  0
% 0.96/0.99  sat_num_of_epr_types:                   0
% 0.96/0.99  sat_num_of_non_cyclic_types:            0
% 0.96/0.99  sat_guarded_non_collapsed_types:        0
% 0.96/0.99  num_pure_diseq_elim:                    0
% 0.96/0.99  simp_replaced_by:                       0
% 0.96/0.99  res_preprocessed:                       33
% 0.96/0.99  prep_upred:                             0
% 0.96/0.99  prep_unflattend:                        0
% 0.96/0.99  smt_new_axioms:                         0
% 0.96/0.99  pred_elim_cands:                        5
% 0.96/0.99  pred_elim:                              1
% 0.96/0.99  pred_elim_cl:                           1
% 0.96/0.99  pred_elim_cycles:                       7
% 0.96/0.99  merged_defs:                            8
% 0.96/0.99  merged_defs_ncl:                        0
% 0.96/0.99  bin_hyper_res:                          9
% 0.96/0.99  prep_cycles:                            2
% 0.96/0.99  pred_elim_time:                         0.016
% 0.96/0.99  splitting_time:                         0.
% 0.96/0.99  sem_filter_time:                        0.
% 0.96/0.99  monotx_time:                            0.
% 0.96/0.99  subtype_inf_time:                       0.
% 0.96/0.99  
% 0.96/0.99  ------ Problem properties
% 0.96/0.99  
% 0.96/0.99  clauses:                                16
% 0.96/0.99  conjectures:                            3
% 0.96/0.99  epr:                                    1
% 0.96/0.99  horn:                                   11
% 0.96/0.99  ground:                                 4
% 0.96/0.99  unary:                                  2
% 0.96/0.99  binary:                                 4
% 0.96/0.99  lits:                                   45
% 0.96/0.99  lits_eq:                                0
% 0.96/0.99  fd_pure:                                0
% 0.96/0.99  fd_pseudo:                              0
% 0.96/0.99  fd_cond:                                0
% 0.96/0.99  fd_pseudo_cond:                         0
% 0.96/0.99  ac_symbols:                             0
% 0.96/0.99  
% 0.96/0.99  ------ Propositional Solver
% 0.96/0.99  
% 0.96/0.99  prop_solver_calls:                      18
% 0.96/0.99  prop_fast_solver_calls:                 433
% 0.96/0.99  smt_solver_calls:                       0
% 0.96/0.99  smt_fast_solver_calls:                  0
% 0.96/0.99  prop_num_of_clauses:                    580
% 0.96/0.99  prop_preprocess_simplified:             1892
% 0.96/0.99  prop_fo_subsumed:                       12
% 0.96/0.99  prop_solver_time:                       0.
% 0.96/0.99  smt_solver_time:                        0.
% 0.96/0.99  smt_fast_solver_time:                   0.
% 0.96/0.99  prop_fast_solver_time:                  0.
% 0.96/0.99  prop_unsat_core_time:                   0.
% 0.96/0.99  
% 0.96/0.99  ------ QBF
% 0.96/0.99  
% 0.96/0.99  qbf_q_res:                              0
% 0.96/0.99  qbf_num_tautologies:                    0
% 0.96/0.99  qbf_prep_cycles:                        0
% 0.96/0.99  
% 0.96/0.99  ------ BMC1
% 0.96/0.99  
% 0.96/0.99  bmc1_current_bound:                     -1
% 0.96/0.99  bmc1_last_solved_bound:                 -1
% 0.96/0.99  bmc1_unsat_core_size:                   -1
% 0.96/0.99  bmc1_unsat_core_parents_size:           -1
% 0.96/0.99  bmc1_merge_next_fun:                    0
% 0.96/0.99  bmc1_unsat_core_clauses_time:           0.
% 0.96/0.99  
% 0.96/0.99  ------ Instantiation
% 0.96/0.99  
% 0.96/0.99  inst_num_of_clauses:                    138
% 0.96/0.99  inst_num_in_passive:                    20
% 0.96/0.99  inst_num_in_active:                     117
% 0.96/0.99  inst_num_in_unprocessed:                0
% 0.96/0.99  inst_num_of_loops:                      183
% 0.96/0.99  inst_num_of_learning_restarts:          0
% 0.96/0.99  inst_num_moves_active_passive:          60
% 0.96/0.99  inst_lit_activity:                      0
% 0.96/0.99  inst_lit_activity_moves:                0
% 0.96/0.99  inst_num_tautologies:                   0
% 0.96/0.99  inst_num_prop_implied:                  0
% 0.96/0.99  inst_num_existing_simplified:           0
% 0.96/0.99  inst_num_eq_res_simplified:             0
% 0.96/0.99  inst_num_child_elim:                    0
% 0.96/0.99  inst_num_of_dismatching_blockings:      33
% 0.96/0.99  inst_num_of_non_proper_insts:           144
% 0.96/0.99  inst_num_of_duplicates:                 0
% 0.96/0.99  inst_inst_num_from_inst_to_res:         0
% 0.96/0.99  inst_dismatching_checking_time:         0.
% 0.96/0.99  
% 0.96/0.99  ------ Resolution
% 0.96/0.99  
% 0.96/0.99  res_num_of_clauses:                     0
% 0.96/0.99  res_num_in_passive:                     0
% 0.96/0.99  res_num_in_active:                      0
% 0.96/0.99  res_num_of_loops:                       35
% 0.96/0.99  res_forward_subset_subsumed:            2
% 0.96/0.99  res_backward_subset_subsumed:           0
% 0.96/0.99  res_forward_subsumed:                   0
% 0.96/0.99  res_backward_subsumed:                  0
% 0.96/0.99  res_forward_subsumption_resolution:     1
% 0.96/0.99  res_backward_subsumption_resolution:    0
% 0.96/0.99  res_clause_to_clause_subsumption:       73
% 0.96/0.99  res_orphan_elimination:                 0
% 0.96/0.99  res_tautology_del:                      35
% 0.96/0.99  res_num_eq_res_simplified:              0
% 0.96/0.99  res_num_sel_changes:                    0
% 0.96/0.99  res_moves_from_active_to_pass:          0
% 0.96/0.99  
% 0.96/0.99  ------ Superposition
% 0.96/0.99  
% 0.96/0.99  sup_time_total:                         0.
% 0.96/0.99  sup_time_generating:                    0.
% 0.96/0.99  sup_time_sim_full:                      0.
% 0.96/0.99  sup_time_sim_immed:                     0.
% 0.96/0.99  
% 0.96/0.99  sup_num_of_clauses:                     0
% 0.96/0.99  sup_num_in_active:                      0
% 0.96/0.99  sup_num_in_passive:                     0
% 0.96/0.99  sup_num_of_loops:                       0
% 0.96/0.99  sup_fw_superposition:                   0
% 0.96/0.99  sup_bw_superposition:                   0
% 0.96/0.99  sup_immediate_simplified:               0
% 0.96/0.99  sup_given_eliminated:                   0
% 0.96/0.99  comparisons_done:                       0
% 0.96/0.99  comparisons_avoided:                    0
% 0.96/0.99  
% 0.96/0.99  ------ Simplifications
% 0.96/0.99  
% 0.96/0.99  
% 0.96/0.99  sim_fw_subset_subsumed:                 0
% 0.96/0.99  sim_bw_subset_subsumed:                 0
% 0.96/0.99  sim_fw_subsumed:                        0
% 0.96/0.99  sim_bw_subsumed:                        0
% 0.96/0.99  sim_fw_subsumption_res:                 0
% 0.96/0.99  sim_bw_subsumption_res:                 0
% 0.96/0.99  sim_tautology_del:                      0
% 0.96/0.99  sim_eq_tautology_del:                   0
% 0.96/0.99  sim_eq_res_simp:                        0
% 0.96/0.99  sim_fw_demodulated:                     0
% 0.96/0.99  sim_bw_demodulated:                     0
% 0.96/0.99  sim_light_normalised:                   0
% 0.96/0.99  sim_joinable_taut:                      0
% 0.96/0.99  sim_joinable_simp:                      0
% 0.96/0.99  sim_ac_normalised:                      0
% 0.96/0.99  sim_smt_subsumption:                    0
% 0.96/0.99  
%------------------------------------------------------------------------------
