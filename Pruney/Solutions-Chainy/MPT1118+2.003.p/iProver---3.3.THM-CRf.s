%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:34 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 279 expanded)
%              Number of clauses        :   64 (  87 expanded)
%              Number of leaves         :   11 (  71 expanded)
%              Depth                    :   13
%              Number of atoms          :  453 (1438 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f8])).

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

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

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

fof(f9,plain,(
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
    inference(flattening,[],[f9])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f17])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( r2_hidden(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( r1_tarski(X1,X3)
                        & v4_pre_topc(X3,X0) )
                     => r2_hidden(X2,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( r2_hidden(X2,X3)
                    | ~ r1_tarski(X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( r2_hidden(X2,X3)
                    | ~ r1_tarski(X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r1_tarski(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r1_tarski(X1,X4)
                      | ~ v4_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r1_tarski(X1,X3)
          & v4_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(X2,sK1(X0,X1,X2))
        & r1_tarski(X1,sK1(X0,X1,X2))
        & v4_pre_topc(sK1(X0,X1,X2),X0)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ( ~ r2_hidden(X2,sK1(X0,X1,X2))
                    & r1_tarski(X1,sK1(X0,X1,X2))
                    & v4_pre_topc(sK1(X0,X1,X2),X0)
                    & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r1_tarski(X1,X4)
                      | ~ v4_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X2,X4)
      | ~ r1_tarski(X1,X4)
      | ~ v4_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X1,X2)
                 => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,sK4))
        & r1_tarski(X1,sK4)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(k2_pre_topc(X0,sK3),k2_pre_topc(X0,X2))
            & r1_tarski(sK3,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
                & r1_tarski(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(sK2,X1),k2_pre_topc(sK2,X2))
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))
    & r1_tarski(sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f26,f25,f24])).

fof(f40,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | r1_tarski(X1,sK1(X0,X1,X2))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | v4_pre_topc(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ r2_hidden(X2,sK1(X0,X1,X2))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,(
    ~ r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_122,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_159,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_0,c_122])).

cnf(c_1538,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | ~ r2_hidden(X2_41,X0_41)
    | r2_hidden(X2_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_159])).

cnf(c_3546,plain,
    ( ~ r1_tarski(sK4,X0_41)
    | r2_hidden(sK0(u1_struct_0(sK2),sK3,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)))),X0_41)
    | ~ r2_hidden(sK0(u1_struct_0(sK2),sK3,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)))),sK4) ),
    inference(instantiation,[status(thm)],[c_1538])).

cnf(c_4080,plain,
    ( ~ r1_tarski(sK4,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
    | r2_hidden(sK0(u1_struct_0(sK2),sK3,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)))),sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
    | ~ r2_hidden(sK0(u1_struct_0(sK2),sK3,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)))),sK4) ),
    inference(instantiation,[status(thm)],[c_3546])).

cnf(c_1648,plain,
    ( ~ r1_tarski(sK3,sK4)
    | r2_hidden(X0_41,sK4)
    | ~ r2_hidden(X0_41,sK3) ),
    inference(instantiation,[status(thm)],[c_1538])).

cnf(c_3122,plain,
    ( ~ r1_tarski(sK3,sK4)
    | r2_hidden(sK0(u1_struct_0(sK2),sK3,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)))),sK4)
    | ~ r2_hidden(sK0(u1_struct_0(sK2),sK3,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)))),sK3) ),
    inference(instantiation,[status(thm)],[c_1648])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(sK0(X2,X0,X1),X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1547,plain,
    ( r1_tarski(X0_41,X1_41)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(X2_41))
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(X2_41))
    | ~ r2_hidden(sK0(X2_41,X0_41,X1_41),X1_41) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1688,plain,
    ( r1_tarski(sK3,X0_41)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK0(u1_struct_0(sK2),sK3,X0_41),X0_41) ),
    inference(instantiation,[status(thm)],[c_1547])).

cnf(c_2758,plain,
    ( r1_tarski(sK3,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
    | ~ m1_subset_1(sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK0(u1_struct_0(sK2),sK3,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)))),sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)))) ),
    inference(instantiation,[status(thm)],[c_1688])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | r2_hidden(sK0(X2,X0,X1),X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1546,plain,
    ( r1_tarski(X0_41,X1_41)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(X2_41))
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(X2_41))
    | r2_hidden(sK0(X2_41,X0_41,X1_41),X0_41) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1673,plain,
    ( r1_tarski(sK3,X0_41)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK0(u1_struct_0(sK2),sK3,X0_41),sK3) ),
    inference(instantiation,[status(thm)],[c_1546])).

cnf(c_2759,plain,
    ( r1_tarski(sK3,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
    | ~ m1_subset_1(sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK0(u1_struct_0(sK2),sK3,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)))),sK3) ),
    inference(instantiation,[status(thm)],[c_1673])).

cnf(c_11,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X3,X0)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ r2_hidden(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_255,plain,
    ( ~ v4_pre_topc(X0,sK2)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k2_pre_topc(sK2,X1))
    | ~ r2_hidden(X2,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_11,c_16])).

cnf(c_1537,plain,
    ( ~ v4_pre_topc(X0_41,sK2)
    | ~ r1_tarski(X1_41,X0_41)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X2_41,X0_41)
    | ~ r2_hidden(X2_41,k2_pre_topc(sK2,X1_41))
    | ~ r2_hidden(X2_41,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_255])).

cnf(c_2073,plain,
    ( ~ v4_pre_topc(sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),sK2)
    | ~ r1_tarski(X0_41,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1_41,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
    | ~ r2_hidden(X1_41,k2_pre_topc(sK2,X0_41))
    | ~ r2_hidden(X1_41,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1537])).

cnf(c_2320,plain,
    ( ~ v4_pre_topc(sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),sK2)
    | ~ r1_tarski(X0_41,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
    | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,X0_41))
    | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2073])).

cnf(c_2322,plain,
    ( ~ v4_pre_topc(sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),sK2)
    | ~ r1_tarski(sK3,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
    | ~ m1_subset_1(sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
    | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,sK3))
    | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2320])).

cnf(c_8,plain,
    ( r1_tarski(X0,sK1(X1,X0,X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ r2_hidden(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_298,plain,
    ( r1_tarski(X0,sK1(sK2,X0,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,k2_pre_topc(sK2,X0))
    | ~ r2_hidden(X1,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_8,c_16])).

cnf(c_1535,plain,
    ( r1_tarski(X0_41,sK1(sK2,X0_41,X1_41))
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1_41,k2_pre_topc(sK2,X0_41))
    | ~ r2_hidden(X1_41,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_298])).

cnf(c_1836,plain,
    ( r1_tarski(X0_41,sK1(sK2,X0_41,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,X0_41))
    | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1535])).

cnf(c_1945,plain,
    ( r1_tarski(sK4,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,sK4))
    | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1836])).

cnf(c_9,plain,
    ( v4_pre_topc(sK1(X0,X1,X2),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ r2_hidden(X2,u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_343,plain,
    ( v4_pre_topc(sK1(sK2,X0,X1),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,k2_pre_topc(sK2,X0))
    | ~ r2_hidden(X1,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_9,c_16])).

cnf(c_1532,plain,
    ( v4_pre_topc(sK1(sK2,X0_41,X1_41),sK2)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1_41,k2_pre_topc(sK2,X0_41))
    | ~ r2_hidden(X1_41,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_343])).

cnf(c_1839,plain,
    ( v4_pre_topc(sK1(sK2,X0_41,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),sK2)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,X0_41))
    | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1532])).

cnf(c_1939,plain,
    ( v4_pre_topc(sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,sK4))
    | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1839])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ r2_hidden(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_281,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,k2_pre_topc(sK2,X0))
    | ~ r2_hidden(X1,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_10,c_16])).

cnf(c_1536,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0_41,X1_41),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1_41,k2_pre_topc(sK2,X0_41))
    | ~ r2_hidden(X1_41,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_281])).

cnf(c_1838,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0_41,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,X0_41))
    | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1536])).

cnf(c_1933,plain,
    ( m1_subset_1(sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,sK4))
    | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1838])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,sK1(X1,X0,X2))
    | r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ r2_hidden(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_315,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,sK1(sK2,X0,X1))
    | r2_hidden(X1,k2_pre_topc(sK2,X0))
    | ~ r2_hidden(X1,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_7,c_16])).

cnf(c_1534,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1_41,sK1(sK2,X0_41,X1_41))
    | r2_hidden(X1_41,k2_pre_topc(sK2,X0_41))
    | ~ r2_hidden(X1_41,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_315])).

cnf(c_1837,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),sK1(sK2,X0_41,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
    | r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,X0_41))
    | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1534])).

cnf(c_1927,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
    | r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,sK4))
    | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1837])).

cnf(c_1759,plain,
    ( ~ r1_tarski(k2_pre_topc(sK2,sK3),X0_41)
    | r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),X0_41)
    | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1538])).

cnf(c_1800,plain,
    ( ~ r1_tarski(k2_pre_topc(sK2,sK3),u1_struct_0(sK2))
    | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,sK3))
    | r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1759])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_332,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[status(thm)],[c_6,c_16])).

cnf(c_1533,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k2_pre_topc(sK2,X0_41),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_332])).

cnf(c_1764,plain,
    ( m1_subset_1(k2_pre_topc(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_1533])).

cnf(c_1693,plain,
    ( r1_tarski(k2_pre_topc(sK2,X0_41),X1_41)
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_pre_topc(sK2,X0_41),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,X0_41),X1_41),X1_41) ),
    inference(instantiation,[status(thm)],[c_1547])).

cnf(c_1740,plain,
    ( r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))
    | ~ m1_subset_1(k2_pre_topc(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_1693])).

cnf(c_1678,plain,
    ( r1_tarski(k2_pre_topc(sK2,X0_41),X1_41)
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_pre_topc(sK2,X0_41),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,X0_41),X1_41),k2_pre_topc(sK2,X0_41)) ),
    inference(instantiation,[status(thm)],[c_1546])).

cnf(c_1737,plain,
    ( r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))
    | ~ m1_subset_1(k2_pre_topc(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1678])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1543,plain,
    ( r1_tarski(X0_41,X1_41)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(X1_41)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1640,plain,
    ( r1_tarski(k2_pre_topc(sK2,X0_41),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_pre_topc(sK2,X0_41),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_1543])).

cnf(c_1642,plain,
    ( r1_tarski(k2_pre_topc(sK2,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_1640])).

cnf(c_1581,plain,
    ( m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_1533])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f41])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4080,c_3122,c_2758,c_2759,c_2322,c_1945,c_1939,c_1933,c_1927,c_1800,c_1764,c_1740,c_1737,c_1642,c_1581,c_12,c_13,c_14,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:49:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.22/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/0.98  
% 3.22/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.22/0.98  
% 3.22/0.98  ------  iProver source info
% 3.22/0.98  
% 3.22/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.22/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.22/0.98  git: non_committed_changes: false
% 3.22/0.98  git: last_make_outside_of_git: false
% 3.22/0.98  
% 3.22/0.98  ------ 
% 3.22/0.98  
% 3.22/0.98  ------ Input Options
% 3.22/0.98  
% 3.22/0.98  --out_options                           all
% 3.22/0.98  --tptp_safe_out                         true
% 3.22/0.98  --problem_path                          ""
% 3.22/0.98  --include_path                          ""
% 3.22/0.98  --clausifier                            res/vclausify_rel
% 3.22/0.98  --clausifier_options                    --mode clausify
% 3.22/0.98  --stdin                                 false
% 3.22/0.98  --stats_out                             all
% 3.22/0.98  
% 3.22/0.98  ------ General Options
% 3.22/0.98  
% 3.22/0.98  --fof                                   false
% 3.22/0.98  --time_out_real                         305.
% 3.22/0.98  --time_out_virtual                      -1.
% 3.22/0.98  --symbol_type_check                     false
% 3.22/0.98  --clausify_out                          false
% 3.22/0.98  --sig_cnt_out                           false
% 3.22/0.98  --trig_cnt_out                          false
% 3.22/0.98  --trig_cnt_out_tolerance                1.
% 3.22/0.98  --trig_cnt_out_sk_spl                   false
% 3.22/0.98  --abstr_cl_out                          false
% 3.22/0.98  
% 3.22/0.98  ------ Global Options
% 3.22/0.98  
% 3.22/0.98  --schedule                              default
% 3.22/0.98  --add_important_lit                     false
% 3.22/0.98  --prop_solver_per_cl                    1000
% 3.22/0.98  --min_unsat_core                        false
% 3.22/0.98  --soft_assumptions                      false
% 3.22/0.98  --soft_lemma_size                       3
% 3.22/0.98  --prop_impl_unit_size                   0
% 3.22/0.98  --prop_impl_unit                        []
% 3.22/0.98  --share_sel_clauses                     true
% 3.22/0.98  --reset_solvers                         false
% 3.22/0.98  --bc_imp_inh                            [conj_cone]
% 3.22/0.98  --conj_cone_tolerance                   3.
% 3.22/0.98  --extra_neg_conj                        none
% 3.22/0.98  --large_theory_mode                     true
% 3.22/0.98  --prolific_symb_bound                   200
% 3.22/0.98  --lt_threshold                          2000
% 3.22/0.98  --clause_weak_htbl                      true
% 3.22/0.98  --gc_record_bc_elim                     false
% 3.22/0.98  
% 3.22/0.98  ------ Preprocessing Options
% 3.22/0.98  
% 3.22/0.98  --preprocessing_flag                    true
% 3.22/0.98  --time_out_prep_mult                    0.1
% 3.22/0.98  --splitting_mode                        input
% 3.22/0.98  --splitting_grd                         true
% 3.22/0.98  --splitting_cvd                         false
% 3.22/0.98  --splitting_cvd_svl                     false
% 3.22/0.98  --splitting_nvd                         32
% 3.22/0.98  --sub_typing                            true
% 3.22/0.98  --prep_gs_sim                           true
% 3.22/0.98  --prep_unflatten                        true
% 3.22/0.98  --prep_res_sim                          true
% 3.22/0.98  --prep_upred                            true
% 3.22/0.98  --prep_sem_filter                       exhaustive
% 3.22/0.98  --prep_sem_filter_out                   false
% 3.22/0.98  --pred_elim                             true
% 3.22/0.98  --res_sim_input                         true
% 3.22/0.98  --eq_ax_congr_red                       true
% 3.22/0.98  --pure_diseq_elim                       true
% 3.22/0.98  --brand_transform                       false
% 3.22/0.98  --non_eq_to_eq                          false
% 3.22/0.98  --prep_def_merge                        true
% 3.22/0.98  --prep_def_merge_prop_impl              false
% 3.22/0.98  --prep_def_merge_mbd                    true
% 3.22/0.98  --prep_def_merge_tr_red                 false
% 3.22/0.98  --prep_def_merge_tr_cl                  false
% 3.22/0.98  --smt_preprocessing                     true
% 3.22/0.98  --smt_ac_axioms                         fast
% 3.22/0.98  --preprocessed_out                      false
% 3.22/0.98  --preprocessed_stats                    false
% 3.22/0.98  
% 3.22/0.98  ------ Abstraction refinement Options
% 3.22/0.98  
% 3.22/0.98  --abstr_ref                             []
% 3.22/0.98  --abstr_ref_prep                        false
% 3.22/0.98  --abstr_ref_until_sat                   false
% 3.22/0.98  --abstr_ref_sig_restrict                funpre
% 3.22/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.22/0.98  --abstr_ref_under                       []
% 3.22/0.98  
% 3.22/0.98  ------ SAT Options
% 3.22/0.98  
% 3.22/0.98  --sat_mode                              false
% 3.22/0.98  --sat_fm_restart_options                ""
% 3.22/0.98  --sat_gr_def                            false
% 3.22/0.98  --sat_epr_types                         true
% 3.22/0.98  --sat_non_cyclic_types                  false
% 3.22/0.98  --sat_finite_models                     false
% 3.22/0.98  --sat_fm_lemmas                         false
% 3.22/0.98  --sat_fm_prep                           false
% 3.22/0.98  --sat_fm_uc_incr                        true
% 3.22/0.98  --sat_out_model                         small
% 3.22/0.98  --sat_out_clauses                       false
% 3.22/0.98  
% 3.22/0.98  ------ QBF Options
% 3.22/0.98  
% 3.22/0.98  --qbf_mode                              false
% 3.22/0.98  --qbf_elim_univ                         false
% 3.22/0.98  --qbf_dom_inst                          none
% 3.22/0.98  --qbf_dom_pre_inst                      false
% 3.22/0.98  --qbf_sk_in                             false
% 3.22/0.98  --qbf_pred_elim                         true
% 3.22/0.98  --qbf_split                             512
% 3.22/0.98  
% 3.22/0.98  ------ BMC1 Options
% 3.22/0.98  
% 3.22/0.98  --bmc1_incremental                      false
% 3.22/0.98  --bmc1_axioms                           reachable_all
% 3.22/0.98  --bmc1_min_bound                        0
% 3.22/0.98  --bmc1_max_bound                        -1
% 3.22/0.98  --bmc1_max_bound_default                -1
% 3.22/0.98  --bmc1_symbol_reachability              true
% 3.22/0.98  --bmc1_property_lemmas                  false
% 3.22/0.98  --bmc1_k_induction                      false
% 3.22/0.98  --bmc1_non_equiv_states                 false
% 3.22/0.98  --bmc1_deadlock                         false
% 3.22/0.98  --bmc1_ucm                              false
% 3.22/0.98  --bmc1_add_unsat_core                   none
% 3.22/0.98  --bmc1_unsat_core_children              false
% 3.22/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.22/0.98  --bmc1_out_stat                         full
% 3.22/0.98  --bmc1_ground_init                      false
% 3.22/0.98  --bmc1_pre_inst_next_state              false
% 3.22/0.98  --bmc1_pre_inst_state                   false
% 3.22/0.98  --bmc1_pre_inst_reach_state             false
% 3.22/0.98  --bmc1_out_unsat_core                   false
% 3.22/0.98  --bmc1_aig_witness_out                  false
% 3.22/0.98  --bmc1_verbose                          false
% 3.22/0.98  --bmc1_dump_clauses_tptp                false
% 3.22/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.22/0.98  --bmc1_dump_file                        -
% 3.22/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.22/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.22/0.98  --bmc1_ucm_extend_mode                  1
% 3.22/0.98  --bmc1_ucm_init_mode                    2
% 3.22/0.98  --bmc1_ucm_cone_mode                    none
% 3.22/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.22/0.98  --bmc1_ucm_relax_model                  4
% 3.22/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.22/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.22/0.98  --bmc1_ucm_layered_model                none
% 3.22/0.98  --bmc1_ucm_max_lemma_size               10
% 3.22/0.98  
% 3.22/0.98  ------ AIG Options
% 3.22/0.98  
% 3.22/0.98  --aig_mode                              false
% 3.22/0.98  
% 3.22/0.98  ------ Instantiation Options
% 3.22/0.98  
% 3.22/0.98  --instantiation_flag                    true
% 3.22/0.98  --inst_sos_flag                         false
% 3.22/0.98  --inst_sos_phase                        true
% 3.22/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.22/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.22/0.98  --inst_lit_sel_side                     num_symb
% 3.22/0.98  --inst_solver_per_active                1400
% 3.22/0.98  --inst_solver_calls_frac                1.
% 3.22/0.98  --inst_passive_queue_type               priority_queues
% 3.22/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.22/0.98  --inst_passive_queues_freq              [25;2]
% 3.22/0.98  --inst_dismatching                      true
% 3.22/0.98  --inst_eager_unprocessed_to_passive     true
% 3.22/0.98  --inst_prop_sim_given                   true
% 3.22/0.98  --inst_prop_sim_new                     false
% 3.22/0.98  --inst_subs_new                         false
% 3.22/0.98  --inst_eq_res_simp                      false
% 3.22/0.98  --inst_subs_given                       false
% 3.22/0.98  --inst_orphan_elimination               true
% 3.22/0.98  --inst_learning_loop_flag               true
% 3.22/0.98  --inst_learning_start                   3000
% 3.22/0.98  --inst_learning_factor                  2
% 3.22/0.98  --inst_start_prop_sim_after_learn       3
% 3.22/0.98  --inst_sel_renew                        solver
% 3.22/0.98  --inst_lit_activity_flag                true
% 3.22/0.98  --inst_restr_to_given                   false
% 3.22/0.98  --inst_activity_threshold               500
% 3.22/0.98  --inst_out_proof                        true
% 3.22/0.98  
% 3.22/0.98  ------ Resolution Options
% 3.22/0.98  
% 3.22/0.98  --resolution_flag                       true
% 3.22/0.98  --res_lit_sel                           adaptive
% 3.22/0.98  --res_lit_sel_side                      none
% 3.22/0.98  --res_ordering                          kbo
% 3.22/0.98  --res_to_prop_solver                    active
% 3.22/0.98  --res_prop_simpl_new                    false
% 3.22/0.98  --res_prop_simpl_given                  true
% 3.22/0.98  --res_passive_queue_type                priority_queues
% 3.22/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.22/0.98  --res_passive_queues_freq               [15;5]
% 3.22/0.98  --res_forward_subs                      full
% 3.22/0.98  --res_backward_subs                     full
% 3.22/0.98  --res_forward_subs_resolution           true
% 3.22/0.98  --res_backward_subs_resolution          true
% 3.22/0.98  --res_orphan_elimination                true
% 3.22/0.98  --res_time_limit                        2.
% 3.22/0.98  --res_out_proof                         true
% 3.22/0.98  
% 3.22/0.98  ------ Superposition Options
% 3.22/0.98  
% 3.22/0.98  --superposition_flag                    true
% 3.22/0.98  --sup_passive_queue_type                priority_queues
% 3.22/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.22/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.22/0.98  --demod_completeness_check              fast
% 3.22/0.98  --demod_use_ground                      true
% 3.22/0.98  --sup_to_prop_solver                    passive
% 3.22/0.98  --sup_prop_simpl_new                    true
% 3.22/0.98  --sup_prop_simpl_given                  true
% 3.22/0.98  --sup_fun_splitting                     false
% 3.22/0.98  --sup_smt_interval                      50000
% 3.22/0.98  
% 3.22/0.98  ------ Superposition Simplification Setup
% 3.22/0.98  
% 3.22/0.98  --sup_indices_passive                   []
% 3.22/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.22/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.98  --sup_full_bw                           [BwDemod]
% 3.22/0.98  --sup_immed_triv                        [TrivRules]
% 3.22/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.22/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.98  --sup_immed_bw_main                     []
% 3.22/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.22/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/0.98  
% 3.22/0.98  ------ Combination Options
% 3.22/0.98  
% 3.22/0.98  --comb_res_mult                         3
% 3.22/0.98  --comb_sup_mult                         2
% 3.22/0.98  --comb_inst_mult                        10
% 3.22/0.98  
% 3.22/0.98  ------ Debug Options
% 3.22/0.98  
% 3.22/0.98  --dbg_backtrace                         false
% 3.22/0.98  --dbg_dump_prop_clauses                 false
% 3.22/0.98  --dbg_dump_prop_clauses_file            -
% 3.22/0.98  --dbg_out_stat                          false
% 3.22/0.98  ------ Parsing...
% 3.22/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.22/0.98  
% 3.22/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 3.22/0.98  
% 3.22/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.22/0.98  ------ Proving...
% 3.22/0.98  ------ Problem Properties 
% 3.22/0.98  
% 3.22/0.98  
% 3.22/0.98  clauses                                 16
% 3.22/0.98  conjectures                             4
% 3.22/0.98  EPR                                     2
% 3.22/0.98  Horn                                    11
% 3.22/0.98  unary                                   4
% 3.22/0.98  binary                                  3
% 3.22/0.98  lits                                    48
% 3.22/0.98  lits eq                                 0
% 3.22/0.98  fd_pure                                 0
% 3.22/0.98  fd_pseudo                               0
% 3.22/0.98  fd_cond                                 0
% 3.22/0.98  fd_pseudo_cond                          0
% 3.22/0.98  AC symbols                              0
% 3.22/0.98  
% 3.22/0.98  ------ Schedule dynamic 5 is on 
% 3.22/0.98  
% 3.22/0.98  ------ no equalities: superposition off 
% 3.22/0.98  
% 3.22/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.22/0.98  
% 3.22/0.98  
% 3.22/0.98  ------ 
% 3.22/0.98  Current options:
% 3.22/0.98  ------ 
% 3.22/0.98  
% 3.22/0.98  ------ Input Options
% 3.22/0.98  
% 3.22/0.98  --out_options                           all
% 3.22/0.98  --tptp_safe_out                         true
% 3.22/0.98  --problem_path                          ""
% 3.22/0.98  --include_path                          ""
% 3.22/0.98  --clausifier                            res/vclausify_rel
% 3.22/0.98  --clausifier_options                    --mode clausify
% 3.22/0.98  --stdin                                 false
% 3.22/0.98  --stats_out                             all
% 3.22/0.98  
% 3.22/0.98  ------ General Options
% 3.22/0.98  
% 3.22/0.98  --fof                                   false
% 3.22/0.98  --time_out_real                         305.
% 3.22/0.98  --time_out_virtual                      -1.
% 3.22/0.98  --symbol_type_check                     false
% 3.22/0.98  --clausify_out                          false
% 3.22/0.98  --sig_cnt_out                           false
% 3.22/0.98  --trig_cnt_out                          false
% 3.22/0.98  --trig_cnt_out_tolerance                1.
% 3.22/0.98  --trig_cnt_out_sk_spl                   false
% 3.22/0.98  --abstr_cl_out                          false
% 3.22/0.98  
% 3.22/0.98  ------ Global Options
% 3.22/0.98  
% 3.22/0.98  --schedule                              default
% 3.22/0.98  --add_important_lit                     false
% 3.22/0.98  --prop_solver_per_cl                    1000
% 3.22/0.98  --min_unsat_core                        false
% 3.22/0.98  --soft_assumptions                      false
% 3.22/0.98  --soft_lemma_size                       3
% 3.22/0.98  --prop_impl_unit_size                   0
% 3.22/0.98  --prop_impl_unit                        []
% 3.22/0.98  --share_sel_clauses                     true
% 3.22/0.98  --reset_solvers                         false
% 3.22/0.98  --bc_imp_inh                            [conj_cone]
% 3.22/0.98  --conj_cone_tolerance                   3.
% 3.22/0.98  --extra_neg_conj                        none
% 3.22/0.98  --large_theory_mode                     true
% 3.22/0.98  --prolific_symb_bound                   200
% 3.22/0.98  --lt_threshold                          2000
% 3.22/0.98  --clause_weak_htbl                      true
% 3.22/0.98  --gc_record_bc_elim                     false
% 3.22/0.98  
% 3.22/0.98  ------ Preprocessing Options
% 3.22/0.98  
% 3.22/0.98  --preprocessing_flag                    true
% 3.22/0.98  --time_out_prep_mult                    0.1
% 3.22/0.98  --splitting_mode                        input
% 3.22/0.98  --splitting_grd                         true
% 3.22/0.98  --splitting_cvd                         false
% 3.22/0.98  --splitting_cvd_svl                     false
% 3.22/0.98  --splitting_nvd                         32
% 3.22/0.98  --sub_typing                            true
% 3.22/0.98  --prep_gs_sim                           true
% 3.22/0.98  --prep_unflatten                        true
% 3.22/0.98  --prep_res_sim                          true
% 3.22/0.98  --prep_upred                            true
% 3.22/0.98  --prep_sem_filter                       exhaustive
% 3.22/0.98  --prep_sem_filter_out                   false
% 3.22/0.98  --pred_elim                             true
% 3.22/0.98  --res_sim_input                         true
% 3.22/0.98  --eq_ax_congr_red                       true
% 3.22/0.98  --pure_diseq_elim                       true
% 3.22/0.98  --brand_transform                       false
% 3.22/0.98  --non_eq_to_eq                          false
% 3.22/0.98  --prep_def_merge                        true
% 3.22/0.98  --prep_def_merge_prop_impl              false
% 3.22/0.98  --prep_def_merge_mbd                    true
% 3.22/0.98  --prep_def_merge_tr_red                 false
% 3.22/0.98  --prep_def_merge_tr_cl                  false
% 3.22/0.98  --smt_preprocessing                     true
% 3.22/0.98  --smt_ac_axioms                         fast
% 3.22/0.98  --preprocessed_out                      false
% 3.22/0.98  --preprocessed_stats                    false
% 3.22/0.98  
% 3.22/0.98  ------ Abstraction refinement Options
% 3.22/0.98  
% 3.22/0.98  --abstr_ref                             []
% 3.22/0.98  --abstr_ref_prep                        false
% 3.22/0.98  --abstr_ref_until_sat                   false
% 3.22/0.98  --abstr_ref_sig_restrict                funpre
% 3.22/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.22/0.98  --abstr_ref_under                       []
% 3.22/0.98  
% 3.22/0.98  ------ SAT Options
% 3.22/0.98  
% 3.22/0.98  --sat_mode                              false
% 3.22/0.98  --sat_fm_restart_options                ""
% 3.22/0.98  --sat_gr_def                            false
% 3.22/0.98  --sat_epr_types                         true
% 3.22/0.98  --sat_non_cyclic_types                  false
% 3.22/0.98  --sat_finite_models                     false
% 3.22/0.98  --sat_fm_lemmas                         false
% 3.22/0.98  --sat_fm_prep                           false
% 3.22/0.98  --sat_fm_uc_incr                        true
% 3.22/0.98  --sat_out_model                         small
% 3.22/0.98  --sat_out_clauses                       false
% 3.22/0.98  
% 3.22/0.98  ------ QBF Options
% 3.22/0.98  
% 3.22/0.98  --qbf_mode                              false
% 3.22/0.98  --qbf_elim_univ                         false
% 3.22/0.98  --qbf_dom_inst                          none
% 3.22/0.98  --qbf_dom_pre_inst                      false
% 3.22/0.98  --qbf_sk_in                             false
% 3.22/0.98  --qbf_pred_elim                         true
% 3.22/0.98  --qbf_split                             512
% 3.22/0.98  
% 3.22/0.98  ------ BMC1 Options
% 3.22/0.98  
% 3.22/0.98  --bmc1_incremental                      false
% 3.22/0.98  --bmc1_axioms                           reachable_all
% 3.22/0.98  --bmc1_min_bound                        0
% 3.22/0.98  --bmc1_max_bound                        -1
% 3.22/0.98  --bmc1_max_bound_default                -1
% 3.22/0.98  --bmc1_symbol_reachability              true
% 3.22/0.98  --bmc1_property_lemmas                  false
% 3.22/0.98  --bmc1_k_induction                      false
% 3.22/0.98  --bmc1_non_equiv_states                 false
% 3.22/0.98  --bmc1_deadlock                         false
% 3.22/0.98  --bmc1_ucm                              false
% 3.22/0.98  --bmc1_add_unsat_core                   none
% 3.22/0.98  --bmc1_unsat_core_children              false
% 3.22/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.22/0.98  --bmc1_out_stat                         full
% 3.22/0.98  --bmc1_ground_init                      false
% 3.22/0.98  --bmc1_pre_inst_next_state              false
% 3.22/0.98  --bmc1_pre_inst_state                   false
% 3.22/0.98  --bmc1_pre_inst_reach_state             false
% 3.22/0.98  --bmc1_out_unsat_core                   false
% 3.22/0.98  --bmc1_aig_witness_out                  false
% 3.22/0.98  --bmc1_verbose                          false
% 3.22/0.98  --bmc1_dump_clauses_tptp                false
% 3.22/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.22/0.98  --bmc1_dump_file                        -
% 3.22/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.22/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.22/0.98  --bmc1_ucm_extend_mode                  1
% 3.22/0.98  --bmc1_ucm_init_mode                    2
% 3.22/0.98  --bmc1_ucm_cone_mode                    none
% 3.22/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.22/0.98  --bmc1_ucm_relax_model                  4
% 3.22/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.22/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.22/0.98  --bmc1_ucm_layered_model                none
% 3.22/0.98  --bmc1_ucm_max_lemma_size               10
% 3.22/0.98  
% 3.22/0.98  ------ AIG Options
% 3.22/0.98  
% 3.22/0.98  --aig_mode                              false
% 3.22/0.98  
% 3.22/0.98  ------ Instantiation Options
% 3.22/0.98  
% 3.22/0.98  --instantiation_flag                    true
% 3.22/0.98  --inst_sos_flag                         false
% 3.22/0.98  --inst_sos_phase                        true
% 3.22/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.22/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.22/0.98  --inst_lit_sel_side                     none
% 3.22/0.98  --inst_solver_per_active                1400
% 3.22/0.98  --inst_solver_calls_frac                1.
% 3.22/0.98  --inst_passive_queue_type               priority_queues
% 3.22/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.22/0.98  --inst_passive_queues_freq              [25;2]
% 3.22/0.98  --inst_dismatching                      true
% 3.22/0.98  --inst_eager_unprocessed_to_passive     true
% 3.22/0.98  --inst_prop_sim_given                   true
% 3.22/0.98  --inst_prop_sim_new                     false
% 3.22/0.98  --inst_subs_new                         false
% 3.22/0.98  --inst_eq_res_simp                      false
% 3.22/0.98  --inst_subs_given                       false
% 3.22/0.98  --inst_orphan_elimination               true
% 3.22/0.98  --inst_learning_loop_flag               true
% 3.22/0.98  --inst_learning_start                   3000
% 3.22/0.98  --inst_learning_factor                  2
% 3.22/0.98  --inst_start_prop_sim_after_learn       3
% 3.22/0.98  --inst_sel_renew                        solver
% 3.22/0.98  --inst_lit_activity_flag                true
% 3.22/0.98  --inst_restr_to_given                   false
% 3.22/0.98  --inst_activity_threshold               500
% 3.22/0.98  --inst_out_proof                        true
% 3.22/0.98  
% 3.22/0.98  ------ Resolution Options
% 3.22/0.98  
% 3.22/0.98  --resolution_flag                       false
% 3.22/0.98  --res_lit_sel                           adaptive
% 3.22/0.98  --res_lit_sel_side                      none
% 3.22/0.98  --res_ordering                          kbo
% 3.22/0.98  --res_to_prop_solver                    active
% 3.22/0.98  --res_prop_simpl_new                    false
% 3.22/0.98  --res_prop_simpl_given                  true
% 3.22/0.98  --res_passive_queue_type                priority_queues
% 3.22/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.22/0.98  --res_passive_queues_freq               [15;5]
% 3.22/0.98  --res_forward_subs                      full
% 3.22/0.98  --res_backward_subs                     full
% 3.22/0.98  --res_forward_subs_resolution           true
% 3.22/0.98  --res_backward_subs_resolution          true
% 3.22/0.98  --res_orphan_elimination                true
% 3.22/0.98  --res_time_limit                        2.
% 3.22/0.98  --res_out_proof                         true
% 3.22/0.98  
% 3.22/0.98  ------ Superposition Options
% 3.22/0.98  
% 3.22/0.98  --superposition_flag                    false
% 3.22/0.98  --sup_passive_queue_type                priority_queues
% 3.22/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.22/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.22/0.98  --demod_completeness_check              fast
% 3.22/0.98  --demod_use_ground                      true
% 3.22/0.98  --sup_to_prop_solver                    passive
% 3.22/0.98  --sup_prop_simpl_new                    true
% 3.22/0.98  --sup_prop_simpl_given                  true
% 3.22/0.98  --sup_fun_splitting                     false
% 3.22/0.98  --sup_smt_interval                      50000
% 3.22/0.98  
% 3.22/0.98  ------ Superposition Simplification Setup
% 3.22/0.98  
% 3.22/0.98  --sup_indices_passive                   []
% 3.22/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.22/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.98  --sup_full_bw                           [BwDemod]
% 3.22/0.98  --sup_immed_triv                        [TrivRules]
% 3.22/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.22/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.98  --sup_immed_bw_main                     []
% 3.22/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.22/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/0.98  
% 3.22/0.98  ------ Combination Options
% 3.22/0.98  
% 3.22/0.98  --comb_res_mult                         3
% 3.22/0.98  --comb_sup_mult                         2
% 3.22/0.98  --comb_inst_mult                        10
% 3.22/0.98  
% 3.22/0.98  ------ Debug Options
% 3.22/0.98  
% 3.22/0.98  --dbg_backtrace                         false
% 3.22/0.98  --dbg_dump_prop_clauses                 false
% 3.22/0.98  --dbg_dump_prop_clauses_file            -
% 3.22/0.98  --dbg_out_stat                          false
% 3.22/0.98  
% 3.22/0.98  
% 3.22/0.98  
% 3.22/0.98  
% 3.22/0.98  ------ Proving...
% 3.22/0.98  
% 3.22/0.98  
% 3.22/0.98  % SZS status Theorem for theBenchmark.p
% 3.22/0.98  
% 3.22/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.22/0.98  
% 3.22/0.98  fof(f1,axiom,(
% 3.22/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.22/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f8,plain,(
% 3.22/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.98    inference(ennf_transformation,[],[f1])).
% 3.22/0.98  
% 3.22/0.98  fof(f28,plain,(
% 3.22/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.22/0.98    inference(cnf_transformation,[],[f8])).
% 3.22/0.98  
% 3.22/0.98  fof(f3,axiom,(
% 3.22/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.22/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f19,plain,(
% 3.22/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.22/0.98    inference(nnf_transformation,[],[f3])).
% 3.22/0.98  
% 3.22/0.98  fof(f33,plain,(
% 3.22/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.22/0.98    inference(cnf_transformation,[],[f19])).
% 3.22/0.98  
% 3.22/0.98  fof(f2,axiom,(
% 3.22/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 3.22/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f9,plain,(
% 3.22/0.98    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.98    inference(ennf_transformation,[],[f2])).
% 3.22/0.98  
% 3.22/0.98  fof(f10,plain,(
% 3.22/0.98    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.98    inference(flattening,[],[f9])).
% 3.22/0.98  
% 3.22/0.98  fof(f17,plain,(
% 3.22/0.98    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),X0)))),
% 3.22/0.98    introduced(choice_axiom,[])).
% 3.22/0.98  
% 3.22/0.98  fof(f18,plain,(
% 3.22/0.98    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f17])).
% 3.22/0.98  
% 3.22/0.98  fof(f31,plain,(
% 3.22/0.98    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.22/0.98    inference(cnf_transformation,[],[f18])).
% 3.22/0.98  
% 3.22/0.98  fof(f30,plain,(
% 3.22/0.98    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.22/0.98    inference(cnf_transformation,[],[f18])).
% 3.22/0.98  
% 3.22/0.98  fof(f5,axiom,(
% 3.22/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (r2_hidden(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X3) & v4_pre_topc(X3,X0)) => r2_hidden(X2,X3)))))))),
% 3.22/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f13,plain,(
% 3.22/0.98    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : ((r2_hidden(X2,X3) | (~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.22/0.98    inference(ennf_transformation,[],[f5])).
% 3.22/0.98  
% 3.22/0.98  fof(f14,plain,(
% 3.22/0.98    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (r2_hidden(X2,X3) | ~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.22/0.98    inference(flattening,[],[f13])).
% 3.22/0.98  
% 3.22/0.98  fof(f20,plain,(
% 3.22/0.98    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (~r2_hidden(X2,X3) & r1_tarski(X1,X3) & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r2_hidden(X2,X3) | ~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.22/0.98    inference(nnf_transformation,[],[f14])).
% 3.22/0.98  
% 3.22/0.98  fof(f21,plain,(
% 3.22/0.98    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (~r2_hidden(X2,X3) & r1_tarski(X1,X3) & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X2,X4) | ~r1_tarski(X1,X4) | ~v4_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.22/0.98    inference(rectify,[],[f20])).
% 3.22/0.98  
% 3.22/0.98  fof(f22,plain,(
% 3.22/0.98    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X2,X3) & r1_tarski(X1,X3) & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(X2,sK1(X0,X1,X2)) & r1_tarski(X1,sK1(X0,X1,X2)) & v4_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.22/0.98    introduced(choice_axiom,[])).
% 3.22/0.98  
% 3.22/0.98  fof(f23,plain,(
% 3.22/0.98    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (~r2_hidden(X2,sK1(X0,X1,X2)) & r1_tarski(X1,sK1(X0,X1,X2)) & v4_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X2,X4) | ~r1_tarski(X1,X4) | ~v4_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.22/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).
% 3.22/0.99  
% 3.22/0.99  fof(f35,plain,(
% 3.22/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X2,X4) | ~r1_tarski(X1,X4) | ~v4_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~r2_hidden(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f23])).
% 3.22/0.99  
% 3.22/0.99  fof(f6,conjecture,(
% 3.22/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 3.22/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f7,negated_conjecture,(
% 3.22/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 3.22/0.99    inference(negated_conjecture,[],[f6])).
% 3.22/0.99  
% 3.22/0.99  fof(f15,plain,(
% 3.22/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.22/0.99    inference(ennf_transformation,[],[f7])).
% 3.22/0.99  
% 3.22/0.99  fof(f16,plain,(
% 3.22/0.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.22/0.99    inference(flattening,[],[f15])).
% 3.22/0.99  
% 3.22/0.99  fof(f26,plain,(
% 3.22/0.99    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,sK4)) & r1_tarski(X1,sK4) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.22/0.99    introduced(choice_axiom,[])).
% 3.22/0.99  
% 3.22/0.99  fof(f25,plain,(
% 3.22/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k2_pre_topc(X0,sK3),k2_pre_topc(X0,X2)) & r1_tarski(sK3,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.22/0.99    introduced(choice_axiom,[])).
% 3.22/0.99  
% 3.22/0.99  fof(f24,plain,(
% 3.22/0.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(sK2,X1),k2_pre_topc(sK2,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2))),
% 3.22/0.99    introduced(choice_axiom,[])).
% 3.22/0.99  
% 3.22/0.99  fof(f27,plain,(
% 3.22/0.99    ((~r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)) & r1_tarski(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2)),
% 3.22/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f26,f25,f24])).
% 3.22/0.99  
% 3.22/0.99  fof(f40,plain,(
% 3.22/0.99    l1_pre_topc(sK2)),
% 3.22/0.99    inference(cnf_transformation,[],[f27])).
% 3.22/0.99  
% 3.22/0.99  fof(f38,plain,(
% 3.22/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | r1_tarski(X1,sK1(X0,X1,X2)) | ~r2_hidden(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f23])).
% 3.22/0.99  
% 3.22/0.99  fof(f37,plain,(
% 3.22/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | v4_pre_topc(sK1(X0,X1,X2),X0) | ~r2_hidden(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f23])).
% 3.22/0.99  
% 3.22/0.99  fof(f36,plain,(
% 3.22/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f23])).
% 3.22/0.99  
% 3.22/0.99  fof(f39,plain,(
% 3.22/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | ~r2_hidden(X2,sK1(X0,X1,X2)) | ~r2_hidden(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f23])).
% 3.22/0.99  
% 3.22/0.99  fof(f4,axiom,(
% 3.22/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.22/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f11,plain,(
% 3.22/0.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.22/0.99    inference(ennf_transformation,[],[f4])).
% 3.22/0.99  
% 3.22/0.99  fof(f12,plain,(
% 3.22/0.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.22/0.99    inference(flattening,[],[f11])).
% 3.22/0.99  
% 3.22/0.99  fof(f34,plain,(
% 3.22/0.99    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f12])).
% 3.22/0.99  
% 3.22/0.99  fof(f32,plain,(
% 3.22/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.22/0.99    inference(cnf_transformation,[],[f19])).
% 3.22/0.99  
% 3.22/0.99  fof(f44,plain,(
% 3.22/0.99    ~r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),
% 3.22/0.99    inference(cnf_transformation,[],[f27])).
% 3.22/0.99  
% 3.22/0.99  fof(f43,plain,(
% 3.22/0.99    r1_tarski(sK3,sK4)),
% 3.22/0.99    inference(cnf_transformation,[],[f27])).
% 3.22/0.99  
% 3.22/0.99  fof(f42,plain,(
% 3.22/0.99    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 3.22/0.99    inference(cnf_transformation,[],[f27])).
% 3.22/0.99  
% 3.22/0.99  fof(f41,plain,(
% 3.22/0.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 3.22/0.99    inference(cnf_transformation,[],[f27])).
% 3.22/0.99  
% 3.22/0.99  cnf(c_0,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.22/0.99      | ~ r2_hidden(X2,X0)
% 3.22/0.99      | r2_hidden(X2,X1) ),
% 3.22/0.99      inference(cnf_transformation,[],[f28]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4,plain,
% 3.22/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.22/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_122,plain,
% 3.22/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.22/0.99      inference(prop_impl,[status(thm)],[c_4]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_159,plain,
% 3.22/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.22/0.99      inference(bin_hyper_res,[status(thm)],[c_0,c_122]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1538,plain,
% 3.22/0.99      ( ~ r1_tarski(X0_41,X1_41)
% 3.22/0.99      | ~ r2_hidden(X2_41,X0_41)
% 3.22/0.99      | r2_hidden(X2_41,X1_41) ),
% 3.22/0.99      inference(subtyping,[status(esa)],[c_159]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_3546,plain,
% 3.22/0.99      ( ~ r1_tarski(sK4,X0_41)
% 3.22/0.99      | r2_hidden(sK0(u1_struct_0(sK2),sK3,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)))),X0_41)
% 3.22/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK2),sK3,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)))),sK4) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1538]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4080,plain,
% 3.22/0.99      ( ~ r1_tarski(sK4,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
% 3.22/0.99      | r2_hidden(sK0(u1_struct_0(sK2),sK3,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)))),sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
% 3.22/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK2),sK3,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)))),sK4) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_3546]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1648,plain,
% 3.22/0.99      ( ~ r1_tarski(sK3,sK4)
% 3.22/0.99      | r2_hidden(X0_41,sK4)
% 3.22/0.99      | ~ r2_hidden(X0_41,sK3) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1538]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_3122,plain,
% 3.22/0.99      ( ~ r1_tarski(sK3,sK4)
% 3.22/0.99      | r2_hidden(sK0(u1_struct_0(sK2),sK3,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)))),sK4)
% 3.22/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK2),sK3,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)))),sK3) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1648]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1,plain,
% 3.22/0.99      ( r1_tarski(X0,X1)
% 3.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
% 3.22/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 3.22/0.99      | ~ r2_hidden(sK0(X2,X0,X1),X1) ),
% 3.22/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1547,plain,
% 3.22/0.99      ( r1_tarski(X0_41,X1_41)
% 3.22/0.99      | ~ m1_subset_1(X0_41,k1_zfmisc_1(X2_41))
% 3.22/0.99      | ~ m1_subset_1(X1_41,k1_zfmisc_1(X2_41))
% 3.22/0.99      | ~ r2_hidden(sK0(X2_41,X0_41,X1_41),X1_41) ),
% 3.22/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1688,plain,
% 3.22/0.99      ( r1_tarski(sK3,X0_41)
% 3.22/0.99      | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK2),sK3,X0_41),X0_41) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1547]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2758,plain,
% 3.22/0.99      ( r1_tarski(sK3,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
% 3.22/0.99      | ~ m1_subset_1(sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK2),sK3,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)))),sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)))) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1688]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2,plain,
% 3.22/0.99      ( r1_tarski(X0,X1)
% 3.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
% 3.22/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 3.22/0.99      | r2_hidden(sK0(X2,X0,X1),X0) ),
% 3.22/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1546,plain,
% 3.22/0.99      ( r1_tarski(X0_41,X1_41)
% 3.22/0.99      | ~ m1_subset_1(X0_41,k1_zfmisc_1(X2_41))
% 3.22/0.99      | ~ m1_subset_1(X1_41,k1_zfmisc_1(X2_41))
% 3.22/0.99      | r2_hidden(sK0(X2_41,X0_41,X1_41),X0_41) ),
% 3.22/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1673,plain,
% 3.22/0.99      ( r1_tarski(sK3,X0_41)
% 3.22/0.99      | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | r2_hidden(sK0(u1_struct_0(sK2),sK3,X0_41),sK3) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1546]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2759,plain,
% 3.22/0.99      ( r1_tarski(sK3,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
% 3.22/0.99      | ~ m1_subset_1(sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | r2_hidden(sK0(u1_struct_0(sK2),sK3,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)))),sK3) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1673]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_11,plain,
% 3.22/0.99      ( ~ v4_pre_topc(X0,X1)
% 3.22/0.99      | ~ r1_tarski(X2,X0)
% 3.22/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/0.99      | r2_hidden(X3,X0)
% 3.22/0.99      | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
% 3.22/0.99      | ~ r2_hidden(X3,u1_struct_0(X1))
% 3.22/0.99      | ~ l1_pre_topc(X1) ),
% 3.22/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_16,negated_conjecture,
% 3.22/0.99      ( l1_pre_topc(sK2) ),
% 3.22/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_255,plain,
% 3.22/0.99      ( ~ v4_pre_topc(X0,sK2)
% 3.22/0.99      | ~ r1_tarski(X1,X0)
% 3.22/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | r2_hidden(X2,X0)
% 3.22/0.99      | ~ r2_hidden(X2,k2_pre_topc(sK2,X1))
% 3.22/0.99      | ~ r2_hidden(X2,u1_struct_0(sK2)) ),
% 3.22/0.99      inference(resolution,[status(thm)],[c_11,c_16]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1537,plain,
% 3.22/0.99      ( ~ v4_pre_topc(X0_41,sK2)
% 3.22/0.99      | ~ r1_tarski(X1_41,X0_41)
% 3.22/0.99      | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | ~ m1_subset_1(X1_41,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | r2_hidden(X2_41,X0_41)
% 3.22/0.99      | ~ r2_hidden(X2_41,k2_pre_topc(sK2,X1_41))
% 3.22/0.99      | ~ r2_hidden(X2_41,u1_struct_0(sK2)) ),
% 3.22/0.99      inference(subtyping,[status(esa)],[c_255]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2073,plain,
% 3.22/0.99      ( ~ v4_pre_topc(sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),sK2)
% 3.22/0.99      | ~ r1_tarski(X0_41,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
% 3.22/0.99      | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | ~ m1_subset_1(sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | r2_hidden(X1_41,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
% 3.22/0.99      | ~ r2_hidden(X1_41,k2_pre_topc(sK2,X0_41))
% 3.22/0.99      | ~ r2_hidden(X1_41,u1_struct_0(sK2)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1537]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2320,plain,
% 3.22/0.99      ( ~ v4_pre_topc(sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),sK2)
% 3.22/0.99      | ~ r1_tarski(X0_41,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
% 3.22/0.99      | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | ~ m1_subset_1(sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
% 3.22/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,X0_41))
% 3.22/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_2073]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2322,plain,
% 3.22/0.99      ( ~ v4_pre_topc(sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),sK2)
% 3.22/0.99      | ~ r1_tarski(sK3,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
% 3.22/0.99      | ~ m1_subset_1(sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
% 3.22/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,sK3))
% 3.22/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_2320]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_8,plain,
% 3.22/0.99      ( r1_tarski(X0,sK1(X1,X0,X2))
% 3.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/0.99      | r2_hidden(X2,k2_pre_topc(X1,X0))
% 3.22/0.99      | ~ r2_hidden(X2,u1_struct_0(X1))
% 3.22/0.99      | ~ l1_pre_topc(X1) ),
% 3.22/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_298,plain,
% 3.22/0.99      ( r1_tarski(X0,sK1(sK2,X0,X1))
% 3.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | r2_hidden(X1,k2_pre_topc(sK2,X0))
% 3.22/0.99      | ~ r2_hidden(X1,u1_struct_0(sK2)) ),
% 3.22/0.99      inference(resolution,[status(thm)],[c_8,c_16]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1535,plain,
% 3.22/0.99      ( r1_tarski(X0_41,sK1(sK2,X0_41,X1_41))
% 3.22/0.99      | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | r2_hidden(X1_41,k2_pre_topc(sK2,X0_41))
% 3.22/0.99      | ~ r2_hidden(X1_41,u1_struct_0(sK2)) ),
% 3.22/0.99      inference(subtyping,[status(esa)],[c_298]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1836,plain,
% 3.22/0.99      ( r1_tarski(X0_41,sK1(sK2,X0_41,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
% 3.22/0.99      | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,X0_41))
% 3.22/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1535]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1945,plain,
% 3.22/0.99      ( r1_tarski(sK4,sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
% 3.22/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,sK4))
% 3.22/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1836]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_9,plain,
% 3.22/0.99      ( v4_pre_topc(sK1(X0,X1,X2),X0)
% 3.22/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.22/0.99      | r2_hidden(X2,k2_pre_topc(X0,X1))
% 3.22/0.99      | ~ r2_hidden(X2,u1_struct_0(X0))
% 3.22/0.99      | ~ l1_pre_topc(X0) ),
% 3.22/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_343,plain,
% 3.22/0.99      ( v4_pre_topc(sK1(sK2,X0,X1),sK2)
% 3.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | r2_hidden(X1,k2_pre_topc(sK2,X0))
% 3.22/0.99      | ~ r2_hidden(X1,u1_struct_0(sK2)) ),
% 3.22/0.99      inference(resolution,[status(thm)],[c_9,c_16]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1532,plain,
% 3.22/0.99      ( v4_pre_topc(sK1(sK2,X0_41,X1_41),sK2)
% 3.22/0.99      | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | r2_hidden(X1_41,k2_pre_topc(sK2,X0_41))
% 3.22/0.99      | ~ r2_hidden(X1_41,u1_struct_0(sK2)) ),
% 3.22/0.99      inference(subtyping,[status(esa)],[c_343]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1839,plain,
% 3.22/0.99      ( v4_pre_topc(sK1(sK2,X0_41,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),sK2)
% 3.22/0.99      | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,X0_41))
% 3.22/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1532]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1939,plain,
% 3.22/0.99      ( v4_pre_topc(sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),sK2)
% 3.22/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,sK4))
% 3.22/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1839]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_10,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/0.99      | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/0.99      | r2_hidden(X2,k2_pre_topc(X1,X0))
% 3.22/0.99      | ~ r2_hidden(X2,u1_struct_0(X1))
% 3.22/0.99      | ~ l1_pre_topc(X1) ),
% 3.22/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_281,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | m1_subset_1(sK1(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | r2_hidden(X1,k2_pre_topc(sK2,X0))
% 3.22/0.99      | ~ r2_hidden(X1,u1_struct_0(sK2)) ),
% 3.22/0.99      inference(resolution,[status(thm)],[c_10,c_16]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1536,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | m1_subset_1(sK1(sK2,X0_41,X1_41),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | r2_hidden(X1_41,k2_pre_topc(sK2,X0_41))
% 3.22/0.99      | ~ r2_hidden(X1_41,u1_struct_0(sK2)) ),
% 3.22/0.99      inference(subtyping,[status(esa)],[c_281]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1838,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | m1_subset_1(sK1(sK2,X0_41,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,X0_41))
% 3.22/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1536]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1933,plain,
% 3.22/0.99      ( m1_subset_1(sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,sK4))
% 3.22/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1838]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_7,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/0.99      | ~ r2_hidden(X2,sK1(X1,X0,X2))
% 3.22/0.99      | r2_hidden(X2,k2_pre_topc(X1,X0))
% 3.22/0.99      | ~ r2_hidden(X2,u1_struct_0(X1))
% 3.22/0.99      | ~ l1_pre_topc(X1) ),
% 3.22/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_315,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | ~ r2_hidden(X1,sK1(sK2,X0,X1))
% 3.22/0.99      | r2_hidden(X1,k2_pre_topc(sK2,X0))
% 3.22/0.99      | ~ r2_hidden(X1,u1_struct_0(sK2)) ),
% 3.22/0.99      inference(resolution,[status(thm)],[c_7,c_16]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1534,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | ~ r2_hidden(X1_41,sK1(sK2,X0_41,X1_41))
% 3.22/0.99      | r2_hidden(X1_41,k2_pre_topc(sK2,X0_41))
% 3.22/0.99      | ~ r2_hidden(X1_41,u1_struct_0(sK2)) ),
% 3.22/0.99      inference(subtyping,[status(esa)],[c_315]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1837,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),sK1(sK2,X0_41,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
% 3.22/0.99      | r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,X0_41))
% 3.22/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1534]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1927,plain,
% 3.22/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),sK1(sK2,sK4,sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
% 3.22/0.99      | r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,sK4))
% 3.22/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1837]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1759,plain,
% 3.22/0.99      ( ~ r1_tarski(k2_pre_topc(sK2,sK3),X0_41)
% 3.22/0.99      | r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),X0_41)
% 3.22/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,sK3)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1538]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1800,plain,
% 3.22/0.99      ( ~ r1_tarski(k2_pre_topc(sK2,sK3),u1_struct_0(sK2))
% 3.22/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,sK3))
% 3.22/0.99      | r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1759]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_6,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/0.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/0.99      | ~ l1_pre_topc(X1) ),
% 3.22/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_332,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.22/0.99      inference(resolution,[status(thm)],[c_6,c_16]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1533,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | m1_subset_1(k2_pre_topc(sK2,X0_41),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.22/0.99      inference(subtyping,[status(esa)],[c_332]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1764,plain,
% 3.22/0.99      ( m1_subset_1(k2_pre_topc(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1533]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1693,plain,
% 3.22/0.99      ( r1_tarski(k2_pre_topc(sK2,X0_41),X1_41)
% 3.22/0.99      | ~ m1_subset_1(X1_41,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | ~ m1_subset_1(k2_pre_topc(sK2,X0_41),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,X0_41),X1_41),X1_41) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1547]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1740,plain,
% 3.22/0.99      ( r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))
% 3.22/0.99      | ~ m1_subset_1(k2_pre_topc(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | ~ m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,sK4)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1693]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1678,plain,
% 3.22/0.99      ( r1_tarski(k2_pre_topc(sK2,X0_41),X1_41)
% 3.22/0.99      | ~ m1_subset_1(X1_41,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | ~ m1_subset_1(k2_pre_topc(sK2,X0_41),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,X0_41),X1_41),k2_pre_topc(sK2,X0_41)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1546]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1737,plain,
% 3.22/0.99      ( r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))
% 3.22/0.99      | ~ m1_subset_1(k2_pre_topc(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | ~ m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | r2_hidden(sK0(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,sK3)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1678]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_5,plain,
% 3.22/0.99      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.22/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1543,plain,
% 3.22/0.99      ( r1_tarski(X0_41,X1_41)
% 3.22/0.99      | ~ m1_subset_1(X0_41,k1_zfmisc_1(X1_41)) ),
% 3.22/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1640,plain,
% 3.22/0.99      ( r1_tarski(k2_pre_topc(sK2,X0_41),u1_struct_0(sK2))
% 3.22/0.99      | ~ m1_subset_1(k2_pre_topc(sK2,X0_41),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1543]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1642,plain,
% 3.22/0.99      ( r1_tarski(k2_pre_topc(sK2,sK3),u1_struct_0(sK2))
% 3.22/0.99      | ~ m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1640]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1581,plain,
% 3.22/0.99      ( m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1533]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_12,negated_conjecture,
% 3.22/0.99      ( ~ r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)) ),
% 3.22/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_13,negated_conjecture,
% 3.22/0.99      ( r1_tarski(sK3,sK4) ),
% 3.22/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_14,negated_conjecture,
% 3.22/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.22/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_15,negated_conjecture,
% 3.22/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.22/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(contradiction,plain,
% 3.22/0.99      ( $false ),
% 3.22/0.99      inference(minisat,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_4080,c_3122,c_2758,c_2759,c_2322,c_1945,c_1939,c_1933,
% 3.22/0.99                 c_1927,c_1800,c_1764,c_1740,c_1737,c_1642,c_1581,c_12,
% 3.22/0.99                 c_13,c_14,c_15]) ).
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.22/0.99  
% 3.22/0.99  ------                               Statistics
% 3.22/0.99  
% 3.22/0.99  ------ General
% 3.22/0.99  
% 3.22/0.99  abstr_ref_over_cycles:                  0
% 3.22/0.99  abstr_ref_under_cycles:                 0
% 3.22/0.99  gc_basic_clause_elim:                   0
% 3.22/0.99  forced_gc_time:                         0
% 3.22/0.99  parsing_time:                           0.01
% 3.22/0.99  unif_index_cands_time:                  0.
% 3.22/0.99  unif_index_add_time:                    0.
% 3.22/0.99  orderings_time:                         0.
% 3.22/0.99  out_proof_time:                         0.011
% 3.22/0.99  total_time:                             0.143
% 3.22/0.99  num_of_symbols:                         43
% 3.22/0.99  num_of_terms:                           3047
% 3.22/0.99  
% 3.22/0.99  ------ Preprocessing
% 3.22/0.99  
% 3.22/0.99  num_of_splits:                          0
% 3.22/0.99  num_of_split_atoms:                     0
% 3.22/0.99  num_of_reused_defs:                     0
% 3.22/0.99  num_eq_ax_congr_red:                    0
% 3.22/0.99  num_of_sem_filtered_clauses:            0
% 3.22/0.99  num_of_subtypes:                        2
% 3.22/0.99  monotx_restored_types:                  0
% 3.22/0.99  sat_num_of_epr_types:                   0
% 3.22/0.99  sat_num_of_non_cyclic_types:            0
% 3.22/0.99  sat_guarded_non_collapsed_types:        0
% 3.22/0.99  num_pure_diseq_elim:                    0
% 3.22/0.99  simp_replaced_by:                       0
% 3.22/0.99  res_preprocessed:                       33
% 3.22/0.99  prep_upred:                             0
% 3.22/0.99  prep_unflattend:                        0
% 3.22/0.99  smt_new_axioms:                         0
% 3.22/0.99  pred_elim_cands:                        4
% 3.22/0.99  pred_elim:                              1
% 3.22/0.99  pred_elim_cl:                           1
% 3.22/0.99  pred_elim_cycles:                       6
% 3.22/0.99  merged_defs:                            4
% 3.22/0.99  merged_defs_ncl:                        0
% 3.22/0.99  bin_hyper_res:                          5
% 3.22/0.99  prep_cycles:                            2
% 3.22/0.99  pred_elim_time:                         0.022
% 3.22/0.99  splitting_time:                         0.
% 3.22/0.99  sem_filter_time:                        0.
% 3.22/0.99  monotx_time:                            0.
% 3.22/0.99  subtype_inf_time:                       0.
% 3.22/0.99  
% 3.22/0.99  ------ Problem properties
% 3.22/0.99  
% 3.22/0.99  clauses:                                16
% 3.22/0.99  conjectures:                            4
% 3.22/0.99  epr:                                    2
% 3.22/0.99  horn:                                   11
% 3.22/0.99  ground:                                 4
% 3.22/0.99  unary:                                  4
% 3.22/0.99  binary:                                 3
% 3.22/0.99  lits:                                   48
% 3.22/0.99  lits_eq:                                0
% 3.22/0.99  fd_pure:                                0
% 3.22/0.99  fd_pseudo:                              0
% 3.22/0.99  fd_cond:                                0
% 3.22/0.99  fd_pseudo_cond:                         0
% 3.22/0.99  ac_symbols:                             0
% 3.22/0.99  
% 3.22/0.99  ------ Propositional Solver
% 3.22/0.99  
% 3.22/0.99  prop_solver_calls:                      22
% 3.22/0.99  prop_fast_solver_calls:                 487
% 3.22/0.99  smt_solver_calls:                       0
% 3.22/0.99  smt_fast_solver_calls:                  0
% 3.22/0.99  prop_num_of_clauses:                    1130
% 3.22/0.99  prop_preprocess_simplified:             2848
% 3.22/0.99  prop_fo_subsumed:                       9
% 3.22/0.99  prop_solver_time:                       0.
% 3.22/0.99  smt_solver_time:                        0.
% 3.22/0.99  smt_fast_solver_time:                   0.
% 3.22/0.99  prop_fast_solver_time:                  0.
% 3.22/0.99  prop_unsat_core_time:                   0.
% 3.22/0.99  
% 3.22/0.99  ------ QBF
% 3.22/0.99  
% 3.22/0.99  qbf_q_res:                              0
% 3.22/0.99  qbf_num_tautologies:                    0
% 3.22/0.99  qbf_prep_cycles:                        0
% 3.22/0.99  
% 3.22/0.99  ------ BMC1
% 3.22/0.99  
% 3.22/0.99  bmc1_current_bound:                     -1
% 3.22/0.99  bmc1_last_solved_bound:                 -1
% 3.22/0.99  bmc1_unsat_core_size:                   -1
% 3.22/0.99  bmc1_unsat_core_parents_size:           -1
% 3.22/0.99  bmc1_merge_next_fun:                    0
% 3.22/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.22/0.99  
% 3.22/0.99  ------ Instantiation
% 3.22/0.99  
% 3.22/0.99  inst_num_of_clauses:                    357
% 3.22/0.99  inst_num_in_passive:                    87
% 3.22/0.99  inst_num_in_active:                     217
% 3.22/0.99  inst_num_in_unprocessed:                52
% 3.22/0.99  inst_num_of_loops:                      355
% 3.22/0.99  inst_num_of_learning_restarts:          0
% 3.22/0.99  inst_num_moves_active_passive:          129
% 3.22/0.99  inst_lit_activity:                      0
% 3.22/0.99  inst_lit_activity_moves:                0
% 3.22/0.99  inst_num_tautologies:                   0
% 3.22/0.99  inst_num_prop_implied:                  0
% 3.22/0.99  inst_num_existing_simplified:           0
% 3.22/0.99  inst_num_eq_res_simplified:             0
% 3.22/0.99  inst_num_child_elim:                    0
% 3.22/0.99  inst_num_of_dismatching_blockings:      138
% 3.22/0.99  inst_num_of_non_proper_insts:           385
% 3.22/0.99  inst_num_of_duplicates:                 0
% 3.22/0.99  inst_inst_num_from_inst_to_res:         0
% 3.22/0.99  inst_dismatching_checking_time:         0.
% 3.22/0.99  
% 3.22/0.99  ------ Resolution
% 3.22/0.99  
% 3.22/0.99  res_num_of_clauses:                     0
% 3.22/0.99  res_num_in_passive:                     0
% 3.22/0.99  res_num_in_active:                      0
% 3.22/0.99  res_num_of_loops:                       35
% 3.22/0.99  res_forward_subset_subsumed:            37
% 3.22/0.99  res_backward_subset_subsumed:           0
% 3.22/0.99  res_forward_subsumed:                   0
% 3.22/0.99  res_backward_subsumed:                  0
% 3.22/0.99  res_forward_subsumption_resolution:     2
% 3.22/0.99  res_backward_subsumption_resolution:    0
% 3.22/0.99  res_clause_to_clause_subsumption:       410
% 3.22/0.99  res_orphan_elimination:                 0
% 3.22/0.99  res_tautology_del:                      74
% 3.22/0.99  res_num_eq_res_simplified:              0
% 3.22/0.99  res_num_sel_changes:                    0
% 3.22/0.99  res_moves_from_active_to_pass:          0
% 3.22/0.99  
% 3.22/0.99  ------ Superposition
% 3.22/0.99  
% 3.22/0.99  sup_time_total:                         0.
% 3.22/0.99  sup_time_generating:                    0.
% 3.22/0.99  sup_time_sim_full:                      0.
% 3.22/0.99  sup_time_sim_immed:                     0.
% 3.22/0.99  
% 3.22/0.99  sup_num_of_clauses:                     0
% 3.22/0.99  sup_num_in_active:                      0
% 3.22/0.99  sup_num_in_passive:                     0
% 3.22/0.99  sup_num_of_loops:                       0
% 3.22/0.99  sup_fw_superposition:                   0
% 3.22/0.99  sup_bw_superposition:                   0
% 3.22/0.99  sup_immediate_simplified:               0
% 3.22/0.99  sup_given_eliminated:                   0
% 3.22/0.99  comparisons_done:                       0
% 3.22/0.99  comparisons_avoided:                    0
% 3.22/0.99  
% 3.22/0.99  ------ Simplifications
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  sim_fw_subset_subsumed:                 0
% 3.22/0.99  sim_bw_subset_subsumed:                 0
% 3.22/0.99  sim_fw_subsumed:                        0
% 3.22/0.99  sim_bw_subsumed:                        0
% 3.22/0.99  sim_fw_subsumption_res:                 0
% 3.22/0.99  sim_bw_subsumption_res:                 0
% 3.22/0.99  sim_tautology_del:                      0
% 3.22/0.99  sim_eq_tautology_del:                   0
% 3.22/0.99  sim_eq_res_simp:                        0
% 3.22/0.99  sim_fw_demodulated:                     0
% 3.22/0.99  sim_bw_demodulated:                     0
% 3.22/0.99  sim_light_normalised:                   0
% 3.22/0.99  sim_joinable_taut:                      0
% 3.22/0.99  sim_joinable_simp:                      0
% 3.22/0.99  sim_ac_normalised:                      0
% 3.22/0.99  sim_smt_subsumption:                    0
% 3.22/0.99  
%------------------------------------------------------------------------------
