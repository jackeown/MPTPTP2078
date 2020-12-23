%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1118+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:55 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 222 expanded)
%              Number of clauses        :   55 (  60 expanded)
%              Number of leaves         :   11 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :  409 (1200 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

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

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X2,X4)
      | ~ r1_tarski(X1,X4)
      | ~ v4_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,sK4))
        & r1_tarski(X1,sK4)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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

fof(f26,plain,
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

fof(f29,plain,
    ( ~ r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))
    & r1_tarski(sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f28,f27,f26])).

fof(f42,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | r1_tarski(X1,sK1(X0,X1,X2))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | v4_pre_topc(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ r2_hidden(X2,sK1(X0,X1,X2))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

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

fof(f17,plain,(
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

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f46,plain,(
    ~ r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)) ),
    inference(cnf_transformation,[],[f29])).

fof(f45,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f44,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_618,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | ~ r1_tarski(X1_41,X2_41)
    | r1_tarski(X0_41,X2_41) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1195,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | ~ r1_tarski(X1_41,sK1(sK2,sK4,sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
    | r1_tarski(X0_41,sK1(sK2,sK4,sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)))) ),
    inference(instantiation,[status(thm)],[c_618])).

cnf(c_1594,plain,
    ( r1_tarski(X0_41,sK1(sK2,sK4,sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
    | ~ r1_tarski(X0_41,sK4)
    | ~ r1_tarski(sK4,sK1(sK2,sK4,sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)))) ),
    inference(instantiation,[status(thm)],[c_1195])).

cnf(c_1596,plain,
    ( ~ r1_tarski(sK4,sK1(sK2,sK4,sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
    | r1_tarski(sK3,sK1(sK2,sK4,sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
    | ~ r1_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1594])).

cnf(c_11,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X3,X0)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ r2_hidden(X3,u1_struct_0(X1))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_276,plain,
    ( ~ v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k2_pre_topc(sK2,X1))
    | ~ r2_hidden(X2,u1_struct_0(sK2))
    | ~ r1_tarski(X1,X0) ),
    inference(resolution,[status(thm)],[c_11,c_16])).

cnf(c_610,plain,
    ( ~ v4_pre_topc(X0_41,sK2)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0_44,X0_41)
    | ~ r2_hidden(X0_44,k2_pre_topc(sK2,X1_41))
    | ~ r2_hidden(X0_44,u1_struct_0(sK2))
    | ~ r1_tarski(X1_41,X0_41) ),
    inference(subtyping,[status(esa)],[c_276])).

cnf(c_921,plain,
    ( ~ v4_pre_topc(sK1(sK2,sK4,sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),sK2)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK1(sK2,sK4,sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0_44,sK1(sK2,sK4,sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
    | ~ r2_hidden(X0_44,k2_pre_topc(sK2,X0_41))
    | ~ r2_hidden(X0_44,u1_struct_0(sK2))
    | ~ r1_tarski(X0_41,sK1(sK2,sK4,sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)))) ),
    inference(instantiation,[status(thm)],[c_610])).

cnf(c_1105,plain,
    ( ~ v4_pre_topc(sK1(sK2,sK4,sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),sK2)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK1(sK2,sK4,sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),sK1(sK2,sK4,sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
    | ~ r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,X0_41))
    | ~ r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2))
    | ~ r1_tarski(X0_41,sK1(sK2,sK4,sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)))) ),
    inference(instantiation,[status(thm)],[c_921])).

cnf(c_1107,plain,
    ( ~ v4_pre_topc(sK1(sK2,sK4,sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),sK2)
    | ~ m1_subset_1(sK1(sK2,sK4,sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),sK1(sK2,sK4,sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
    | ~ r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,sK3))
    | ~ r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2))
    | ~ r1_tarski(sK3,sK1(sK2,sK4,sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)))) ),
    inference(instantiation,[status(thm)],[c_1105])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ r2_hidden(X2,u1_struct_0(X1))
    | r1_tarski(X0,sK1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_319,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,k2_pre_topc(sK2,X0))
    | ~ r2_hidden(X1,u1_struct_0(sK2))
    | r1_tarski(X0,sK1(sK2,X0,X1)) ),
    inference(resolution,[status(thm)],[c_8,c_16])).

cnf(c_608,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0_44,k2_pre_topc(sK2,X0_41))
    | ~ r2_hidden(X0_44,u1_struct_0(sK2))
    | r1_tarski(X0_41,sK1(sK2,X0_41,X0_44)) ),
    inference(subtyping,[status(esa)],[c_319])).

cnf(c_745,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,X0_41))
    | ~ r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2))
    | r1_tarski(X0_41,sK1(sK2,X0_41,sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)))) ),
    inference(instantiation,[status(thm)],[c_608])).

cnf(c_883,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,sK4))
    | ~ r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2))
    | r1_tarski(sK4,sK1(sK2,sK4,sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)))) ),
    inference(instantiation,[status(thm)],[c_745])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ r2_hidden(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_302,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,k2_pre_topc(sK2,X0))
    | ~ r2_hidden(X1,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_10,c_16])).

cnf(c_609,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0_41,X0_44),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0_44,k2_pre_topc(sK2,X0_41))
    | ~ r2_hidden(X0_44,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_302])).

cnf(c_748,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0_41,sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,X0_41))
    | ~ r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_609])).

cnf(c_868,plain,
    ( m1_subset_1(sK1(sK2,sK4,sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,sK4))
    | ~ r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_748])).

cnf(c_9,plain,
    ( v4_pre_topc(sK1(X0,X1,X2),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ r2_hidden(X2,u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_259,plain,
    ( v4_pre_topc(sK1(sK2,X0,X1),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,k2_pre_topc(sK2,X0))
    | ~ r2_hidden(X1,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_9,c_16])).

cnf(c_611,plain,
    ( v4_pre_topc(sK1(sK2,X0_41,X0_44),sK2)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0_44,k2_pre_topc(sK2,X0_41))
    | ~ r2_hidden(X0_44,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_259])).

cnf(c_747,plain,
    ( v4_pre_topc(sK1(sK2,X0_41,sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),sK2)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,X0_41))
    | ~ r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_611])).

cnf(c_863,plain,
    ( v4_pre_topc(sK1(sK2,sK4,sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))),sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,sK4))
    | ~ r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_747])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,sK1(X1,X0,X2))
    | r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ r2_hidden(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_336,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,sK1(sK2,X0,X1))
    | r2_hidden(X1,k2_pre_topc(sK2,X0))
    | ~ r2_hidden(X1,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_7,c_16])).

cnf(c_607,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0_44,sK1(sK2,X0_41,X0_44))
    | r2_hidden(X0_44,k2_pre_topc(sK2,X0_41))
    | ~ r2_hidden(X0_44,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_336])).

cnf(c_746,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),sK1(sK2,X0_41,sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
    | r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,X0_41))
    | ~ r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_607])).

cnf(c_858,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),sK1(sK2,sK4,sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4))))
    | r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,sK4))
    | ~ r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_746])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_616,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X1_41))
    | r1_tarski(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_774,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(X0_41))
    | r1_tarski(k2_pre_topc(sK2,sK3),X0_41) ),
    inference(instantiation,[status(thm)],[c_616])).

cnf(c_837,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k2_pre_topc(sK2,sK3),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_774])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_619,plain,
    ( ~ r2_hidden(X0_44,X0_41)
    | r2_hidden(X0_44,X1_41)
    | ~ r1_tarski(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_721,plain,
    ( r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),X0_41)
    | ~ r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,sK3))
    | ~ r1_tarski(k2_pre_topc(sK2,sK3),X0_41) ),
    inference(instantiation,[status(thm)],[c_619])).

cnf(c_744,plain,
    ( ~ r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,sK3))
    | r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),u1_struct_0(sK2))
    | ~ r1_tarski(k2_pre_topc(sK2,sK3),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_621,plain,
    ( ~ r2_hidden(sK0(X0_41,X1_41),X1_41)
    | r1_tarski(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_712,plain,
    ( ~ r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,sK4))
    | r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_621])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_620,plain,
    ( r2_hidden(sK0(X0_41,X1_41),X0_41)
    | r1_tarski(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_709,plain,
    ( r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)),k2_pre_topc(sK2,sK3))
    | r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_620])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_353,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[status(thm)],[c_3,c_16])).

cnf(c_606,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k2_pre_topc(sK2,X0_41),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_353])).

cnf(c_656,plain,
    ( m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_606])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK4)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f43])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1596,c_1107,c_883,c_868,c_863,c_858,c_837,c_744,c_712,c_709,c_656,c_12,c_13,c_14,c_15])).


%------------------------------------------------------------------------------
