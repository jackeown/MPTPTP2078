%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1388+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:37 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 460 expanded)
%              Number of clauses        :   89 ( 124 expanded)
%              Number of leaves         :   18 ( 116 expanded)
%              Depth                    :   15
%              Number of atoms          :  760 (2896 expanded)
%              Number of equality atoms :  107 ( 196 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( X2 = X3
                   => ( v2_connsp_1(X2,X0)
                    <=> v2_connsp_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v2_connsp_1(X2,X0)
                  <=> v2_connsp_1(X3,X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v2_connsp_1(X2,X0)
                  <=> v2_connsp_1(X3,X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v2_connsp_1(X2,X0)
                      | ~ v2_connsp_1(X3,X1) )
                    & ( v2_connsp_1(X3,X1)
                      | ~ v2_connsp_1(X2,X0) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_connsp_1(X2,X0)
      | ~ v2_connsp_1(X3,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( v2_connsp_1(X3,X0)
      | ~ v2_connsp_1(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_connsp_1(X1,X0) )
               => r3_connsp_1(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_tarski(X1,X2)
                    & v3_connsp_1(X1,X0) )
                 => r3_connsp_1(X0,X2,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_tarski(X1,X2)
                    & v3_connsp_1(X1,X0) )
                 => r3_connsp_1(X0,X2,X1) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_connsp_1(X0,X2,X1)
              & r1_tarski(X1,X2)
              & v3_connsp_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_connsp_1(X0,X2,X1)
              & r1_tarski(X1,X2)
              & v3_connsp_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r3_connsp_1(X0,X2,X1)
          & r1_tarski(X1,X2)
          & v3_connsp_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r3_connsp_1(X0,sK4,X1)
        & r1_tarski(X1,sK4)
        & v3_connsp_1(X1,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_connsp_1(X0,X2,X1)
              & r1_tarski(X1,X2)
              & v3_connsp_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r3_connsp_1(X0,X2,sK3)
            & r1_tarski(sK3,X2)
            & v3_connsp_1(sK3,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r3_connsp_1(X0,X2,X1)
                & r1_tarski(X1,X2)
                & v3_connsp_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_connsp_1(sK2,X2,X1)
              & r1_tarski(X1,X2)
              & v3_connsp_1(X1,sK2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ~ r3_connsp_1(sK2,sK4,sK3)
    & r1_tarski(sK3,sK4)
    & v3_connsp_1(sK3,sK2)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f43,f42,f41])).

fof(f67,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_connsp_1(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_connsp_1(X2,X0) )
                   => X1 = X2 ) )
              & v2_connsp_1(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_connsp_1(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_connsp_1(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_connsp_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_connsp_1(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_connsp_1(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_connsp_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_connsp_1(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_connsp_1(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_connsp_1(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_connsp_1(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_connsp_1(X1,X0) )
              | ~ v3_connsp_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_connsp_1(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_connsp_1(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_connsp_1(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_connsp_1(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_connsp_1(X1,X0) )
              | ~ v3_connsp_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_connsp_1(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_connsp_1(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_connsp_1(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_connsp_1(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_connsp_1(X1,X0) )
              | ~ v3_connsp_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_connsp_1(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK0(X0,X1) != X1
        & r1_tarski(X1,sK0(X0,X1))
        & v2_connsp_1(sK0(X0,X1),X0)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_connsp_1(X1,X0)
              | ( sK0(X0,X1) != X1
                & r1_tarski(X1,sK0(X0,X1))
                & v2_connsp_1(sK0(X0,X1),X0)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_connsp_1(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_connsp_1(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_connsp_1(X1,X0) )
              | ~ v3_connsp_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( X1 = X3
      | ~ r1_tarski(X1,X3)
      | ~ v2_connsp_1(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_connsp_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v3_connsp_1(X1,X0)
      | v2_connsp_1(sK0(X0,X1),X0)
      | ~ v2_connsp_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v3_connsp_1(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_connsp_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v3_connsp_1(X1,X0)
      | sK0(X0,X1) != X1
      | ~ v2_connsp_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v3_connsp_1(X1,X0)
      | r1_tarski(X1,sK0(X0,X1))
      | ~ v2_connsp_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_connsp_1(X3,X1)
      | ~ v2_connsp_1(X2,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( v2_connsp_1(X3,X1)
      | ~ v2_connsp_1(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v2_connsp_1(X1,X0)
      | ~ v3_connsp_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f71,plain,(
    v3_connsp_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r3_connsp_1(X0,X1,X2)
              <=> ? [X3] :
                    ( v3_connsp_1(X3,k1_pre_topc(X0,X1))
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_connsp_1(X0,X1,X2)
              <=> ? [X3] :
                    ( v3_connsp_1(X3,k1_pre_topc(X0,X1))
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_connsp_1(X0,X1,X2)
                  | ! [X3] :
                      ( ~ v3_connsp_1(X3,k1_pre_topc(X0,X1))
                      | X2 != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                & ( ? [X3] :
                      ( v3_connsp_1(X3,k1_pre_topc(X0,X1))
                      & X2 = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
                  | ~ r3_connsp_1(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_connsp_1(X0,X1,X2)
                  | ! [X3] :
                      ( ~ v3_connsp_1(X3,k1_pre_topc(X0,X1))
                      | X2 != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                & ( ? [X4] :
                      ( v3_connsp_1(X4,k1_pre_topc(X0,X1))
                      & X2 = X4
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
                  | ~ r3_connsp_1(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( v3_connsp_1(X4,k1_pre_topc(X0,X1))
          & X2 = X4
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
     => ( v3_connsp_1(sK1(X0,X1,X2),k1_pre_topc(X0,X1))
        & sK1(X0,X1,X2) = X2
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_connsp_1(X0,X1,X2)
                  | ! [X3] :
                      ( ~ v3_connsp_1(X3,k1_pre_topc(X0,X1))
                      | X2 != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                & ( ( v3_connsp_1(sK1(X0,X1,X2),k1_pre_topc(X0,X1))
                    & sK1(X0,X1,X2) = X2
                    & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
                  | ~ r3_connsp_1(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r3_connsp_1(X0,X1,X2)
      | ~ v3_connsp_1(X3,k1_pre_topc(X0,X1))
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( r3_connsp_1(X0,X1,X3)
      | ~ v3_connsp_1(X3,k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f73,plain,(
    ~ r3_connsp_1(sK2,sK4,sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f72,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_17,plain,
    ( ~ v2_connsp_1(X0,X1)
    | v2_connsp_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_164,plain,
    ( v2_connsp_1(X0,X2)
    | ~ v2_connsp_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_19])).

cnf(c_165,plain,
    ( ~ v2_connsp_1(X0,X1)
    | v2_connsp_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(renaming,[status(thm)],[c_164])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_431,plain,
    ( ~ v2_connsp_1(X0,X1)
    | v2_connsp_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_165,c_28])).

cnf(c_432,plain,
    ( ~ v2_connsp_1(X0,X1)
    | v2_connsp_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_434,plain,
    ( ~ m1_pre_topc(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_connsp_1(X0,sK2)
    | ~ v2_connsp_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_432,c_27])).

cnf(c_435,plain,
    ( ~ v2_connsp_1(X0,X1)
    | v2_connsp_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,sK2) ),
    inference(renaming,[status(thm)],[c_434])).

cnf(c_3522,plain,
    ( ~ v2_connsp_1(X0,k1_pre_topc(sK2,sK4))
    | v2_connsp_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK4))))
    | ~ m1_pre_topc(k1_pre_topc(sK2,sK4),sK2) ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_14639,plain,
    ( ~ v2_connsp_1(sK0(k1_pre_topc(sK2,sK4),sK3),k1_pre_topc(sK2,sK4))
    | v2_connsp_1(sK0(k1_pre_topc(sK2,sK4),sK3),sK2)
    | ~ m1_subset_1(sK0(k1_pre_topc(sK2,sK4),sK3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK4))))
    | ~ m1_pre_topc(k1_pre_topc(sK2,sK4),sK2) ),
    inference(instantiation,[status(thm)],[c_3522])).

cnf(c_3517,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK4))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_pre_topc(k1_pre_topc(sK2,sK4),sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_14607,plain,
    ( ~ m1_subset_1(sK0(k1_pre_topc(sK2,sK4),sK3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK4))))
    | m1_subset_1(sK0(k1_pre_topc(sK2,sK4),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_pre_topc(k1_pre_topc(sK2,sK4),sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3517])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v2_connsp_1(X1,X2)
    | ~ v3_connsp_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3579,plain,
    ( ~ r1_tarski(sK3,X0)
    | ~ v2_connsp_1(X0,X1)
    | ~ v3_connsp_1(sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_14544,plain,
    ( ~ r1_tarski(sK3,sK0(k1_pre_topc(sK2,sK4),sK3))
    | ~ v2_connsp_1(sK0(k1_pre_topc(sK2,sK4),sK3),X0)
    | ~ v3_connsp_1(sK3,X0)
    | ~ m1_subset_1(sK0(k1_pre_topc(sK2,sK4),sK3),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0(k1_pre_topc(sK2,sK4),sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_3579])).

cnf(c_14546,plain,
    ( ~ r1_tarski(sK3,sK0(k1_pre_topc(sK2,sK4),sK3))
    | ~ v2_connsp_1(sK0(k1_pre_topc(sK2,sK4),sK3),sK2)
    | ~ v3_connsp_1(sK3,sK2)
    | ~ m1_subset_1(sK0(k1_pre_topc(sK2,sK4),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | sK0(k1_pre_topc(sK2,sK4),sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_14544])).

cnf(c_2417,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4195,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK3,k2_struct_0(k1_pre_topc(sK2,sK4)))
    | X1 != k2_struct_0(k1_pre_topc(sK2,sK4))
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2417])).

cnf(c_5672,plain,
    ( r1_tarski(sK3,X0)
    | ~ r1_tarski(sK3,k2_struct_0(k1_pre_topc(sK2,sK4)))
    | X0 != k2_struct_0(k1_pre_topc(sK2,sK4))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_4195])).

cnf(c_9371,plain,
    ( r1_tarski(sK3,u1_struct_0(k1_pre_topc(sK2,sK4)))
    | ~ r1_tarski(sK3,k2_struct_0(k1_pre_topc(sK2,sK4)))
    | u1_struct_0(k1_pre_topc(sK2,sK4)) != k2_struct_0(k1_pre_topc(sK2,sK4))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_5672])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_6039,plain,
    ( ~ r1_tarski(sK3,u1_struct_0(X0))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_7808,plain,
    ( ~ r1_tarski(sK3,u1_struct_0(k1_pre_topc(sK2,sK4)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK4)))) ),
    inference(instantiation,[status(thm)],[c_6039])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3089,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_pre_topc(k1_pre_topc(X1,X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3098,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_pre_topc(k1_pre_topc(X1,X0),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4245,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK4),sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3089,c_3098])).

cnf(c_30,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_32,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3376,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_pre_topc(k1_pre_topc(sK2,sK4),sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3377,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK4),sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3376])).

cnf(c_4660,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK4),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4245,c_30,c_32,c_3377])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3096,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4665,plain,
    ( l1_pre_topc(k1_pre_topc(sK2,sK4)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4660,c_3096])).

cnf(c_5739,plain,
    ( l1_pre_topc(k1_pre_topc(sK2,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4665,c_30])).

cnf(c_15,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_387,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_15,c_2])).

cnf(c_3085,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_387])).

cnf(c_5744,plain,
    ( u1_struct_0(k1_pre_topc(sK2,sK4)) = k2_struct_0(k1_pre_topc(sK2,sK4)) ),
    inference(superposition,[status(thm)],[c_5739,c_3085])).

cnf(c_5,plain,
    ( ~ v2_connsp_1(X0,X1)
    | v2_connsp_1(sK0(X1,X0),X1)
    | v3_connsp_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3802,plain,
    ( v2_connsp_1(sK0(X0,sK3),X0)
    | ~ v2_connsp_1(sK3,X0)
    | v3_connsp_1(sK3,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4866,plain,
    ( v2_connsp_1(sK0(k1_pre_topc(sK2,sK4),sK3),k1_pre_topc(sK2,sK4))
    | ~ v2_connsp_1(sK3,k1_pre_topc(sK2,sK4))
    | v3_connsp_1(sK3,k1_pre_topc(sK2,sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK4))))
    | ~ l1_pre_topc(k1_pre_topc(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_3802])).

cnf(c_6,plain,
    ( ~ v2_connsp_1(X0,X1)
    | v3_connsp_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_3801,plain,
    ( ~ v2_connsp_1(sK3,X0)
    | v3_connsp_1(sK3,X0)
    | m1_subset_1(sK0(X0,sK3),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4855,plain,
    ( ~ v2_connsp_1(sK3,k1_pre_topc(sK2,sK4))
    | v3_connsp_1(sK3,k1_pre_topc(sK2,sK4))
    | m1_subset_1(sK0(k1_pre_topc(sK2,sK4),sK3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK4))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK4))))
    | ~ l1_pre_topc(k1_pre_topc(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_3801])).

cnf(c_3,plain,
    ( ~ v2_connsp_1(X0,X1)
    | v3_connsp_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3804,plain,
    ( ~ v2_connsp_1(sK3,X0)
    | v3_connsp_1(sK3,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0(X0,sK3) != sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4759,plain,
    ( ~ v2_connsp_1(sK3,k1_pre_topc(sK2,sK4))
    | v3_connsp_1(sK3,k1_pre_topc(sK2,sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK4))))
    | ~ l1_pre_topc(k1_pre_topc(sK2,sK4))
    | sK0(k1_pre_topc(sK2,sK4),sK3) != sK3 ),
    inference(instantiation,[status(thm)],[c_3804])).

cnf(c_4,plain,
    ( r1_tarski(X0,sK0(X1,X0))
    | ~ v2_connsp_1(X0,X1)
    | v3_connsp_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3803,plain,
    ( r1_tarski(sK3,sK0(X0,sK3))
    | ~ v2_connsp_1(sK3,X0)
    | v3_connsp_1(sK3,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4748,plain,
    ( r1_tarski(sK3,sK0(k1_pre_topc(sK2,sK4),sK3))
    | ~ v2_connsp_1(sK3,k1_pre_topc(sK2,sK4))
    | v3_connsp_1(sK3,k1_pre_topc(sK2,sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK4))))
    | ~ l1_pre_topc(k1_pre_topc(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_3803])).

cnf(c_4666,plain,
    ( l1_pre_topc(k1_pre_topc(sK2,sK4))
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4665])).

cnf(c_3410,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK3,sK4)
    | X0 != sK3
    | X1 != sK4 ),
    inference(instantiation,[status(thm)],[c_2417])).

cnf(c_3694,plain,
    ( r1_tarski(sK3,X0)
    | ~ r1_tarski(sK3,sK4)
    | X0 != sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3410])).

cnf(c_4048,plain,
    ( r1_tarski(sK3,k2_struct_0(k1_pre_topc(sK2,sK4)))
    | ~ r1_tarski(sK3,sK4)
    | k2_struct_0(k1_pre_topc(sK2,sK4)) != sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3694])).

cnf(c_18,plain,
    ( ~ v2_connsp_1(X0,X1)
    | v2_connsp_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_451,plain,
    ( ~ v2_connsp_1(X0,X1)
    | v2_connsp_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_28])).

cnf(c_452,plain,
    ( v2_connsp_1(X0,X1)
    | ~ v2_connsp_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_pre_topc(X1,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_454,plain,
    ( ~ m1_pre_topc(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_connsp_1(X0,sK2)
    | v2_connsp_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_452,c_27])).

cnf(c_455,plain,
    ( v2_connsp_1(X0,X1)
    | ~ v2_connsp_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_pre_topc(X1,sK2) ),
    inference(renaming,[status(thm)],[c_454])).

cnf(c_3568,plain,
    ( v2_connsp_1(sK3,X0)
    | ~ v2_connsp_1(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_pre_topc(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_455])).

cnf(c_3816,plain,
    ( v2_connsp_1(sK3,k1_pre_topc(sK2,sK4))
    | ~ v2_connsp_1(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK4))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_pre_topc(k1_pre_topc(sK2,sK4),sK2) ),
    inference(instantiation,[status(thm)],[c_3568])).

cnf(c_2405,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3583,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_2405])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(k1_pre_topc(X1,X0),X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(k1_pre_topc(X1,X0))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_184,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1,c_14,c_13])).

cnf(c_185,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_184])).

cnf(c_3382,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | k2_struct_0(k1_pre_topc(sK2,sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_185])).

cnf(c_8,plain,
    ( v2_connsp_1(X0,X1)
    | ~ v3_connsp_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_24,negated_conjecture,
    ( v3_connsp_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1120,plain,
    ( v2_connsp_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_1121,plain,
    ( v2_connsp_1(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1120])).

cnf(c_524,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | X4 != X1
    | k1_pre_topc(X1,X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_525,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_524])).

cnf(c_9,plain,
    ( r3_connsp_1(X0,X1,X2)
    | ~ v3_connsp_1(X2,k1_pre_topc(X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_600,plain,
    ( r3_connsp_1(X0,X1,X2)
    | ~ v3_connsp_1(X2,k1_pre_topc(X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
    | ~ l1_pre_topc(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_525,c_9])).

cnf(c_22,negated_conjecture,
    ( ~ r3_connsp_1(sK2,sK4,sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_682,plain,
    ( ~ v3_connsp_1(X0,k1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))
    | ~ l1_pre_topc(X1)
    | sK3 != X0
    | sK4 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_600,c_22])).

cnf(c_683,plain,
    ( ~ v3_connsp_1(sK3,k1_pre_topc(sK2,sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK4))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_682])).

cnf(c_685,plain,
    ( ~ v3_connsp_1(sK3,k1_pre_topc(sK2,sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK4)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_683,c_27,c_25])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f69])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14639,c_14607,c_14546,c_9371,c_7808,c_5744,c_4866,c_4855,c_4759,c_4748,c_4666,c_4048,c_3816,c_3583,c_3382,c_3376,c_1121,c_685,c_23,c_24,c_25,c_26,c_27])).


%------------------------------------------------------------------------------
