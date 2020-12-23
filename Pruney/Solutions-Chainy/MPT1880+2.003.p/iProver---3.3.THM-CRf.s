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
% DateTime   : Thu Dec  3 12:27:07 EST 2020

% Result     : Theorem 11.52s
% Output     : CNFRefutation 11.52s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 980 expanded)
%              Number of clauses        :   90 ( 243 expanded)
%              Number of leaves         :   12 ( 248 expanded)
%              Depth                    :   22
%              Number of atoms          :  619 (6380 expanded)
%              Number of equality atoms :  186 ( 564 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v2_tex_2(X1,X0)
                & v1_tops_1(X1,X0) )
             => v3_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tex_2(X1,X0)
          & v2_tex_2(X1,X0)
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tex_2(X1,X0)
          & v2_tex_2(X1,X0)
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_tex_2(X1,X0)
          & v2_tex_2(X1,X0)
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_tex_2(sK3,X0)
        & v2_tex_2(sK3,X0)
        & v1_tops_1(sK3,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v3_tex_2(X1,X0)
            & v2_tex_2(X1,X0)
            & v1_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v3_tex_2(X1,sK2)
          & v2_tex_2(X1,sK2)
          & v1_tops_1(X1,sK2)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ~ v3_tex_2(sK3,sK2)
    & v2_tex_2(sK3,sK2)
    & v1_tops_1(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f35,f34])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK0(X0,X1) != X1
        & r1_tarski(X1,sK0(X0,X1))
        & v2_tex_2(sK0(X0,X1),X0)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK0(X0,X1) != X1
                & r1_tarski(X1,sK0(X0,X1))
                & v2_tex_2(sK0(X0,X1),X0)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,(
    v1_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,(
    ~ v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | r1_tarski(X1,sK0(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK1(X0,X1))) != sK1(X0,X1)
        & r1_tarski(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK1(X0,X1))) != sK1(X0,X1)
                & r1_tarski(sK1(X0,X1),X1)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | v2_tex_2(sK0(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | sK0(X0,X1) != X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1619,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_12,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_487,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_23])).

cnf(c_488,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_487])).

cnf(c_1612,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_488])).

cnf(c_8,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_21,negated_conjecture,
    ( v1_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_331,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1)
    | sK2 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_332,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | k2_pre_topc(sK2,sK3) = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_334,plain,
    ( k2_pre_topc(sK2,sK3) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_332,c_23,c_22])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_559,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_23])).

cnf(c_560,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k2_pre_topc(sK2,X0),k2_pre_topc(sK2,X1)) ),
    inference(unflattening,[status(thm)],[c_559])).

cnf(c_1608,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_pre_topc(sK2,X0),k2_pre_topc(sK2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_560])).

cnf(c_2082,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(u1_struct_0(sK2),k2_pre_topc(sK2,X0)) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_334,c_1608])).

cnf(c_29,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2377,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(u1_struct_0(sK2),k2_pre_topc(sK2,X0)) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2082,c_29])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1625,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2387,plain,
    ( k2_pre_topc(sK2,X0) = u1_struct_0(sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k2_pre_topc(sK2,X0),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2377,c_1625])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_577,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_23])).

cnf(c_578,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_577])).

cnf(c_1607,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_578])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1622,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2176,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k2_pre_topc(sK2,X0),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1607,c_1622])).

cnf(c_4511,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k2_pre_topc(sK2,X0) = u1_struct_0(sK2)
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2387,c_2176])).

cnf(c_4512,plain,
    ( k2_pre_topc(sK2,X0) = u1_struct_0(sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4511])).

cnf(c_4523,plain,
    ( k2_pre_topc(sK2,sK0(sK2,X0)) = u1_struct_0(sK2)
    | v2_tex_2(X0,sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK3,sK0(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1612,c_4512])).

cnf(c_43593,plain,
    ( k2_pre_topc(sK2,sK0(sK2,sK3)) = u1_struct_0(sK2)
    | v2_tex_2(sK3,sK2) != iProver_top
    | v3_tex_2(sK3,sK2) = iProver_top
    | r1_tarski(sK3,sK0(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1619,c_4523])).

cnf(c_20,negated_conjecture,
    ( v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_31,plain,
    ( v2_tex_2(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( ~ v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_32,plain,
    ( v3_tex_2(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_10,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,sK0(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_523,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,sK0(X1,X0))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_23])).

cnf(c_524,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(X0,sK0(sK2,X0)) ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_640,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(X0,sK0(sK2,X0))
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_524])).

cnf(c_641,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK3,sK0(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_640])).

cnf(c_642,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK3,sK0(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_641])).

cnf(c_43944,plain,
    ( k2_pre_topc(sK2,sK0(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_43593,c_29,c_31,c_32,c_642])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1624,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1623,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_18,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_340,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_341,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_345,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_341,c_25,c_23])).

cnf(c_1618,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1
    | v2_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_345])).

cnf(c_3573,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,X0),k2_pre_topc(sK2,X1)) = X1
    | v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(sK0(sK2,X0),sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,sK0(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1612,c_1618])).

cnf(c_11,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK0(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_505,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK0(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_506,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v2_tex_2(sK0(sK2,X0),sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_507,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(sK0(sK2,X0),sK2) = iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_506])).

cnf(c_29708,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | k9_subset_1(u1_struct_0(sK2),sK0(sK2,X0),k2_pre_topc(sK2,X1)) = X1
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,sK0(sK2,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3573,c_507])).

cnf(c_29709,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,X0),k2_pre_topc(sK2,X1)) = X1
    | v2_tex_2(X0,sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,sK0(sK2,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_29708])).

cnf(c_29721,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,X0)) = X0
    | v2_tex_2(sK3,sK2) != iProver_top
    | v3_tex_2(sK3,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK0(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1619,c_29709])).

cnf(c_29806,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK0(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29721,c_31,c_32])).

cnf(c_29815,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,X0)) = X0
    | r1_tarski(X0,sK0(sK2,sK3)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1623,c_29806])).

cnf(c_29981,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,sK0(sK2,sK3))) = sK0(sK2,sK3)
    | r1_tarski(sK0(sK2,sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1624,c_29815])).

cnf(c_651,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v2_tex_2(sK0(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_506])).

cnf(c_652,plain,
    ( v2_tex_2(sK0(sK2,sK3),sK2)
    | ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_651])).

cnf(c_662,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_488])).

cnf(c_663,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_662])).

cnf(c_1885,plain,
    ( ~ v2_tex_2(sK0(sK2,sK3),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,sK0(sK2,sK3))
    | k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,X0)) = X0 ),
    inference(instantiation,[status(thm)],[c_345])).

cnf(c_2266,plain,
    ( ~ v2_tex_2(sK0(sK2,sK3),sK2)
    | ~ m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(sK0(sK2,sK3),sK0(sK2,sK3))
    | k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,sK0(sK2,sK3))) = sK0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1885])).

cnf(c_2672,plain,
    ( r1_tarski(sK0(sK2,sK3),sK0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_30007,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,sK0(sK2,sK3))) = sK0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29981,c_22,c_20,c_652,c_663,c_2266,c_2672])).

cnf(c_43947,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),u1_struct_0(sK2)) = sK0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_43944,c_30007])).

cnf(c_1610,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK0(sK2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_524])).

cnf(c_2812,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | v3_tex_2(sK3,sK2) = iProver_top
    | r1_tarski(sK3,sK0(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1619,c_1610])).

cnf(c_3091,plain,
    ( r1_tarski(sK3,sK0(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2812,c_29,c_31,c_642])).

cnf(c_29984,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,sK3)) = sK3
    | r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3091,c_29815])).

cnf(c_29987,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),u1_struct_0(sK2)) = sK3
    | r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_29984,c_334])).

cnf(c_29816,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,sK3)) = sK3
    | r1_tarski(sK3,sK0(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1619,c_29806])).

cnf(c_29852,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),u1_struct_0(sK2)) = sK3
    | r1_tarski(sK3,sK0(sK2,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_29816,c_334])).

cnf(c_30583,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),u1_struct_0(sK2)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_29987,c_29,c_31,c_642,c_29852])).

cnf(c_43948,plain,
    ( sK0(sK2,sK3) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_43947,c_30583])).

cnf(c_9,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_541,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK0(X1,X0) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_23])).

cnf(c_542,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK0(sK2,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_541])).

cnf(c_632,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK0(sK2,X0) != X0
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_542])).

cnf(c_633,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK0(sK2,sK3) != sK3 ),
    inference(unflattening,[status(thm)],[c_632])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_43948,c_633,c_20,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:20:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.52/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.52/2.00  
% 11.52/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.52/2.00  
% 11.52/2.00  ------  iProver source info
% 11.52/2.00  
% 11.52/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.52/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.52/2.00  git: non_committed_changes: false
% 11.52/2.00  git: last_make_outside_of_git: false
% 11.52/2.00  
% 11.52/2.00  ------ 
% 11.52/2.00  
% 11.52/2.00  ------ Input Options
% 11.52/2.00  
% 11.52/2.00  --out_options                           all
% 11.52/2.00  --tptp_safe_out                         true
% 11.52/2.00  --problem_path                          ""
% 11.52/2.00  --include_path                          ""
% 11.52/2.00  --clausifier                            res/vclausify_rel
% 11.52/2.00  --clausifier_options                    --mode clausify
% 11.52/2.00  --stdin                                 false
% 11.52/2.00  --stats_out                             all
% 11.52/2.00  
% 11.52/2.00  ------ General Options
% 11.52/2.00  
% 11.52/2.00  --fof                                   false
% 11.52/2.00  --time_out_real                         305.
% 11.52/2.00  --time_out_virtual                      -1.
% 11.52/2.00  --symbol_type_check                     false
% 11.52/2.00  --clausify_out                          false
% 11.52/2.00  --sig_cnt_out                           false
% 11.52/2.00  --trig_cnt_out                          false
% 11.52/2.00  --trig_cnt_out_tolerance                1.
% 11.52/2.00  --trig_cnt_out_sk_spl                   false
% 11.52/2.00  --abstr_cl_out                          false
% 11.52/2.00  
% 11.52/2.00  ------ Global Options
% 11.52/2.00  
% 11.52/2.00  --schedule                              default
% 11.52/2.00  --add_important_lit                     false
% 11.52/2.00  --prop_solver_per_cl                    1000
% 11.52/2.00  --min_unsat_core                        false
% 11.52/2.00  --soft_assumptions                      false
% 11.52/2.00  --soft_lemma_size                       3
% 11.52/2.00  --prop_impl_unit_size                   0
% 11.52/2.00  --prop_impl_unit                        []
% 11.52/2.00  --share_sel_clauses                     true
% 11.52/2.00  --reset_solvers                         false
% 11.52/2.00  --bc_imp_inh                            [conj_cone]
% 11.52/2.00  --conj_cone_tolerance                   3.
% 11.52/2.00  --extra_neg_conj                        none
% 11.52/2.00  --large_theory_mode                     true
% 11.52/2.00  --prolific_symb_bound                   200
% 11.52/2.00  --lt_threshold                          2000
% 11.52/2.00  --clause_weak_htbl                      true
% 11.52/2.00  --gc_record_bc_elim                     false
% 11.52/2.00  
% 11.52/2.00  ------ Preprocessing Options
% 11.52/2.00  
% 11.52/2.00  --preprocessing_flag                    true
% 11.52/2.00  --time_out_prep_mult                    0.1
% 11.52/2.00  --splitting_mode                        input
% 11.52/2.00  --splitting_grd                         true
% 11.52/2.00  --splitting_cvd                         false
% 11.52/2.00  --splitting_cvd_svl                     false
% 11.52/2.00  --splitting_nvd                         32
% 11.52/2.00  --sub_typing                            true
% 11.52/2.00  --prep_gs_sim                           true
% 11.52/2.00  --prep_unflatten                        true
% 11.52/2.00  --prep_res_sim                          true
% 11.52/2.00  --prep_upred                            true
% 11.52/2.00  --prep_sem_filter                       exhaustive
% 11.52/2.00  --prep_sem_filter_out                   false
% 11.52/2.00  --pred_elim                             true
% 11.52/2.00  --res_sim_input                         true
% 11.52/2.00  --eq_ax_congr_red                       true
% 11.52/2.00  --pure_diseq_elim                       true
% 11.52/2.00  --brand_transform                       false
% 11.52/2.00  --non_eq_to_eq                          false
% 11.52/2.00  --prep_def_merge                        true
% 11.52/2.00  --prep_def_merge_prop_impl              false
% 11.52/2.00  --prep_def_merge_mbd                    true
% 11.52/2.00  --prep_def_merge_tr_red                 false
% 11.52/2.00  --prep_def_merge_tr_cl                  false
% 11.52/2.00  --smt_preprocessing                     true
% 11.52/2.00  --smt_ac_axioms                         fast
% 11.52/2.00  --preprocessed_out                      false
% 11.52/2.00  --preprocessed_stats                    false
% 11.52/2.00  
% 11.52/2.00  ------ Abstraction refinement Options
% 11.52/2.00  
% 11.52/2.00  --abstr_ref                             []
% 11.52/2.00  --abstr_ref_prep                        false
% 11.52/2.00  --abstr_ref_until_sat                   false
% 11.52/2.00  --abstr_ref_sig_restrict                funpre
% 11.52/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.52/2.00  --abstr_ref_under                       []
% 11.52/2.00  
% 11.52/2.00  ------ SAT Options
% 11.52/2.00  
% 11.52/2.00  --sat_mode                              false
% 11.52/2.00  --sat_fm_restart_options                ""
% 11.52/2.00  --sat_gr_def                            false
% 11.52/2.00  --sat_epr_types                         true
% 11.52/2.00  --sat_non_cyclic_types                  false
% 11.52/2.00  --sat_finite_models                     false
% 11.52/2.00  --sat_fm_lemmas                         false
% 11.52/2.00  --sat_fm_prep                           false
% 11.52/2.00  --sat_fm_uc_incr                        true
% 11.52/2.00  --sat_out_model                         small
% 11.52/2.00  --sat_out_clauses                       false
% 11.52/2.00  
% 11.52/2.00  ------ QBF Options
% 11.52/2.00  
% 11.52/2.00  --qbf_mode                              false
% 11.52/2.00  --qbf_elim_univ                         false
% 11.52/2.00  --qbf_dom_inst                          none
% 11.52/2.00  --qbf_dom_pre_inst                      false
% 11.52/2.00  --qbf_sk_in                             false
% 11.52/2.00  --qbf_pred_elim                         true
% 11.52/2.00  --qbf_split                             512
% 11.52/2.00  
% 11.52/2.00  ------ BMC1 Options
% 11.52/2.00  
% 11.52/2.00  --bmc1_incremental                      false
% 11.52/2.00  --bmc1_axioms                           reachable_all
% 11.52/2.00  --bmc1_min_bound                        0
% 11.52/2.00  --bmc1_max_bound                        -1
% 11.52/2.00  --bmc1_max_bound_default                -1
% 11.52/2.00  --bmc1_symbol_reachability              true
% 11.52/2.00  --bmc1_property_lemmas                  false
% 11.52/2.00  --bmc1_k_induction                      false
% 11.52/2.00  --bmc1_non_equiv_states                 false
% 11.52/2.00  --bmc1_deadlock                         false
% 11.52/2.00  --bmc1_ucm                              false
% 11.52/2.00  --bmc1_add_unsat_core                   none
% 11.52/2.00  --bmc1_unsat_core_children              false
% 11.52/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.52/2.00  --bmc1_out_stat                         full
% 11.52/2.00  --bmc1_ground_init                      false
% 11.52/2.00  --bmc1_pre_inst_next_state              false
% 11.52/2.00  --bmc1_pre_inst_state                   false
% 11.52/2.00  --bmc1_pre_inst_reach_state             false
% 11.52/2.00  --bmc1_out_unsat_core                   false
% 11.52/2.00  --bmc1_aig_witness_out                  false
% 11.52/2.00  --bmc1_verbose                          false
% 11.52/2.00  --bmc1_dump_clauses_tptp                false
% 11.52/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.52/2.00  --bmc1_dump_file                        -
% 11.52/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.52/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.52/2.00  --bmc1_ucm_extend_mode                  1
% 11.52/2.00  --bmc1_ucm_init_mode                    2
% 11.52/2.00  --bmc1_ucm_cone_mode                    none
% 11.52/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.52/2.00  --bmc1_ucm_relax_model                  4
% 11.52/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.52/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.52/2.00  --bmc1_ucm_layered_model                none
% 11.52/2.00  --bmc1_ucm_max_lemma_size               10
% 11.52/2.00  
% 11.52/2.00  ------ AIG Options
% 11.52/2.00  
% 11.52/2.00  --aig_mode                              false
% 11.52/2.00  
% 11.52/2.00  ------ Instantiation Options
% 11.52/2.00  
% 11.52/2.00  --instantiation_flag                    true
% 11.52/2.00  --inst_sos_flag                         false
% 11.52/2.00  --inst_sos_phase                        true
% 11.52/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.52/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.52/2.00  --inst_lit_sel_side                     num_symb
% 11.52/2.00  --inst_solver_per_active                1400
% 11.52/2.00  --inst_solver_calls_frac                1.
% 11.52/2.00  --inst_passive_queue_type               priority_queues
% 11.52/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.52/2.00  --inst_passive_queues_freq              [25;2]
% 11.52/2.00  --inst_dismatching                      true
% 11.52/2.00  --inst_eager_unprocessed_to_passive     true
% 11.52/2.00  --inst_prop_sim_given                   true
% 11.52/2.00  --inst_prop_sim_new                     false
% 11.52/2.00  --inst_subs_new                         false
% 11.52/2.00  --inst_eq_res_simp                      false
% 11.52/2.00  --inst_subs_given                       false
% 11.52/2.00  --inst_orphan_elimination               true
% 11.52/2.00  --inst_learning_loop_flag               true
% 11.52/2.00  --inst_learning_start                   3000
% 11.52/2.00  --inst_learning_factor                  2
% 11.52/2.00  --inst_start_prop_sim_after_learn       3
% 11.52/2.00  --inst_sel_renew                        solver
% 11.52/2.00  --inst_lit_activity_flag                true
% 11.52/2.00  --inst_restr_to_given                   false
% 11.52/2.00  --inst_activity_threshold               500
% 11.52/2.00  --inst_out_proof                        true
% 11.52/2.00  
% 11.52/2.00  ------ Resolution Options
% 11.52/2.00  
% 11.52/2.00  --resolution_flag                       true
% 11.52/2.00  --res_lit_sel                           adaptive
% 11.52/2.00  --res_lit_sel_side                      none
% 11.52/2.00  --res_ordering                          kbo
% 11.52/2.00  --res_to_prop_solver                    active
% 11.52/2.00  --res_prop_simpl_new                    false
% 11.52/2.00  --res_prop_simpl_given                  true
% 11.52/2.00  --res_passive_queue_type                priority_queues
% 11.52/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.52/2.00  --res_passive_queues_freq               [15;5]
% 11.52/2.00  --res_forward_subs                      full
% 11.52/2.00  --res_backward_subs                     full
% 11.52/2.00  --res_forward_subs_resolution           true
% 11.52/2.00  --res_backward_subs_resolution          true
% 11.52/2.00  --res_orphan_elimination                true
% 11.52/2.00  --res_time_limit                        2.
% 11.52/2.00  --res_out_proof                         true
% 11.52/2.00  
% 11.52/2.00  ------ Superposition Options
% 11.52/2.00  
% 11.52/2.00  --superposition_flag                    true
% 11.52/2.00  --sup_passive_queue_type                priority_queues
% 11.52/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.52/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.52/2.00  --demod_completeness_check              fast
% 11.52/2.00  --demod_use_ground                      true
% 11.52/2.00  --sup_to_prop_solver                    passive
% 11.52/2.00  --sup_prop_simpl_new                    true
% 11.52/2.00  --sup_prop_simpl_given                  true
% 11.52/2.00  --sup_fun_splitting                     false
% 11.52/2.00  --sup_smt_interval                      50000
% 11.52/2.00  
% 11.52/2.00  ------ Superposition Simplification Setup
% 11.52/2.00  
% 11.52/2.00  --sup_indices_passive                   []
% 11.52/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.52/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.52/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.52/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.52/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.52/2.00  --sup_full_bw                           [BwDemod]
% 11.52/2.00  --sup_immed_triv                        [TrivRules]
% 11.52/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.52/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.52/2.00  --sup_immed_bw_main                     []
% 11.52/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.52/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.52/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.52/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.52/2.00  
% 11.52/2.00  ------ Combination Options
% 11.52/2.00  
% 11.52/2.00  --comb_res_mult                         3
% 11.52/2.00  --comb_sup_mult                         2
% 11.52/2.00  --comb_inst_mult                        10
% 11.52/2.00  
% 11.52/2.00  ------ Debug Options
% 11.52/2.00  
% 11.52/2.00  --dbg_backtrace                         false
% 11.52/2.00  --dbg_dump_prop_clauses                 false
% 11.52/2.00  --dbg_dump_prop_clauses_file            -
% 11.52/2.00  --dbg_out_stat                          false
% 11.52/2.00  ------ Parsing...
% 11.52/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.52/2.00  
% 11.52/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 11.52/2.00  
% 11.52/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.52/2.00  
% 11.52/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.52/2.00  ------ Proving...
% 11.52/2.00  ------ Problem Properties 
% 11.52/2.00  
% 11.52/2.00  
% 11.52/2.00  clauses                                 20
% 11.52/2.00  conjectures                             3
% 11.52/2.00  EPR                                     4
% 11.52/2.00  Horn                                    15
% 11.52/2.00  unary                                   5
% 11.52/2.00  binary                                  3
% 11.52/2.00  lits                                    57
% 11.52/2.00  lits eq                                 6
% 11.52/2.00  fd_pure                                 0
% 11.52/2.00  fd_pseudo                               0
% 11.52/2.00  fd_cond                                 0
% 11.52/2.00  fd_pseudo_cond                          2
% 11.52/2.00  AC symbols                              0
% 11.52/2.00  
% 11.52/2.00  ------ Schedule dynamic 5 is on 
% 11.52/2.00  
% 11.52/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.52/2.00  
% 11.52/2.00  
% 11.52/2.00  ------ 
% 11.52/2.00  Current options:
% 11.52/2.00  ------ 
% 11.52/2.00  
% 11.52/2.00  ------ Input Options
% 11.52/2.00  
% 11.52/2.00  --out_options                           all
% 11.52/2.00  --tptp_safe_out                         true
% 11.52/2.00  --problem_path                          ""
% 11.52/2.00  --include_path                          ""
% 11.52/2.00  --clausifier                            res/vclausify_rel
% 11.52/2.00  --clausifier_options                    --mode clausify
% 11.52/2.00  --stdin                                 false
% 11.52/2.00  --stats_out                             all
% 11.52/2.00  
% 11.52/2.00  ------ General Options
% 11.52/2.00  
% 11.52/2.00  --fof                                   false
% 11.52/2.00  --time_out_real                         305.
% 11.52/2.00  --time_out_virtual                      -1.
% 11.52/2.00  --symbol_type_check                     false
% 11.52/2.00  --clausify_out                          false
% 11.52/2.00  --sig_cnt_out                           false
% 11.52/2.00  --trig_cnt_out                          false
% 11.52/2.00  --trig_cnt_out_tolerance                1.
% 11.52/2.00  --trig_cnt_out_sk_spl                   false
% 11.52/2.00  --abstr_cl_out                          false
% 11.52/2.00  
% 11.52/2.00  ------ Global Options
% 11.52/2.00  
% 11.52/2.00  --schedule                              default
% 11.52/2.00  --add_important_lit                     false
% 11.52/2.00  --prop_solver_per_cl                    1000
% 11.52/2.00  --min_unsat_core                        false
% 11.52/2.00  --soft_assumptions                      false
% 11.52/2.00  --soft_lemma_size                       3
% 11.52/2.00  --prop_impl_unit_size                   0
% 11.52/2.00  --prop_impl_unit                        []
% 11.52/2.00  --share_sel_clauses                     true
% 11.52/2.00  --reset_solvers                         false
% 11.52/2.00  --bc_imp_inh                            [conj_cone]
% 11.52/2.00  --conj_cone_tolerance                   3.
% 11.52/2.00  --extra_neg_conj                        none
% 11.52/2.00  --large_theory_mode                     true
% 11.52/2.00  --prolific_symb_bound                   200
% 11.52/2.00  --lt_threshold                          2000
% 11.52/2.00  --clause_weak_htbl                      true
% 11.52/2.00  --gc_record_bc_elim                     false
% 11.52/2.00  
% 11.52/2.00  ------ Preprocessing Options
% 11.52/2.00  
% 11.52/2.00  --preprocessing_flag                    true
% 11.52/2.00  --time_out_prep_mult                    0.1
% 11.52/2.00  --splitting_mode                        input
% 11.52/2.00  --splitting_grd                         true
% 11.52/2.00  --splitting_cvd                         false
% 11.52/2.00  --splitting_cvd_svl                     false
% 11.52/2.00  --splitting_nvd                         32
% 11.52/2.00  --sub_typing                            true
% 11.52/2.00  --prep_gs_sim                           true
% 11.52/2.00  --prep_unflatten                        true
% 11.52/2.00  --prep_res_sim                          true
% 11.52/2.00  --prep_upred                            true
% 11.52/2.00  --prep_sem_filter                       exhaustive
% 11.52/2.00  --prep_sem_filter_out                   false
% 11.52/2.00  --pred_elim                             true
% 11.52/2.00  --res_sim_input                         true
% 11.52/2.00  --eq_ax_congr_red                       true
% 11.52/2.00  --pure_diseq_elim                       true
% 11.52/2.00  --brand_transform                       false
% 11.52/2.00  --non_eq_to_eq                          false
% 11.52/2.00  --prep_def_merge                        true
% 11.52/2.00  --prep_def_merge_prop_impl              false
% 11.52/2.00  --prep_def_merge_mbd                    true
% 11.52/2.00  --prep_def_merge_tr_red                 false
% 11.52/2.00  --prep_def_merge_tr_cl                  false
% 11.52/2.00  --smt_preprocessing                     true
% 11.52/2.00  --smt_ac_axioms                         fast
% 11.52/2.00  --preprocessed_out                      false
% 11.52/2.00  --preprocessed_stats                    false
% 11.52/2.00  
% 11.52/2.00  ------ Abstraction refinement Options
% 11.52/2.00  
% 11.52/2.00  --abstr_ref                             []
% 11.52/2.00  --abstr_ref_prep                        false
% 11.52/2.00  --abstr_ref_until_sat                   false
% 11.52/2.00  --abstr_ref_sig_restrict                funpre
% 11.52/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.52/2.00  --abstr_ref_under                       []
% 11.52/2.00  
% 11.52/2.00  ------ SAT Options
% 11.52/2.00  
% 11.52/2.00  --sat_mode                              false
% 11.52/2.00  --sat_fm_restart_options                ""
% 11.52/2.00  --sat_gr_def                            false
% 11.52/2.00  --sat_epr_types                         true
% 11.52/2.00  --sat_non_cyclic_types                  false
% 11.52/2.00  --sat_finite_models                     false
% 11.52/2.00  --sat_fm_lemmas                         false
% 11.52/2.00  --sat_fm_prep                           false
% 11.52/2.00  --sat_fm_uc_incr                        true
% 11.52/2.00  --sat_out_model                         small
% 11.52/2.00  --sat_out_clauses                       false
% 11.52/2.00  
% 11.52/2.00  ------ QBF Options
% 11.52/2.00  
% 11.52/2.00  --qbf_mode                              false
% 11.52/2.00  --qbf_elim_univ                         false
% 11.52/2.00  --qbf_dom_inst                          none
% 11.52/2.00  --qbf_dom_pre_inst                      false
% 11.52/2.00  --qbf_sk_in                             false
% 11.52/2.00  --qbf_pred_elim                         true
% 11.52/2.00  --qbf_split                             512
% 11.52/2.00  
% 11.52/2.00  ------ BMC1 Options
% 11.52/2.00  
% 11.52/2.00  --bmc1_incremental                      false
% 11.52/2.00  --bmc1_axioms                           reachable_all
% 11.52/2.00  --bmc1_min_bound                        0
% 11.52/2.00  --bmc1_max_bound                        -1
% 11.52/2.00  --bmc1_max_bound_default                -1
% 11.52/2.00  --bmc1_symbol_reachability              true
% 11.52/2.00  --bmc1_property_lemmas                  false
% 11.52/2.00  --bmc1_k_induction                      false
% 11.52/2.00  --bmc1_non_equiv_states                 false
% 11.52/2.00  --bmc1_deadlock                         false
% 11.52/2.00  --bmc1_ucm                              false
% 11.52/2.00  --bmc1_add_unsat_core                   none
% 11.52/2.00  --bmc1_unsat_core_children              false
% 11.52/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.52/2.00  --bmc1_out_stat                         full
% 11.52/2.00  --bmc1_ground_init                      false
% 11.52/2.00  --bmc1_pre_inst_next_state              false
% 11.52/2.00  --bmc1_pre_inst_state                   false
% 11.52/2.00  --bmc1_pre_inst_reach_state             false
% 11.52/2.00  --bmc1_out_unsat_core                   false
% 11.52/2.00  --bmc1_aig_witness_out                  false
% 11.52/2.00  --bmc1_verbose                          false
% 11.52/2.00  --bmc1_dump_clauses_tptp                false
% 11.52/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.52/2.00  --bmc1_dump_file                        -
% 11.52/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.52/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.52/2.00  --bmc1_ucm_extend_mode                  1
% 11.52/2.00  --bmc1_ucm_init_mode                    2
% 11.52/2.00  --bmc1_ucm_cone_mode                    none
% 11.52/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.52/2.00  --bmc1_ucm_relax_model                  4
% 11.52/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.52/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.52/2.00  --bmc1_ucm_layered_model                none
% 11.52/2.00  --bmc1_ucm_max_lemma_size               10
% 11.52/2.00  
% 11.52/2.00  ------ AIG Options
% 11.52/2.00  
% 11.52/2.00  --aig_mode                              false
% 11.52/2.00  
% 11.52/2.00  ------ Instantiation Options
% 11.52/2.00  
% 11.52/2.00  --instantiation_flag                    true
% 11.52/2.00  --inst_sos_flag                         false
% 11.52/2.00  --inst_sos_phase                        true
% 11.52/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.52/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.52/2.00  --inst_lit_sel_side                     none
% 11.52/2.00  --inst_solver_per_active                1400
% 11.52/2.00  --inst_solver_calls_frac                1.
% 11.52/2.00  --inst_passive_queue_type               priority_queues
% 11.52/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.52/2.00  --inst_passive_queues_freq              [25;2]
% 11.52/2.00  --inst_dismatching                      true
% 11.52/2.00  --inst_eager_unprocessed_to_passive     true
% 11.52/2.00  --inst_prop_sim_given                   true
% 11.52/2.00  --inst_prop_sim_new                     false
% 11.52/2.00  --inst_subs_new                         false
% 11.52/2.00  --inst_eq_res_simp                      false
% 11.52/2.00  --inst_subs_given                       false
% 11.52/2.00  --inst_orphan_elimination               true
% 11.52/2.00  --inst_learning_loop_flag               true
% 11.52/2.00  --inst_learning_start                   3000
% 11.52/2.00  --inst_learning_factor                  2
% 11.52/2.00  --inst_start_prop_sim_after_learn       3
% 11.52/2.00  --inst_sel_renew                        solver
% 11.52/2.00  --inst_lit_activity_flag                true
% 11.52/2.00  --inst_restr_to_given                   false
% 11.52/2.00  --inst_activity_threshold               500
% 11.52/2.00  --inst_out_proof                        true
% 11.52/2.00  
% 11.52/2.00  ------ Resolution Options
% 11.52/2.00  
% 11.52/2.00  --resolution_flag                       false
% 11.52/2.00  --res_lit_sel                           adaptive
% 11.52/2.00  --res_lit_sel_side                      none
% 11.52/2.00  --res_ordering                          kbo
% 11.52/2.00  --res_to_prop_solver                    active
% 11.52/2.00  --res_prop_simpl_new                    false
% 11.52/2.00  --res_prop_simpl_given                  true
% 11.52/2.00  --res_passive_queue_type                priority_queues
% 11.52/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.52/2.00  --res_passive_queues_freq               [15;5]
% 11.52/2.00  --res_forward_subs                      full
% 11.52/2.00  --res_backward_subs                     full
% 11.52/2.00  --res_forward_subs_resolution           true
% 11.52/2.00  --res_backward_subs_resolution          true
% 11.52/2.00  --res_orphan_elimination                true
% 11.52/2.00  --res_time_limit                        2.
% 11.52/2.00  --res_out_proof                         true
% 11.52/2.00  
% 11.52/2.00  ------ Superposition Options
% 11.52/2.00  
% 11.52/2.00  --superposition_flag                    true
% 11.52/2.00  --sup_passive_queue_type                priority_queues
% 11.52/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.52/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.52/2.00  --demod_completeness_check              fast
% 11.52/2.00  --demod_use_ground                      true
% 11.52/2.00  --sup_to_prop_solver                    passive
% 11.52/2.00  --sup_prop_simpl_new                    true
% 11.52/2.00  --sup_prop_simpl_given                  true
% 11.52/2.00  --sup_fun_splitting                     false
% 11.52/2.00  --sup_smt_interval                      50000
% 11.52/2.00  
% 11.52/2.00  ------ Superposition Simplification Setup
% 11.52/2.00  
% 11.52/2.00  --sup_indices_passive                   []
% 11.52/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.52/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.52/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.52/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.52/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.52/2.00  --sup_full_bw                           [BwDemod]
% 11.52/2.00  --sup_immed_triv                        [TrivRules]
% 11.52/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.52/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.52/2.00  --sup_immed_bw_main                     []
% 11.52/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.52/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.52/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.52/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.52/2.00  
% 11.52/2.00  ------ Combination Options
% 11.52/2.00  
% 11.52/2.00  --comb_res_mult                         3
% 11.52/2.00  --comb_sup_mult                         2
% 11.52/2.00  --comb_inst_mult                        10
% 11.52/2.00  
% 11.52/2.00  ------ Debug Options
% 11.52/2.00  
% 11.52/2.00  --dbg_backtrace                         false
% 11.52/2.00  --dbg_dump_prop_clauses                 false
% 11.52/2.00  --dbg_dump_prop_clauses_file            -
% 11.52/2.00  --dbg_out_stat                          false
% 11.52/2.00  
% 11.52/2.00  
% 11.52/2.00  
% 11.52/2.00  
% 11.52/2.00  ------ Proving...
% 11.52/2.00  
% 11.52/2.00  
% 11.52/2.00  % SZS status Theorem for theBenchmark.p
% 11.52/2.00  
% 11.52/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.52/2.00  
% 11.52/2.00  fof(f8,conjecture,(
% 11.52/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 11.52/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.52/2.00  
% 11.52/2.00  fof(f9,negated_conjecture,(
% 11.52/2.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 11.52/2.00    inference(negated_conjecture,[],[f8])).
% 11.52/2.00  
% 11.52/2.00  fof(f19,plain,(
% 11.52/2.00    ? [X0] : (? [X1] : ((~v3_tex_2(X1,X0) & (v2_tex_2(X1,X0) & v1_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 11.52/2.00    inference(ennf_transformation,[],[f9])).
% 11.52/2.00  
% 11.52/2.00  fof(f20,plain,(
% 11.52/2.00    ? [X0] : (? [X1] : (~v3_tex_2(X1,X0) & v2_tex_2(X1,X0) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 11.52/2.00    inference(flattening,[],[f19])).
% 11.52/2.00  
% 11.52/2.00  fof(f35,plain,(
% 11.52/2.00    ( ! [X0] : (? [X1] : (~v3_tex_2(X1,X0) & v2_tex_2(X1,X0) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_tex_2(sK3,X0) & v2_tex_2(sK3,X0) & v1_tops_1(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.52/2.00    introduced(choice_axiom,[])).
% 11.52/2.00  
% 11.52/2.00  fof(f34,plain,(
% 11.52/2.00    ? [X0] : (? [X1] : (~v3_tex_2(X1,X0) & v2_tex_2(X1,X0) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v3_tex_2(X1,sK2) & v2_tex_2(X1,sK2) & v1_tops_1(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 11.52/2.00    introduced(choice_axiom,[])).
% 11.52/2.00  
% 11.52/2.00  fof(f36,plain,(
% 11.52/2.00    (~v3_tex_2(sK3,sK2) & v2_tex_2(sK3,sK2) & v1_tops_1(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 11.52/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f35,f34])).
% 11.52/2.00  
% 11.52/2.00  fof(f59,plain,(
% 11.52/2.00    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 11.52/2.00    inference(cnf_transformation,[],[f36])).
% 11.52/2.00  
% 11.52/2.00  fof(f6,axiom,(
% 11.52/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 11.52/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.52/2.00  
% 11.52/2.00  fof(f15,plain,(
% 11.52/2.00    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.52/2.00    inference(ennf_transformation,[],[f6])).
% 11.52/2.00  
% 11.52/2.00  fof(f16,plain,(
% 11.52/2.00    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.52/2.00    inference(flattening,[],[f15])).
% 11.52/2.00  
% 11.52/2.00  fof(f25,plain,(
% 11.52/2.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.52/2.00    inference(nnf_transformation,[],[f16])).
% 11.52/2.00  
% 11.52/2.00  fof(f26,plain,(
% 11.52/2.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.52/2.00    inference(flattening,[],[f25])).
% 11.52/2.00  
% 11.52/2.00  fof(f27,plain,(
% 11.52/2.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.52/2.00    inference(rectify,[],[f26])).
% 11.52/2.00  
% 11.52/2.00  fof(f28,plain,(
% 11.52/2.00    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK0(X0,X1) != X1 & r1_tarski(X1,sK0(X0,X1)) & v2_tex_2(sK0(X0,X1),X0) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.52/2.00    introduced(choice_axiom,[])).
% 11.52/2.00  
% 11.52/2.00  fof(f29,plain,(
% 11.52/2.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK0(X0,X1) != X1 & r1_tarski(X1,sK0(X0,X1)) & v2_tex_2(sK0(X0,X1),X0) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.52/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 11.52/2.00  
% 11.52/2.00  fof(f48,plain,(
% 11.52/2.00    ( ! [X0,X1] : (v3_tex_2(X1,X0) | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.52/2.00    inference(cnf_transformation,[],[f29])).
% 11.52/2.00  
% 11.52/2.00  fof(f58,plain,(
% 11.52/2.00    l1_pre_topc(sK2)),
% 11.52/2.00    inference(cnf_transformation,[],[f36])).
% 11.52/2.00  
% 11.52/2.00  fof(f5,axiom,(
% 11.52/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 11.52/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.52/2.00  
% 11.52/2.00  fof(f14,plain,(
% 11.52/2.00    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.52/2.00    inference(ennf_transformation,[],[f5])).
% 11.52/2.00  
% 11.52/2.00  fof(f24,plain,(
% 11.52/2.00    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.52/2.00    inference(nnf_transformation,[],[f14])).
% 11.52/2.00  
% 11.52/2.00  fof(f44,plain,(
% 11.52/2.00    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.52/2.00    inference(cnf_transformation,[],[f24])).
% 11.52/2.00  
% 11.52/2.00  fof(f60,plain,(
% 11.52/2.00    v1_tops_1(sK3,sK2)),
% 11.52/2.00    inference(cnf_transformation,[],[f36])).
% 11.52/2.00  
% 11.52/2.00  fof(f4,axiom,(
% 11.52/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 11.52/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.52/2.00  
% 11.52/2.00  fof(f12,plain,(
% 11.52/2.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.52/2.00    inference(ennf_transformation,[],[f4])).
% 11.52/2.00  
% 11.52/2.00  fof(f13,plain,(
% 11.52/2.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.52/2.00    inference(flattening,[],[f12])).
% 11.52/2.00  
% 11.52/2.00  fof(f43,plain,(
% 11.52/2.00    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.52/2.00    inference(cnf_transformation,[],[f13])).
% 11.52/2.00  
% 11.52/2.00  fof(f1,axiom,(
% 11.52/2.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.52/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.52/2.00  
% 11.52/2.00  fof(f21,plain,(
% 11.52/2.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.52/2.00    inference(nnf_transformation,[],[f1])).
% 11.52/2.00  
% 11.52/2.00  fof(f22,plain,(
% 11.52/2.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.52/2.00    inference(flattening,[],[f21])).
% 11.52/2.00  
% 11.52/2.00  fof(f39,plain,(
% 11.52/2.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.52/2.00    inference(cnf_transformation,[],[f22])).
% 11.52/2.00  
% 11.52/2.00  fof(f3,axiom,(
% 11.52/2.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.52/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.52/2.00  
% 11.52/2.00  fof(f10,plain,(
% 11.52/2.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.52/2.00    inference(ennf_transformation,[],[f3])).
% 11.52/2.00  
% 11.52/2.00  fof(f11,plain,(
% 11.52/2.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.52/2.00    inference(flattening,[],[f10])).
% 11.52/2.00  
% 11.52/2.00  fof(f42,plain,(
% 11.52/2.00    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.52/2.00    inference(cnf_transformation,[],[f11])).
% 11.52/2.00  
% 11.52/2.00  fof(f2,axiom,(
% 11.52/2.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.52/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.52/2.00  
% 11.52/2.00  fof(f23,plain,(
% 11.52/2.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.52/2.00    inference(nnf_transformation,[],[f2])).
% 11.52/2.00  
% 11.52/2.00  fof(f40,plain,(
% 11.52/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.52/2.00    inference(cnf_transformation,[],[f23])).
% 11.52/2.00  
% 11.52/2.00  fof(f61,plain,(
% 11.52/2.00    v2_tex_2(sK3,sK2)),
% 11.52/2.00    inference(cnf_transformation,[],[f36])).
% 11.52/2.00  
% 11.52/2.00  fof(f62,plain,(
% 11.52/2.00    ~v3_tex_2(sK3,sK2)),
% 11.52/2.00    inference(cnf_transformation,[],[f36])).
% 11.52/2.00  
% 11.52/2.00  fof(f50,plain,(
% 11.52/2.00    ( ! [X0,X1] : (v3_tex_2(X1,X0) | r1_tarski(X1,sK0(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.52/2.00    inference(cnf_transformation,[],[f29])).
% 11.52/2.00  
% 11.52/2.00  fof(f37,plain,(
% 11.52/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.52/2.00    inference(cnf_transformation,[],[f22])).
% 11.52/2.00  
% 11.52/2.00  fof(f64,plain,(
% 11.52/2.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.52/2.00    inference(equality_resolution,[],[f37])).
% 11.52/2.00  
% 11.52/2.00  fof(f41,plain,(
% 11.52/2.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.52/2.00    inference(cnf_transformation,[],[f23])).
% 11.52/2.00  
% 11.52/2.00  fof(f7,axiom,(
% 11.52/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 11.52/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.52/2.00  
% 11.52/2.00  fof(f17,plain,(
% 11.52/2.00    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.52/2.00    inference(ennf_transformation,[],[f7])).
% 11.52/2.00  
% 11.52/2.00  fof(f18,plain,(
% 11.52/2.00    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.52/2.00    inference(flattening,[],[f17])).
% 11.52/2.00  
% 11.52/2.00  fof(f30,plain,(
% 11.52/2.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.52/2.00    inference(nnf_transformation,[],[f18])).
% 11.52/2.00  
% 11.52/2.00  fof(f31,plain,(
% 11.52/2.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.52/2.00    inference(rectify,[],[f30])).
% 11.52/2.00  
% 11.52/2.00  fof(f32,plain,(
% 11.52/2.00    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK1(X0,X1))) != sK1(X0,X1) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.52/2.00    introduced(choice_axiom,[])).
% 11.52/2.00  
% 11.52/2.00  fof(f33,plain,(
% 11.52/2.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK1(X0,X1))) != sK1(X0,X1) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.52/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 11.52/2.00  
% 11.52/2.00  fof(f52,plain,(
% 11.52/2.00    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.52/2.00    inference(cnf_transformation,[],[f33])).
% 11.52/2.00  
% 11.52/2.00  fof(f57,plain,(
% 11.52/2.00    v2_pre_topc(sK2)),
% 11.52/2.00    inference(cnf_transformation,[],[f36])).
% 11.52/2.00  
% 11.52/2.00  fof(f56,plain,(
% 11.52/2.00    ~v2_struct_0(sK2)),
% 11.52/2.00    inference(cnf_transformation,[],[f36])).
% 11.52/2.00  
% 11.52/2.00  fof(f49,plain,(
% 11.52/2.00    ( ! [X0,X1] : (v3_tex_2(X1,X0) | v2_tex_2(sK0(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.52/2.00    inference(cnf_transformation,[],[f29])).
% 11.52/2.00  
% 11.52/2.00  fof(f51,plain,(
% 11.52/2.00    ( ! [X0,X1] : (v3_tex_2(X1,X0) | sK0(X0,X1) != X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.52/2.00    inference(cnf_transformation,[],[f29])).
% 11.52/2.00  
% 11.52/2.00  cnf(c_22,negated_conjecture,
% 11.52/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 11.52/2.00      inference(cnf_transformation,[],[f59]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1619,plain,
% 11.52/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_12,plain,
% 11.52/2.00      ( ~ v2_tex_2(X0,X1)
% 11.52/2.00      | v3_tex_2(X0,X1)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.52/2.00      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.52/2.00      | ~ l1_pre_topc(X1) ),
% 11.52/2.00      inference(cnf_transformation,[],[f48]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_23,negated_conjecture,
% 11.52/2.00      ( l1_pre_topc(sK2) ),
% 11.52/2.00      inference(cnf_transformation,[],[f58]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_487,plain,
% 11.52/2.00      ( ~ v2_tex_2(X0,X1)
% 11.52/2.00      | v3_tex_2(X0,X1)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.52/2.00      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.52/2.00      | sK2 != X1 ),
% 11.52/2.00      inference(resolution_lifted,[status(thm)],[c_12,c_23]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_488,plain,
% 11.52/2.00      ( ~ v2_tex_2(X0,sK2)
% 11.52/2.00      | v3_tex_2(X0,sK2)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.52/2.00      | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 11.52/2.00      inference(unflattening,[status(thm)],[c_487]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1612,plain,
% 11.52/2.00      ( v2_tex_2(X0,sK2) != iProver_top
% 11.52/2.00      | v3_tex_2(X0,sK2) = iProver_top
% 11.52/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.52/2.00      | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_488]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_8,plain,
% 11.52/2.00      ( ~ v1_tops_1(X0,X1)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.52/2.00      | ~ l1_pre_topc(X1)
% 11.52/2.00      | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
% 11.52/2.00      inference(cnf_transformation,[],[f44]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_21,negated_conjecture,
% 11.52/2.00      ( v1_tops_1(sK3,sK2) ),
% 11.52/2.00      inference(cnf_transformation,[],[f60]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_331,plain,
% 11.52/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.52/2.00      | ~ l1_pre_topc(X1)
% 11.52/2.00      | k2_pre_topc(X1,X0) = u1_struct_0(X1)
% 11.52/2.00      | sK2 != X1
% 11.52/2.00      | sK3 != X0 ),
% 11.52/2.00      inference(resolution_lifted,[status(thm)],[c_8,c_21]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_332,plain,
% 11.52/2.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.52/2.00      | ~ l1_pre_topc(sK2)
% 11.52/2.00      | k2_pre_topc(sK2,sK3) = u1_struct_0(sK2) ),
% 11.52/2.00      inference(unflattening,[status(thm)],[c_331]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_334,plain,
% 11.52/2.00      ( k2_pre_topc(sK2,sK3) = u1_struct_0(sK2) ),
% 11.52/2.00      inference(global_propositional_subsumption,
% 11.52/2.00                [status(thm)],
% 11.52/2.00                [c_332,c_23,c_22]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_6,plain,
% 11.52/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.52/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.52/2.00      | ~ r1_tarski(X0,X2)
% 11.52/2.00      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
% 11.52/2.00      | ~ l1_pre_topc(X1) ),
% 11.52/2.00      inference(cnf_transformation,[],[f43]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_559,plain,
% 11.52/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.52/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.52/2.00      | ~ r1_tarski(X0,X2)
% 11.52/2.00      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
% 11.52/2.00      | sK2 != X1 ),
% 11.52/2.00      inference(resolution_lifted,[status(thm)],[c_6,c_23]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_560,plain,
% 11.52/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.52/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.52/2.00      | ~ r1_tarski(X0,X1)
% 11.52/2.00      | r1_tarski(k2_pre_topc(sK2,X0),k2_pre_topc(sK2,X1)) ),
% 11.52/2.00      inference(unflattening,[status(thm)],[c_559]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1608,plain,
% 11.52/2.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.52/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.52/2.00      | r1_tarski(X0,X1) != iProver_top
% 11.52/2.00      | r1_tarski(k2_pre_topc(sK2,X0),k2_pre_topc(sK2,X1)) = iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_560]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2082,plain,
% 11.52/2.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.52/2.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.52/2.00      | r1_tarski(u1_struct_0(sK2),k2_pre_topc(sK2,X0)) = iProver_top
% 11.52/2.00      | r1_tarski(sK3,X0) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_334,c_1608]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_29,plain,
% 11.52/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2377,plain,
% 11.52/2.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.52/2.00      | r1_tarski(u1_struct_0(sK2),k2_pre_topc(sK2,X0)) = iProver_top
% 11.52/2.00      | r1_tarski(sK3,X0) != iProver_top ),
% 11.52/2.00      inference(global_propositional_subsumption,
% 11.52/2.00                [status(thm)],
% 11.52/2.00                [c_2082,c_29]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_0,plain,
% 11.52/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.52/2.00      inference(cnf_transformation,[],[f39]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1625,plain,
% 11.52/2.00      ( X0 = X1
% 11.52/2.00      | r1_tarski(X1,X0) != iProver_top
% 11.52/2.00      | r1_tarski(X0,X1) != iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2387,plain,
% 11.52/2.00      ( k2_pre_topc(sK2,X0) = u1_struct_0(sK2)
% 11.52/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.52/2.00      | r1_tarski(k2_pre_topc(sK2,X0),u1_struct_0(sK2)) != iProver_top
% 11.52/2.00      | r1_tarski(sK3,X0) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_2377,c_1625]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_5,plain,
% 11.52/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.52/2.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.52/2.00      | ~ l1_pre_topc(X1) ),
% 11.52/2.00      inference(cnf_transformation,[],[f42]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_577,plain,
% 11.52/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.52/2.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.52/2.00      | sK2 != X1 ),
% 11.52/2.00      inference(resolution_lifted,[status(thm)],[c_5,c_23]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_578,plain,
% 11.52/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.52/2.00      | m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 11.52/2.00      inference(unflattening,[status(thm)],[c_577]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1607,plain,
% 11.52/2.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.52/2.00      | m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_578]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_4,plain,
% 11.52/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.52/2.00      inference(cnf_transformation,[],[f40]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1622,plain,
% 11.52/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.52/2.00      | r1_tarski(X0,X1) = iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2176,plain,
% 11.52/2.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.52/2.00      | r1_tarski(k2_pre_topc(sK2,X0),u1_struct_0(sK2)) = iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_1607,c_1622]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_4511,plain,
% 11.52/2.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.52/2.00      | k2_pre_topc(sK2,X0) = u1_struct_0(sK2)
% 11.52/2.00      | r1_tarski(sK3,X0) != iProver_top ),
% 11.52/2.00      inference(global_propositional_subsumption,
% 11.52/2.00                [status(thm)],
% 11.52/2.00                [c_2387,c_2176]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_4512,plain,
% 11.52/2.00      ( k2_pre_topc(sK2,X0) = u1_struct_0(sK2)
% 11.52/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.52/2.00      | r1_tarski(sK3,X0) != iProver_top ),
% 11.52/2.00      inference(renaming,[status(thm)],[c_4511]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_4523,plain,
% 11.52/2.00      ( k2_pre_topc(sK2,sK0(sK2,X0)) = u1_struct_0(sK2)
% 11.52/2.00      | v2_tex_2(X0,sK2) != iProver_top
% 11.52/2.00      | v3_tex_2(X0,sK2) = iProver_top
% 11.52/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.52/2.00      | r1_tarski(sK3,sK0(sK2,X0)) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_1612,c_4512]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_43593,plain,
% 11.52/2.00      ( k2_pre_topc(sK2,sK0(sK2,sK3)) = u1_struct_0(sK2)
% 11.52/2.00      | v2_tex_2(sK3,sK2) != iProver_top
% 11.52/2.00      | v3_tex_2(sK3,sK2) = iProver_top
% 11.52/2.00      | r1_tarski(sK3,sK0(sK2,sK3)) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_1619,c_4523]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_20,negated_conjecture,
% 11.52/2.00      ( v2_tex_2(sK3,sK2) ),
% 11.52/2.00      inference(cnf_transformation,[],[f61]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_31,plain,
% 11.52/2.00      ( v2_tex_2(sK3,sK2) = iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_19,negated_conjecture,
% 11.52/2.00      ( ~ v3_tex_2(sK3,sK2) ),
% 11.52/2.00      inference(cnf_transformation,[],[f62]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_32,plain,
% 11.52/2.00      ( v3_tex_2(sK3,sK2) != iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_10,plain,
% 11.52/2.00      ( ~ v2_tex_2(X0,X1)
% 11.52/2.00      | v3_tex_2(X0,X1)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.52/2.00      | r1_tarski(X0,sK0(X1,X0))
% 11.52/2.00      | ~ l1_pre_topc(X1) ),
% 11.52/2.00      inference(cnf_transformation,[],[f50]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_523,plain,
% 11.52/2.00      ( ~ v2_tex_2(X0,X1)
% 11.52/2.00      | v3_tex_2(X0,X1)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.52/2.00      | r1_tarski(X0,sK0(X1,X0))
% 11.52/2.00      | sK2 != X1 ),
% 11.52/2.00      inference(resolution_lifted,[status(thm)],[c_10,c_23]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_524,plain,
% 11.52/2.00      ( ~ v2_tex_2(X0,sK2)
% 11.52/2.00      | v3_tex_2(X0,sK2)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.52/2.00      | r1_tarski(X0,sK0(sK2,X0)) ),
% 11.52/2.00      inference(unflattening,[status(thm)],[c_523]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_640,plain,
% 11.52/2.00      ( ~ v2_tex_2(X0,sK2)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.52/2.00      | r1_tarski(X0,sK0(sK2,X0))
% 11.52/2.00      | sK2 != sK2
% 11.52/2.00      | sK3 != X0 ),
% 11.52/2.00      inference(resolution_lifted,[status(thm)],[c_19,c_524]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_641,plain,
% 11.52/2.00      ( ~ v2_tex_2(sK3,sK2)
% 11.52/2.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.52/2.00      | r1_tarski(sK3,sK0(sK2,sK3)) ),
% 11.52/2.00      inference(unflattening,[status(thm)],[c_640]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_642,plain,
% 11.52/2.00      ( v2_tex_2(sK3,sK2) != iProver_top
% 11.52/2.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.52/2.00      | r1_tarski(sK3,sK0(sK2,sK3)) = iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_641]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_43944,plain,
% 11.52/2.00      ( k2_pre_topc(sK2,sK0(sK2,sK3)) = u1_struct_0(sK2) ),
% 11.52/2.00      inference(global_propositional_subsumption,
% 11.52/2.00                [status(thm)],
% 11.52/2.00                [c_43593,c_29,c_31,c_32,c_642]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2,plain,
% 11.52/2.00      ( r1_tarski(X0,X0) ),
% 11.52/2.00      inference(cnf_transformation,[],[f64]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1624,plain,
% 11.52/2.00      ( r1_tarski(X0,X0) = iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_3,plain,
% 11.52/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.52/2.00      inference(cnf_transformation,[],[f41]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1623,plain,
% 11.52/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 11.52/2.00      | r1_tarski(X0,X1) != iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_18,plain,
% 11.52/2.00      ( ~ v2_tex_2(X0,X1)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.52/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.52/2.00      | ~ r1_tarski(X2,X0)
% 11.52/2.00      | v2_struct_0(X1)
% 11.52/2.00      | ~ v2_pre_topc(X1)
% 11.52/2.00      | ~ l1_pre_topc(X1)
% 11.52/2.00      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
% 11.52/2.00      inference(cnf_transformation,[],[f52]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_24,negated_conjecture,
% 11.52/2.00      ( v2_pre_topc(sK2) ),
% 11.52/2.00      inference(cnf_transformation,[],[f57]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_340,plain,
% 11.52/2.00      ( ~ v2_tex_2(X0,X1)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.52/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.52/2.00      | ~ r1_tarski(X2,X0)
% 11.52/2.00      | v2_struct_0(X1)
% 11.52/2.00      | ~ l1_pre_topc(X1)
% 11.52/2.00      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
% 11.52/2.00      | sK2 != X1 ),
% 11.52/2.00      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_341,plain,
% 11.52/2.00      ( ~ v2_tex_2(X0,sK2)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.52/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.52/2.00      | ~ r1_tarski(X1,X0)
% 11.52/2.00      | v2_struct_0(sK2)
% 11.52/2.00      | ~ l1_pre_topc(sK2)
% 11.52/2.00      | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
% 11.52/2.00      inference(unflattening,[status(thm)],[c_340]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_25,negated_conjecture,
% 11.52/2.00      ( ~ v2_struct_0(sK2) ),
% 11.52/2.00      inference(cnf_transformation,[],[f56]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_345,plain,
% 11.52/2.00      ( ~ v2_tex_2(X0,sK2)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.52/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.52/2.00      | ~ r1_tarski(X1,X0)
% 11.52/2.00      | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
% 11.52/2.00      inference(global_propositional_subsumption,
% 11.52/2.00                [status(thm)],
% 11.52/2.00                [c_341,c_25,c_23]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1618,plain,
% 11.52/2.00      ( k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1
% 11.52/2.00      | v2_tex_2(X0,sK2) != iProver_top
% 11.52/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.52/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.52/2.00      | r1_tarski(X1,X0) != iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_345]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_3573,plain,
% 11.52/2.00      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,X0),k2_pre_topc(sK2,X1)) = X1
% 11.52/2.00      | v2_tex_2(X0,sK2) != iProver_top
% 11.52/2.00      | v2_tex_2(sK0(sK2,X0),sK2) != iProver_top
% 11.52/2.00      | v3_tex_2(X0,sK2) = iProver_top
% 11.52/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.52/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.52/2.00      | r1_tarski(X1,sK0(sK2,X0)) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_1612,c_1618]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_11,plain,
% 11.52/2.00      ( ~ v2_tex_2(X0,X1)
% 11.52/2.00      | v2_tex_2(sK0(X1,X0),X1)
% 11.52/2.00      | v3_tex_2(X0,X1)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.52/2.00      | ~ l1_pre_topc(X1) ),
% 11.52/2.00      inference(cnf_transformation,[],[f49]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_505,plain,
% 11.52/2.00      ( ~ v2_tex_2(X0,X1)
% 11.52/2.00      | v2_tex_2(sK0(X1,X0),X1)
% 11.52/2.00      | v3_tex_2(X0,X1)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.52/2.00      | sK2 != X1 ),
% 11.52/2.00      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_506,plain,
% 11.52/2.00      ( ~ v2_tex_2(X0,sK2)
% 11.52/2.00      | v2_tex_2(sK0(sK2,X0),sK2)
% 11.52/2.00      | v3_tex_2(X0,sK2)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 11.52/2.00      inference(unflattening,[status(thm)],[c_505]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_507,plain,
% 11.52/2.00      ( v2_tex_2(X0,sK2) != iProver_top
% 11.52/2.00      | v2_tex_2(sK0(sK2,X0),sK2) = iProver_top
% 11.52/2.00      | v3_tex_2(X0,sK2) = iProver_top
% 11.52/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_506]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_29708,plain,
% 11.52/2.00      ( v2_tex_2(X0,sK2) != iProver_top
% 11.52/2.00      | k9_subset_1(u1_struct_0(sK2),sK0(sK2,X0),k2_pre_topc(sK2,X1)) = X1
% 11.52/2.00      | v3_tex_2(X0,sK2) = iProver_top
% 11.52/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.52/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.52/2.00      | r1_tarski(X1,sK0(sK2,X0)) != iProver_top ),
% 11.52/2.00      inference(global_propositional_subsumption,
% 11.52/2.00                [status(thm)],
% 11.52/2.00                [c_3573,c_507]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_29709,plain,
% 11.52/2.00      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,X0),k2_pre_topc(sK2,X1)) = X1
% 11.52/2.00      | v2_tex_2(X0,sK2) != iProver_top
% 11.52/2.00      | v3_tex_2(X0,sK2) = iProver_top
% 11.52/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.52/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.52/2.00      | r1_tarski(X1,sK0(sK2,X0)) != iProver_top ),
% 11.52/2.00      inference(renaming,[status(thm)],[c_29708]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_29721,plain,
% 11.52/2.00      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,X0)) = X0
% 11.52/2.00      | v2_tex_2(sK3,sK2) != iProver_top
% 11.52/2.00      | v3_tex_2(sK3,sK2) = iProver_top
% 11.52/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.52/2.00      | r1_tarski(X0,sK0(sK2,sK3)) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_1619,c_29709]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_29806,plain,
% 11.52/2.00      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,X0)) = X0
% 11.52/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.52/2.00      | r1_tarski(X0,sK0(sK2,sK3)) != iProver_top ),
% 11.52/2.00      inference(global_propositional_subsumption,
% 11.52/2.00                [status(thm)],
% 11.52/2.00                [c_29721,c_31,c_32]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_29815,plain,
% 11.52/2.00      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,X0)) = X0
% 11.52/2.00      | r1_tarski(X0,sK0(sK2,sK3)) != iProver_top
% 11.52/2.00      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_1623,c_29806]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_29981,plain,
% 11.52/2.00      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,sK0(sK2,sK3))) = sK0(sK2,sK3)
% 11.52/2.00      | r1_tarski(sK0(sK2,sK3),u1_struct_0(sK2)) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_1624,c_29815]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_651,plain,
% 11.52/2.00      ( ~ v2_tex_2(X0,sK2)
% 11.52/2.00      | v2_tex_2(sK0(sK2,X0),sK2)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.52/2.00      | sK2 != sK2
% 11.52/2.00      | sK3 != X0 ),
% 11.52/2.00      inference(resolution_lifted,[status(thm)],[c_19,c_506]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_652,plain,
% 11.52/2.00      ( v2_tex_2(sK0(sK2,sK3),sK2)
% 11.52/2.00      | ~ v2_tex_2(sK3,sK2)
% 11.52/2.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 11.52/2.00      inference(unflattening,[status(thm)],[c_651]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_662,plain,
% 11.52/2.00      ( ~ v2_tex_2(X0,sK2)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.52/2.00      | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 11.52/2.00      | sK2 != sK2
% 11.52/2.00      | sK3 != X0 ),
% 11.52/2.00      inference(resolution_lifted,[status(thm)],[c_19,c_488]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_663,plain,
% 11.52/2.00      ( ~ v2_tex_2(sK3,sK2)
% 11.52/2.00      | m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 11.52/2.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 11.52/2.00      inference(unflattening,[status(thm)],[c_662]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1885,plain,
% 11.52/2.00      ( ~ v2_tex_2(sK0(sK2,sK3),sK2)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.52/2.00      | ~ m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 11.52/2.00      | ~ r1_tarski(X0,sK0(sK2,sK3))
% 11.52/2.00      | k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,X0)) = X0 ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_345]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2266,plain,
% 11.52/2.00      ( ~ v2_tex_2(sK0(sK2,sK3),sK2)
% 11.52/2.00      | ~ m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 11.52/2.00      | ~ r1_tarski(sK0(sK2,sK3),sK0(sK2,sK3))
% 11.52/2.00      | k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,sK0(sK2,sK3))) = sK0(sK2,sK3) ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_1885]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2672,plain,
% 11.52/2.00      ( r1_tarski(sK0(sK2,sK3),sK0(sK2,sK3)) ),
% 11.52/2.00      inference(instantiation,[status(thm)],[c_2]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_30007,plain,
% 11.52/2.00      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,sK0(sK2,sK3))) = sK0(sK2,sK3) ),
% 11.52/2.00      inference(global_propositional_subsumption,
% 11.52/2.00                [status(thm)],
% 11.52/2.00                [c_29981,c_22,c_20,c_652,c_663,c_2266,c_2672]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_43947,plain,
% 11.52/2.00      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),u1_struct_0(sK2)) = sK0(sK2,sK3) ),
% 11.52/2.00      inference(demodulation,[status(thm)],[c_43944,c_30007]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_1610,plain,
% 11.52/2.00      ( v2_tex_2(X0,sK2) != iProver_top
% 11.52/2.00      | v3_tex_2(X0,sK2) = iProver_top
% 11.52/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.52/2.00      | r1_tarski(X0,sK0(sK2,X0)) = iProver_top ),
% 11.52/2.00      inference(predicate_to_equality,[status(thm)],[c_524]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_2812,plain,
% 11.52/2.00      ( v2_tex_2(sK3,sK2) != iProver_top
% 11.52/2.00      | v3_tex_2(sK3,sK2) = iProver_top
% 11.52/2.00      | r1_tarski(sK3,sK0(sK2,sK3)) = iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_1619,c_1610]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_3091,plain,
% 11.52/2.00      ( r1_tarski(sK3,sK0(sK2,sK3)) = iProver_top ),
% 11.52/2.00      inference(global_propositional_subsumption,
% 11.52/2.00                [status(thm)],
% 11.52/2.00                [c_2812,c_29,c_31,c_642]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_29984,plain,
% 11.52/2.00      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,sK3)) = sK3
% 11.52/2.00      | r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_3091,c_29815]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_29987,plain,
% 11.52/2.00      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),u1_struct_0(sK2)) = sK3
% 11.52/2.00      | r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top ),
% 11.52/2.00      inference(light_normalisation,[status(thm)],[c_29984,c_334]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_29816,plain,
% 11.52/2.00      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,sK3)) = sK3
% 11.52/2.00      | r1_tarski(sK3,sK0(sK2,sK3)) != iProver_top ),
% 11.52/2.00      inference(superposition,[status(thm)],[c_1619,c_29806]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_29852,plain,
% 11.52/2.00      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),u1_struct_0(sK2)) = sK3
% 11.52/2.00      | r1_tarski(sK3,sK0(sK2,sK3)) != iProver_top ),
% 11.52/2.00      inference(light_normalisation,[status(thm)],[c_29816,c_334]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_30583,plain,
% 11.52/2.00      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),u1_struct_0(sK2)) = sK3 ),
% 11.52/2.00      inference(global_propositional_subsumption,
% 11.52/2.00                [status(thm)],
% 11.52/2.00                [c_29987,c_29,c_31,c_642,c_29852]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_43948,plain,
% 11.52/2.00      ( sK0(sK2,sK3) = sK3 ),
% 11.52/2.00      inference(light_normalisation,[status(thm)],[c_43947,c_30583]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_9,plain,
% 11.52/2.00      ( ~ v2_tex_2(X0,X1)
% 11.52/2.00      | v3_tex_2(X0,X1)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.52/2.00      | ~ l1_pre_topc(X1)
% 11.52/2.00      | sK0(X1,X0) != X0 ),
% 11.52/2.00      inference(cnf_transformation,[],[f51]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_541,plain,
% 11.52/2.00      ( ~ v2_tex_2(X0,X1)
% 11.52/2.00      | v3_tex_2(X0,X1)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.52/2.00      | sK0(X1,X0) != X0
% 11.52/2.00      | sK2 != X1 ),
% 11.52/2.00      inference(resolution_lifted,[status(thm)],[c_9,c_23]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_542,plain,
% 11.52/2.00      ( ~ v2_tex_2(X0,sK2)
% 11.52/2.00      | v3_tex_2(X0,sK2)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.52/2.00      | sK0(sK2,X0) != X0 ),
% 11.52/2.00      inference(unflattening,[status(thm)],[c_541]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_632,plain,
% 11.52/2.00      ( ~ v2_tex_2(X0,sK2)
% 11.52/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.52/2.00      | sK0(sK2,X0) != X0
% 11.52/2.00      | sK2 != sK2
% 11.52/2.00      | sK3 != X0 ),
% 11.52/2.00      inference(resolution_lifted,[status(thm)],[c_19,c_542]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(c_633,plain,
% 11.52/2.00      ( ~ v2_tex_2(sK3,sK2)
% 11.52/2.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.52/2.00      | sK0(sK2,sK3) != sK3 ),
% 11.52/2.00      inference(unflattening,[status(thm)],[c_632]) ).
% 11.52/2.00  
% 11.52/2.00  cnf(contradiction,plain,
% 11.52/2.00      ( $false ),
% 11.52/2.00      inference(minisat,[status(thm)],[c_43948,c_633,c_20,c_22]) ).
% 11.52/2.00  
% 11.52/2.00  
% 11.52/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.52/2.00  
% 11.52/2.00  ------                               Statistics
% 11.52/2.00  
% 11.52/2.00  ------ General
% 11.52/2.00  
% 11.52/2.00  abstr_ref_over_cycles:                  0
% 11.52/2.00  abstr_ref_under_cycles:                 0
% 11.52/2.00  gc_basic_clause_elim:                   0
% 11.52/2.00  forced_gc_time:                         0
% 11.52/2.00  parsing_time:                           0.01
% 11.52/2.00  unif_index_cands_time:                  0.
% 11.52/2.00  unif_index_add_time:                    0.
% 11.52/2.00  orderings_time:                         0.
% 11.52/2.00  out_proof_time:                         0.017
% 11.52/2.00  total_time:                             1.319
% 11.52/2.00  num_of_symbols:                         47
% 11.52/2.00  num_of_terms:                           18487
% 11.52/2.00  
% 11.52/2.00  ------ Preprocessing
% 11.52/2.00  
% 11.52/2.00  num_of_splits:                          0
% 11.52/2.00  num_of_split_atoms:                     0
% 11.52/2.00  num_of_reused_defs:                     0
% 11.52/2.00  num_eq_ax_congr_red:                    12
% 11.52/2.00  num_of_sem_filtered_clauses:            1
% 11.52/2.00  num_of_subtypes:                        0
% 11.52/2.00  monotx_restored_types:                  0
% 11.52/2.00  sat_num_of_epr_types:                   0
% 11.52/2.00  sat_num_of_non_cyclic_types:            0
% 11.52/2.00  sat_guarded_non_collapsed_types:        0
% 11.52/2.00  num_pure_diseq_elim:                    0
% 11.52/2.00  simp_replaced_by:                       0
% 11.52/2.00  res_preprocessed:                       110
% 11.52/2.00  prep_upred:                             0
% 11.52/2.00  prep_unflattend:                        30
% 11.52/2.00  smt_new_axioms:                         0
% 11.52/2.00  pred_elim_cands:                        4
% 11.52/2.00  pred_elim:                              4
% 11.52/2.00  pred_elim_cl:                           5
% 11.52/2.00  pred_elim_cycles:                       6
% 11.52/2.00  merged_defs:                            8
% 11.52/2.00  merged_defs_ncl:                        0
% 11.52/2.00  bin_hyper_res:                          8
% 11.52/2.00  prep_cycles:                            4
% 11.52/2.00  pred_elim_time:                         0.015
% 11.52/2.00  splitting_time:                         0.
% 11.52/2.00  sem_filter_time:                        0.
% 11.52/2.00  monotx_time:                            0.001
% 11.52/2.00  subtype_inf_time:                       0.
% 11.52/2.00  
% 11.52/2.00  ------ Problem properties
% 11.52/2.00  
% 11.52/2.00  clauses:                                20
% 11.52/2.00  conjectures:                            3
% 11.52/2.00  epr:                                    4
% 11.52/2.00  horn:                                   15
% 11.52/2.00  ground:                                 4
% 11.52/2.00  unary:                                  5
% 11.52/2.00  binary:                                 3
% 11.52/2.00  lits:                                   57
% 11.52/2.00  lits_eq:                                6
% 11.52/2.00  fd_pure:                                0
% 11.52/2.00  fd_pseudo:                              0
% 11.52/2.00  fd_cond:                                0
% 11.52/2.00  fd_pseudo_cond:                         2
% 11.52/2.00  ac_symbols:                             0
% 11.52/2.00  
% 11.52/2.00  ------ Propositional Solver
% 11.52/2.00  
% 11.52/2.00  prop_solver_calls:                      31
% 11.52/2.00  prop_fast_solver_calls:                 2879
% 11.52/2.00  smt_solver_calls:                       0
% 11.52/2.00  smt_fast_solver_calls:                  0
% 11.52/2.00  prop_num_of_clauses:                    11211
% 11.52/2.00  prop_preprocess_simplified:             17562
% 11.52/2.00  prop_fo_subsumed:                       173
% 11.52/2.00  prop_solver_time:                       0.
% 11.52/2.00  smt_solver_time:                        0.
% 11.52/2.00  smt_fast_solver_time:                   0.
% 11.52/2.00  prop_fast_solver_time:                  0.
% 11.52/2.00  prop_unsat_core_time:                   0.001
% 11.52/2.00  
% 11.52/2.00  ------ QBF
% 11.52/2.00  
% 11.52/2.00  qbf_q_res:                              0
% 11.52/2.00  qbf_num_tautologies:                    0
% 11.52/2.00  qbf_prep_cycles:                        0
% 11.52/2.00  
% 11.52/2.00  ------ BMC1
% 11.52/2.00  
% 11.52/2.00  bmc1_current_bound:                     -1
% 11.52/2.00  bmc1_last_solved_bound:                 -1
% 11.52/2.00  bmc1_unsat_core_size:                   -1
% 11.52/2.00  bmc1_unsat_core_parents_size:           -1
% 11.52/2.01  bmc1_merge_next_fun:                    0
% 11.52/2.01  bmc1_unsat_core_clauses_time:           0.
% 11.52/2.01  
% 11.52/2.01  ------ Instantiation
% 11.52/2.01  
% 11.52/2.01  inst_num_of_clauses:                    3094
% 11.52/2.01  inst_num_in_passive:                    734
% 11.52/2.01  inst_num_in_active:                     1469
% 11.52/2.01  inst_num_in_unprocessed:                891
% 11.52/2.01  inst_num_of_loops:                      1950
% 11.52/2.01  inst_num_of_learning_restarts:          0
% 11.52/2.01  inst_num_moves_active_passive:          478
% 11.52/2.01  inst_lit_activity:                      0
% 11.52/2.01  inst_lit_activity_moves:                1
% 11.52/2.01  inst_num_tautologies:                   0
% 11.52/2.01  inst_num_prop_implied:                  0
% 11.52/2.01  inst_num_existing_simplified:           0
% 11.52/2.01  inst_num_eq_res_simplified:             0
% 11.52/2.01  inst_num_child_elim:                    0
% 11.52/2.01  inst_num_of_dismatching_blockings:      3193
% 11.52/2.01  inst_num_of_non_proper_insts:           6198
% 11.52/2.01  inst_num_of_duplicates:                 0
% 11.52/2.01  inst_inst_num_from_inst_to_res:         0
% 11.52/2.01  inst_dismatching_checking_time:         0.
% 11.52/2.01  
% 11.52/2.01  ------ Resolution
% 11.52/2.01  
% 11.52/2.01  res_num_of_clauses:                     0
% 11.52/2.01  res_num_in_passive:                     0
% 11.52/2.01  res_num_in_active:                      0
% 11.52/2.01  res_num_of_loops:                       114
% 11.52/2.01  res_forward_subset_subsumed:            306
% 11.52/2.01  res_backward_subset_subsumed:           2
% 11.52/2.01  res_forward_subsumed:                   0
% 11.52/2.01  res_backward_subsumed:                  0
% 11.52/2.01  res_forward_subsumption_resolution:     0
% 11.52/2.01  res_backward_subsumption_resolution:    0
% 11.52/2.01  res_clause_to_clause_subsumption:       21350
% 11.52/2.01  res_orphan_elimination:                 0
% 11.52/2.01  res_tautology_del:                      193
% 11.52/2.01  res_num_eq_res_simplified:              0
% 11.52/2.01  res_num_sel_changes:                    0
% 11.52/2.01  res_moves_from_active_to_pass:          0
% 11.52/2.01  
% 11.52/2.01  ------ Superposition
% 11.52/2.01  
% 11.52/2.01  sup_time_total:                         0.
% 11.52/2.01  sup_time_generating:                    0.
% 11.52/2.01  sup_time_sim_full:                      0.
% 11.52/2.01  sup_time_sim_immed:                     0.
% 11.52/2.01  
% 11.52/2.01  sup_num_of_clauses:                     871
% 11.52/2.01  sup_num_in_active:                      384
% 11.52/2.01  sup_num_in_passive:                     487
% 11.52/2.01  sup_num_of_loops:                       388
% 11.52/2.01  sup_fw_superposition:                   1764
% 11.52/2.01  sup_bw_superposition:                   63
% 11.52/2.01  sup_immediate_simplified:               730
% 11.52/2.01  sup_given_eliminated:                   0
% 11.52/2.01  comparisons_done:                       0
% 11.52/2.01  comparisons_avoided:                    0
% 11.52/2.01  
% 11.52/2.01  ------ Simplifications
% 11.52/2.01  
% 11.52/2.01  
% 11.52/2.01  sim_fw_subset_subsumed:                 98
% 11.52/2.01  sim_bw_subset_subsumed:                 13
% 11.52/2.01  sim_fw_subsumed:                        207
% 11.52/2.01  sim_bw_subsumed:                        3
% 11.52/2.01  sim_fw_subsumption_res:                 2
% 11.52/2.01  sim_bw_subsumption_res:                 0
% 11.52/2.01  sim_tautology_del:                      39
% 11.52/2.01  sim_eq_tautology_del:                   228
% 11.52/2.01  sim_eq_res_simp:                        0
% 11.52/2.01  sim_fw_demodulated:                     12
% 11.52/2.01  sim_bw_demodulated:                     4
% 11.52/2.01  sim_light_normalised:                   590
% 11.52/2.01  sim_joinable_taut:                      0
% 11.52/2.01  sim_joinable_simp:                      0
% 11.52/2.01  sim_ac_normalised:                      0
% 11.52/2.01  sim_smt_subsumption:                    0
% 11.52/2.01  
%------------------------------------------------------------------------------
