%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:15 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :  169 (1365 expanded)
%              Number of clauses        :   96 ( 361 expanded)
%              Number of leaves         :   19 ( 305 expanded)
%              Depth                    :   24
%              Number of atoms          :  651 (8034 expanded)
%              Number of equality atoms :  164 ( 520 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( v1_subset_1(sK3,u1_struct_0(X0))
          | ~ v3_tex_2(sK3,X0) )
        & ( ~ v1_subset_1(sK3,u1_struct_0(X0))
          | v3_tex_2(sK3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( v1_subset_1(X1,u1_struct_0(X0))
              | ~ v3_tex_2(X1,X0) )
            & ( ~ v1_subset_1(X1,u1_struct_0(X0))
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(sK2))
            | ~ v3_tex_2(X1,sK2) )
          & ( ~ v1_subset_1(X1,u1_struct_0(sK2))
            | v3_tex_2(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v1_tdlat_3(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ( v1_subset_1(sK3,u1_struct_0(sK2))
      | ~ v3_tex_2(sK3,sK2) )
    & ( ~ v1_subset_1(sK3,u1_struct_0(sK2))
      | v3_tex_2(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v1_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f50,f52,f51])).

fof(f84,plain,
    ( ~ v1_subset_1(sK3,u1_struct_0(sK2))
    | v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f83,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f53])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f62,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f82,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f13,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK1(X0,X1) != X1
        & r1_tarski(X1,sK1(X0,X1))
        & v2_tex_2(sK1(X0,X1),X0)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK1(X0,X1) != X1
                & r1_tarski(X1,sK1(X0,X1))
                & v2_tex_2(sK1(X0,X1),X0)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,(
    v1_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f79,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f80,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( X1 = X3
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f85,plain,
    ( v1_subset_1(sK3,u1_struct_0(sK2))
    | ~ v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f63,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f15,axiom,(
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

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_15,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_26,negated_conjecture,
    ( v3_tex_2(sK3,sK2)
    | ~ v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_237,plain,
    ( v3_tex_2(sK3,sK2)
    | ~ v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(prop_impl,[status(thm)],[c_26])).

cnf(c_579,plain,
    ( v3_tex_2(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 = X0
    | u1_struct_0(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_237])).

cnf(c_580,plain,
    ( v3_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(sK2) = sK3 ),
    inference(unflattening,[status(thm)],[c_579])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_582,plain,
    ( v3_tex_2(sK3,sK2)
    | u1_struct_0(sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_580,c_27])).

cnf(c_1921,plain,
    ( u1_struct_0(sK2) = sK3
    | v3_tex_2(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_582])).

cnf(c_8,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_7,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_410,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_8,c_7])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_617,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_410,c_28])).

cnf(c_618,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_617])).

cnf(c_1943,plain,
    ( k2_struct_0(sK2) = sK3
    | v3_tex_2(sK3,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1921,c_618])).

cnf(c_1925,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1937,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1925,c_618])).

cnf(c_20,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_658,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_28])).

cnf(c_659,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_658])).

cnf(c_23,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_29,negated_conjecture,
    ( v1_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_426,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_29])).

cnf(c_427,plain,
    ( v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_431,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tex_2(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_427,c_31,c_30,c_28])).

cnf(c_432,plain,
    ( v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_431])).

cnf(c_663,plain,
    ( v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_659,c_31,c_30,c_28,c_427])).

cnf(c_1918,plain,
    ( v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_663])).

cnf(c_2001,plain,
    ( v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1918,c_618])).

cnf(c_21,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_631,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | X2 = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_632,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v3_tex_2(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_631])).

cnf(c_636,plain,
    ( ~ v3_tex_2(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_632,c_31,c_30,c_28,c_427])).

cnf(c_637,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,X1)
    | X0 = X1 ),
    inference(renaming,[status(thm)],[c_636])).

cnf(c_1919,plain,
    ( X0 = X1
    | v3_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_637])).

cnf(c_2008,plain,
    ( X0 = X1
    | v3_tex_2(X1,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1919,c_618])).

cnf(c_2203,plain,
    ( sK1(sK2,X0) = X1
    | v3_tex_2(X1,sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,sK1(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2001,c_2008])).

cnf(c_3048,plain,
    ( sK1(sK2,sK3) = X0
    | v3_tex_2(X0,sK2) != iProver_top
    | v3_tex_2(sK3,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1937,c_2203])).

cnf(c_4,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1927,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1940,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1927,c_3])).

cnf(c_2370,plain,
    ( k2_struct_0(sK2) = X0
    | v3_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,k2_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1940,c_2008])).

cnf(c_2559,plain,
    ( k2_struct_0(sK2) = sK3
    | v3_tex_2(sK3,sK2) != iProver_top
    | r1_tarski(sK3,k2_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1937,c_2370])).

cnf(c_6,plain,
    ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_25,negated_conjecture,
    ( ~ v3_tex_2(sK3,sK2)
    | v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_239,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(prop_impl,[status(thm)],[c_25])).

cnf(c_567,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | u1_struct_0(sK2) != X0
    | k2_subset_1(X0) != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_239])).

cnf(c_568,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | k2_subset_1(u1_struct_0(sK2)) != sK3 ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_1922,plain,
    ( k2_subset_1(u1_struct_0(sK2)) != sK3
    | v3_tex_2(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_568])).

cnf(c_1948,plain,
    ( k2_subset_1(k2_struct_0(sK2)) != sK3
    | v3_tex_2(sK3,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1922,c_618])).

cnf(c_1949,plain,
    ( k2_struct_0(sK2) != sK3
    | v3_tex_2(sK3,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1948,c_3])).

cnf(c_2623,plain,
    ( v3_tex_2(sK3,sK2) != iProver_top
    | r1_tarski(sK3,k2_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2559,c_1949])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1929,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1926,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2304,plain,
    ( r2_hidden(X0,k2_struct_0(sK2)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1937,c_1926])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1930,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2696,plain,
    ( r2_hidden(sK0(X0,k2_struct_0(sK2)),sK3) != iProver_top
    | r1_tarski(X0,k2_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2304,c_1930])).

cnf(c_2851,plain,
    ( r1_tarski(sK3,k2_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1929,c_2696])).

cnf(c_3177,plain,
    ( v3_tex_2(X0,sK2) != iProver_top
    | sK1(sK2,sK3) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK1(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3048,c_2623,c_2851])).

cnf(c_3178,plain,
    ( sK1(sK2,sK3) = X0
    | v3_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK1(sK2,sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3177])).

cnf(c_3188,plain,
    ( sK1(sK2,sK3) = sK3
    | v3_tex_2(sK3,sK2) != iProver_top
    | r1_tarski(sK3,sK1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1937,c_3178])).

cnf(c_3218,plain,
    ( v3_tex_2(sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3188,c_2623,c_2851])).

cnf(c_3223,plain,
    ( k2_struct_0(sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_1943,c_3218])).

cnf(c_11,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_9,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_472,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_30])).

cnf(c_473,plain,
    ( v4_pre_topc(k2_struct_0(sK2),sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_83,plain,
    ( v4_pre_topc(k2_struct_0(sK2),sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_475,plain,
    ( v4_pre_topc(k2_struct_0(sK2),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_473,c_30,c_28,c_83])).

cnf(c_510,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0
    | k2_struct_0(sK2) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_475])).

cnf(c_511,plain,
    ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_510])).

cnf(c_513,plain,
    ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_511,c_28])).

cnf(c_1924,plain,
    ( k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2)
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_513])).

cnf(c_1962,plain,
    ( k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2)
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1924,c_618])).

cnf(c_1965,plain,
    ( k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1962,c_1940])).

cnf(c_12,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_24,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_447,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_31])).

cnf(c_448,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ v1_tops_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_447])).

cnf(c_452,plain,
    ( v3_tex_2(X0,sK2)
    | ~ v1_tops_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_448,c_31,c_30,c_28,c_427])).

cnf(c_530,plain,
    ( v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X2)
    | X0 != X1
    | k2_pre_topc(X2,X1) != k2_struct_0(X2)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_452])).

cnf(c_531,plain,
    ( v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | k2_pre_topc(sK2,X0) != k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_535,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_tex_2(X0,sK2)
    | k2_pre_topc(sK2,X0) != k2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_531,c_28])).

cnf(c_536,plain,
    ( v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_pre_topc(sK2,X0) != k2_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_535])).

cnf(c_1923,plain,
    ( k2_pre_topc(sK2,X0) != k2_struct_0(sK2)
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_536])).

cnf(c_1994,plain,
    ( k2_pre_topc(sK2,X0) != k2_struct_0(sK2)
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1923,c_618])).

cnf(c_2441,plain,
    ( v3_tex_2(k2_struct_0(sK2),sK2) = iProver_top
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1965,c_1994])).

cnf(c_2486,plain,
    ( v3_tex_2(k2_struct_0(sK2),sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2441,c_1940])).

cnf(c_3310,plain,
    ( v3_tex_2(sK3,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3223,c_2486])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3310,c_2851,c_2623])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:33:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.05/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/0.99  
% 2.05/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.05/0.99  
% 2.05/0.99  ------  iProver source info
% 2.05/0.99  
% 2.05/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.05/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.05/0.99  git: non_committed_changes: false
% 2.05/0.99  git: last_make_outside_of_git: false
% 2.05/0.99  
% 2.05/0.99  ------ 
% 2.05/0.99  
% 2.05/0.99  ------ Input Options
% 2.05/0.99  
% 2.05/0.99  --out_options                           all
% 2.05/0.99  --tptp_safe_out                         true
% 2.05/0.99  --problem_path                          ""
% 2.05/0.99  --include_path                          ""
% 2.05/0.99  --clausifier                            res/vclausify_rel
% 2.05/0.99  --clausifier_options                    --mode clausify
% 2.05/0.99  --stdin                                 false
% 2.05/0.99  --stats_out                             all
% 2.05/0.99  
% 2.05/0.99  ------ General Options
% 2.05/0.99  
% 2.05/0.99  --fof                                   false
% 2.05/0.99  --time_out_real                         305.
% 2.05/0.99  --time_out_virtual                      -1.
% 2.05/0.99  --symbol_type_check                     false
% 2.05/0.99  --clausify_out                          false
% 2.05/0.99  --sig_cnt_out                           false
% 2.05/0.99  --trig_cnt_out                          false
% 2.05/0.99  --trig_cnt_out_tolerance                1.
% 2.05/0.99  --trig_cnt_out_sk_spl                   false
% 2.05/0.99  --abstr_cl_out                          false
% 2.05/0.99  
% 2.05/0.99  ------ Global Options
% 2.05/0.99  
% 2.05/0.99  --schedule                              default
% 2.05/0.99  --add_important_lit                     false
% 2.05/0.99  --prop_solver_per_cl                    1000
% 2.05/0.99  --min_unsat_core                        false
% 2.05/0.99  --soft_assumptions                      false
% 2.05/0.99  --soft_lemma_size                       3
% 2.05/0.99  --prop_impl_unit_size                   0
% 2.05/0.99  --prop_impl_unit                        []
% 2.05/0.99  --share_sel_clauses                     true
% 2.05/0.99  --reset_solvers                         false
% 2.05/0.99  --bc_imp_inh                            [conj_cone]
% 2.05/0.99  --conj_cone_tolerance                   3.
% 2.05/0.99  --extra_neg_conj                        none
% 2.05/0.99  --large_theory_mode                     true
% 2.05/0.99  --prolific_symb_bound                   200
% 2.05/0.99  --lt_threshold                          2000
% 2.05/0.99  --clause_weak_htbl                      true
% 2.05/0.99  --gc_record_bc_elim                     false
% 2.05/0.99  
% 2.05/0.99  ------ Preprocessing Options
% 2.05/0.99  
% 2.05/0.99  --preprocessing_flag                    true
% 2.05/0.99  --time_out_prep_mult                    0.1
% 2.05/0.99  --splitting_mode                        input
% 2.05/0.99  --splitting_grd                         true
% 2.05/0.99  --splitting_cvd                         false
% 2.05/0.99  --splitting_cvd_svl                     false
% 2.05/0.99  --splitting_nvd                         32
% 2.05/0.99  --sub_typing                            true
% 2.05/0.99  --prep_gs_sim                           true
% 2.05/0.99  --prep_unflatten                        true
% 2.05/0.99  --prep_res_sim                          true
% 2.05/0.99  --prep_upred                            true
% 2.05/0.99  --prep_sem_filter                       exhaustive
% 2.05/0.99  --prep_sem_filter_out                   false
% 2.05/0.99  --pred_elim                             true
% 2.05/0.99  --res_sim_input                         true
% 2.05/0.99  --eq_ax_congr_red                       true
% 2.05/0.99  --pure_diseq_elim                       true
% 2.05/0.99  --brand_transform                       false
% 2.05/0.99  --non_eq_to_eq                          false
% 2.05/0.99  --prep_def_merge                        true
% 2.05/0.99  --prep_def_merge_prop_impl              false
% 2.05/0.99  --prep_def_merge_mbd                    true
% 2.05/0.99  --prep_def_merge_tr_red                 false
% 2.05/0.99  --prep_def_merge_tr_cl                  false
% 2.05/0.99  --smt_preprocessing                     true
% 2.05/0.99  --smt_ac_axioms                         fast
% 2.05/0.99  --preprocessed_out                      false
% 2.05/0.99  --preprocessed_stats                    false
% 2.05/0.99  
% 2.05/0.99  ------ Abstraction refinement Options
% 2.05/0.99  
% 2.05/0.99  --abstr_ref                             []
% 2.05/0.99  --abstr_ref_prep                        false
% 2.05/0.99  --abstr_ref_until_sat                   false
% 2.05/0.99  --abstr_ref_sig_restrict                funpre
% 2.05/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.05/0.99  --abstr_ref_under                       []
% 2.05/0.99  
% 2.05/0.99  ------ SAT Options
% 2.05/0.99  
% 2.05/0.99  --sat_mode                              false
% 2.05/0.99  --sat_fm_restart_options                ""
% 2.05/0.99  --sat_gr_def                            false
% 2.05/0.99  --sat_epr_types                         true
% 2.05/0.99  --sat_non_cyclic_types                  false
% 2.05/0.99  --sat_finite_models                     false
% 2.05/0.99  --sat_fm_lemmas                         false
% 2.05/0.99  --sat_fm_prep                           false
% 2.05/0.99  --sat_fm_uc_incr                        true
% 2.05/0.99  --sat_out_model                         small
% 2.05/0.99  --sat_out_clauses                       false
% 2.05/0.99  
% 2.05/0.99  ------ QBF Options
% 2.05/0.99  
% 2.05/0.99  --qbf_mode                              false
% 2.05/0.99  --qbf_elim_univ                         false
% 2.05/0.99  --qbf_dom_inst                          none
% 2.05/0.99  --qbf_dom_pre_inst                      false
% 2.05/0.99  --qbf_sk_in                             false
% 2.05/0.99  --qbf_pred_elim                         true
% 2.05/0.99  --qbf_split                             512
% 2.05/0.99  
% 2.05/0.99  ------ BMC1 Options
% 2.05/0.99  
% 2.05/0.99  --bmc1_incremental                      false
% 2.05/0.99  --bmc1_axioms                           reachable_all
% 2.05/0.99  --bmc1_min_bound                        0
% 2.05/0.99  --bmc1_max_bound                        -1
% 2.05/0.99  --bmc1_max_bound_default                -1
% 2.05/0.99  --bmc1_symbol_reachability              true
% 2.05/0.99  --bmc1_property_lemmas                  false
% 2.05/0.99  --bmc1_k_induction                      false
% 2.05/0.99  --bmc1_non_equiv_states                 false
% 2.05/0.99  --bmc1_deadlock                         false
% 2.05/0.99  --bmc1_ucm                              false
% 2.05/0.99  --bmc1_add_unsat_core                   none
% 2.05/0.99  --bmc1_unsat_core_children              false
% 2.05/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.05/0.99  --bmc1_out_stat                         full
% 2.05/0.99  --bmc1_ground_init                      false
% 2.05/0.99  --bmc1_pre_inst_next_state              false
% 2.05/0.99  --bmc1_pre_inst_state                   false
% 2.05/0.99  --bmc1_pre_inst_reach_state             false
% 2.05/0.99  --bmc1_out_unsat_core                   false
% 2.05/0.99  --bmc1_aig_witness_out                  false
% 2.05/0.99  --bmc1_verbose                          false
% 2.05/0.99  --bmc1_dump_clauses_tptp                false
% 2.05/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.05/0.99  --bmc1_dump_file                        -
% 2.05/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.05/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.05/0.99  --bmc1_ucm_extend_mode                  1
% 2.05/0.99  --bmc1_ucm_init_mode                    2
% 2.05/0.99  --bmc1_ucm_cone_mode                    none
% 2.05/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.05/0.99  --bmc1_ucm_relax_model                  4
% 2.05/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.05/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.05/0.99  --bmc1_ucm_layered_model                none
% 2.05/0.99  --bmc1_ucm_max_lemma_size               10
% 2.05/0.99  
% 2.05/0.99  ------ AIG Options
% 2.05/0.99  
% 2.05/0.99  --aig_mode                              false
% 2.05/0.99  
% 2.05/0.99  ------ Instantiation Options
% 2.05/0.99  
% 2.05/0.99  --instantiation_flag                    true
% 2.05/0.99  --inst_sos_flag                         false
% 2.05/0.99  --inst_sos_phase                        true
% 2.05/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.05/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.05/0.99  --inst_lit_sel_side                     num_symb
% 2.05/0.99  --inst_solver_per_active                1400
% 2.05/0.99  --inst_solver_calls_frac                1.
% 2.05/0.99  --inst_passive_queue_type               priority_queues
% 2.05/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.05/0.99  --inst_passive_queues_freq              [25;2]
% 2.05/0.99  --inst_dismatching                      true
% 2.05/0.99  --inst_eager_unprocessed_to_passive     true
% 2.05/0.99  --inst_prop_sim_given                   true
% 2.05/0.99  --inst_prop_sim_new                     false
% 2.05/0.99  --inst_subs_new                         false
% 2.05/0.99  --inst_eq_res_simp                      false
% 2.05/0.99  --inst_subs_given                       false
% 2.05/0.99  --inst_orphan_elimination               true
% 2.05/0.99  --inst_learning_loop_flag               true
% 2.05/0.99  --inst_learning_start                   3000
% 2.05/0.99  --inst_learning_factor                  2
% 2.05/0.99  --inst_start_prop_sim_after_learn       3
% 2.05/0.99  --inst_sel_renew                        solver
% 2.05/0.99  --inst_lit_activity_flag                true
% 2.05/0.99  --inst_restr_to_given                   false
% 2.05/0.99  --inst_activity_threshold               500
% 2.05/0.99  --inst_out_proof                        true
% 2.05/0.99  
% 2.05/0.99  ------ Resolution Options
% 2.05/0.99  
% 2.05/0.99  --resolution_flag                       true
% 2.05/0.99  --res_lit_sel                           adaptive
% 2.05/0.99  --res_lit_sel_side                      none
% 2.05/0.99  --res_ordering                          kbo
% 2.05/0.99  --res_to_prop_solver                    active
% 2.05/0.99  --res_prop_simpl_new                    false
% 2.05/0.99  --res_prop_simpl_given                  true
% 2.05/0.99  --res_passive_queue_type                priority_queues
% 2.05/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.05/0.99  --res_passive_queues_freq               [15;5]
% 2.05/0.99  --res_forward_subs                      full
% 2.05/0.99  --res_backward_subs                     full
% 2.05/0.99  --res_forward_subs_resolution           true
% 2.05/0.99  --res_backward_subs_resolution          true
% 2.05/0.99  --res_orphan_elimination                true
% 2.05/0.99  --res_time_limit                        2.
% 2.05/0.99  --res_out_proof                         true
% 2.05/0.99  
% 2.05/0.99  ------ Superposition Options
% 2.05/0.99  
% 2.05/0.99  --superposition_flag                    true
% 2.05/0.99  --sup_passive_queue_type                priority_queues
% 2.05/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.05/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.05/0.99  --demod_completeness_check              fast
% 2.05/0.99  --demod_use_ground                      true
% 2.05/0.99  --sup_to_prop_solver                    passive
% 2.05/0.99  --sup_prop_simpl_new                    true
% 2.05/0.99  --sup_prop_simpl_given                  true
% 2.05/0.99  --sup_fun_splitting                     false
% 2.05/0.99  --sup_smt_interval                      50000
% 2.05/0.99  
% 2.05/0.99  ------ Superposition Simplification Setup
% 2.05/0.99  
% 2.05/0.99  --sup_indices_passive                   []
% 2.05/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.05/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.99  --sup_full_bw                           [BwDemod]
% 2.05/0.99  --sup_immed_triv                        [TrivRules]
% 2.05/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.05/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.99  --sup_immed_bw_main                     []
% 2.05/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.05/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.99  
% 2.05/0.99  ------ Combination Options
% 2.05/0.99  
% 2.05/0.99  --comb_res_mult                         3
% 2.05/0.99  --comb_sup_mult                         2
% 2.05/0.99  --comb_inst_mult                        10
% 2.05/0.99  
% 2.05/0.99  ------ Debug Options
% 2.05/0.99  
% 2.05/0.99  --dbg_backtrace                         false
% 2.05/0.99  --dbg_dump_prop_clauses                 false
% 2.05/0.99  --dbg_dump_prop_clauses_file            -
% 2.05/0.99  --dbg_out_stat                          false
% 2.05/0.99  ------ Parsing...
% 2.05/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.05/0.99  
% 2.05/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.05/0.99  
% 2.05/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.05/0.99  
% 2.05/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.05/0.99  ------ Proving...
% 2.05/0.99  ------ Problem Properties 
% 2.05/0.99  
% 2.05/0.99  
% 2.05/0.99  clauses                                 18
% 2.05/0.99  conjectures                             1
% 2.05/0.99  EPR                                     1
% 2.05/0.99  Horn                                    14
% 2.05/0.99  unary                                   5
% 2.05/0.99  binary                                  5
% 2.05/0.99  lits                                    41
% 2.05/0.99  lits eq                                 10
% 2.05/0.99  fd_pure                                 0
% 2.05/0.99  fd_pseudo                               0
% 2.05/0.99  fd_cond                                 0
% 2.05/0.99  fd_pseudo_cond                          1
% 2.05/0.99  AC symbols                              0
% 2.05/0.99  
% 2.05/0.99  ------ Schedule dynamic 5 is on 
% 2.05/0.99  
% 2.05/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.05/0.99  
% 2.05/0.99  
% 2.05/0.99  ------ 
% 2.05/0.99  Current options:
% 2.05/0.99  ------ 
% 2.05/0.99  
% 2.05/0.99  ------ Input Options
% 2.05/0.99  
% 2.05/0.99  --out_options                           all
% 2.05/0.99  --tptp_safe_out                         true
% 2.05/0.99  --problem_path                          ""
% 2.05/0.99  --include_path                          ""
% 2.05/0.99  --clausifier                            res/vclausify_rel
% 2.05/0.99  --clausifier_options                    --mode clausify
% 2.05/0.99  --stdin                                 false
% 2.05/0.99  --stats_out                             all
% 2.05/0.99  
% 2.05/0.99  ------ General Options
% 2.05/0.99  
% 2.05/0.99  --fof                                   false
% 2.05/0.99  --time_out_real                         305.
% 2.05/0.99  --time_out_virtual                      -1.
% 2.05/0.99  --symbol_type_check                     false
% 2.05/0.99  --clausify_out                          false
% 2.05/0.99  --sig_cnt_out                           false
% 2.05/0.99  --trig_cnt_out                          false
% 2.05/0.99  --trig_cnt_out_tolerance                1.
% 2.05/0.99  --trig_cnt_out_sk_spl                   false
% 2.05/0.99  --abstr_cl_out                          false
% 2.05/0.99  
% 2.05/0.99  ------ Global Options
% 2.05/0.99  
% 2.05/0.99  --schedule                              default
% 2.05/0.99  --add_important_lit                     false
% 2.05/0.99  --prop_solver_per_cl                    1000
% 2.05/0.99  --min_unsat_core                        false
% 2.05/0.99  --soft_assumptions                      false
% 2.05/0.99  --soft_lemma_size                       3
% 2.05/0.99  --prop_impl_unit_size                   0
% 2.05/0.99  --prop_impl_unit                        []
% 2.05/0.99  --share_sel_clauses                     true
% 2.05/0.99  --reset_solvers                         false
% 2.05/0.99  --bc_imp_inh                            [conj_cone]
% 2.05/0.99  --conj_cone_tolerance                   3.
% 2.05/0.99  --extra_neg_conj                        none
% 2.05/0.99  --large_theory_mode                     true
% 2.05/0.99  --prolific_symb_bound                   200
% 2.05/0.99  --lt_threshold                          2000
% 2.05/0.99  --clause_weak_htbl                      true
% 2.05/0.99  --gc_record_bc_elim                     false
% 2.05/0.99  
% 2.05/0.99  ------ Preprocessing Options
% 2.05/0.99  
% 2.05/0.99  --preprocessing_flag                    true
% 2.05/0.99  --time_out_prep_mult                    0.1
% 2.05/0.99  --splitting_mode                        input
% 2.05/0.99  --splitting_grd                         true
% 2.05/0.99  --splitting_cvd                         false
% 2.05/0.99  --splitting_cvd_svl                     false
% 2.05/0.99  --splitting_nvd                         32
% 2.05/0.99  --sub_typing                            true
% 2.05/0.99  --prep_gs_sim                           true
% 2.05/0.99  --prep_unflatten                        true
% 2.05/0.99  --prep_res_sim                          true
% 2.05/0.99  --prep_upred                            true
% 2.05/0.99  --prep_sem_filter                       exhaustive
% 2.05/0.99  --prep_sem_filter_out                   false
% 2.05/0.99  --pred_elim                             true
% 2.05/0.99  --res_sim_input                         true
% 2.05/0.99  --eq_ax_congr_red                       true
% 2.05/0.99  --pure_diseq_elim                       true
% 2.05/0.99  --brand_transform                       false
% 2.05/0.99  --non_eq_to_eq                          false
% 2.05/0.99  --prep_def_merge                        true
% 2.05/0.99  --prep_def_merge_prop_impl              false
% 2.05/0.99  --prep_def_merge_mbd                    true
% 2.05/0.99  --prep_def_merge_tr_red                 false
% 2.05/0.99  --prep_def_merge_tr_cl                  false
% 2.05/0.99  --smt_preprocessing                     true
% 2.05/0.99  --smt_ac_axioms                         fast
% 2.05/0.99  --preprocessed_out                      false
% 2.05/0.99  --preprocessed_stats                    false
% 2.05/0.99  
% 2.05/0.99  ------ Abstraction refinement Options
% 2.05/0.99  
% 2.05/0.99  --abstr_ref                             []
% 2.05/0.99  --abstr_ref_prep                        false
% 2.05/0.99  --abstr_ref_until_sat                   false
% 2.05/0.99  --abstr_ref_sig_restrict                funpre
% 2.05/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.05/0.99  --abstr_ref_under                       []
% 2.05/0.99  
% 2.05/0.99  ------ SAT Options
% 2.05/0.99  
% 2.05/0.99  --sat_mode                              false
% 2.05/0.99  --sat_fm_restart_options                ""
% 2.05/0.99  --sat_gr_def                            false
% 2.05/0.99  --sat_epr_types                         true
% 2.05/0.99  --sat_non_cyclic_types                  false
% 2.05/0.99  --sat_finite_models                     false
% 2.05/0.99  --sat_fm_lemmas                         false
% 2.05/0.99  --sat_fm_prep                           false
% 2.05/0.99  --sat_fm_uc_incr                        true
% 2.05/0.99  --sat_out_model                         small
% 2.05/0.99  --sat_out_clauses                       false
% 2.05/0.99  
% 2.05/0.99  ------ QBF Options
% 2.05/0.99  
% 2.05/0.99  --qbf_mode                              false
% 2.05/0.99  --qbf_elim_univ                         false
% 2.05/0.99  --qbf_dom_inst                          none
% 2.05/0.99  --qbf_dom_pre_inst                      false
% 2.05/0.99  --qbf_sk_in                             false
% 2.05/0.99  --qbf_pred_elim                         true
% 2.05/0.99  --qbf_split                             512
% 2.05/0.99  
% 2.05/0.99  ------ BMC1 Options
% 2.05/0.99  
% 2.05/0.99  --bmc1_incremental                      false
% 2.05/0.99  --bmc1_axioms                           reachable_all
% 2.05/0.99  --bmc1_min_bound                        0
% 2.05/0.99  --bmc1_max_bound                        -1
% 2.05/0.99  --bmc1_max_bound_default                -1
% 2.05/0.99  --bmc1_symbol_reachability              true
% 2.05/0.99  --bmc1_property_lemmas                  false
% 2.05/0.99  --bmc1_k_induction                      false
% 2.05/0.99  --bmc1_non_equiv_states                 false
% 2.05/0.99  --bmc1_deadlock                         false
% 2.05/0.99  --bmc1_ucm                              false
% 2.05/0.99  --bmc1_add_unsat_core                   none
% 2.05/0.99  --bmc1_unsat_core_children              false
% 2.05/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.05/0.99  --bmc1_out_stat                         full
% 2.05/0.99  --bmc1_ground_init                      false
% 2.05/0.99  --bmc1_pre_inst_next_state              false
% 2.05/0.99  --bmc1_pre_inst_state                   false
% 2.05/0.99  --bmc1_pre_inst_reach_state             false
% 2.05/0.99  --bmc1_out_unsat_core                   false
% 2.05/0.99  --bmc1_aig_witness_out                  false
% 2.05/0.99  --bmc1_verbose                          false
% 2.05/0.99  --bmc1_dump_clauses_tptp                false
% 2.05/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.05/0.99  --bmc1_dump_file                        -
% 2.05/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.05/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.05/0.99  --bmc1_ucm_extend_mode                  1
% 2.05/0.99  --bmc1_ucm_init_mode                    2
% 2.05/0.99  --bmc1_ucm_cone_mode                    none
% 2.05/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.05/0.99  --bmc1_ucm_relax_model                  4
% 2.05/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.05/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.05/0.99  --bmc1_ucm_layered_model                none
% 2.05/0.99  --bmc1_ucm_max_lemma_size               10
% 2.05/0.99  
% 2.05/0.99  ------ AIG Options
% 2.05/0.99  
% 2.05/0.99  --aig_mode                              false
% 2.05/0.99  
% 2.05/0.99  ------ Instantiation Options
% 2.05/0.99  
% 2.05/0.99  --instantiation_flag                    true
% 2.05/0.99  --inst_sos_flag                         false
% 2.05/0.99  --inst_sos_phase                        true
% 2.05/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.05/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.05/0.99  --inst_lit_sel_side                     none
% 2.05/0.99  --inst_solver_per_active                1400
% 2.05/0.99  --inst_solver_calls_frac                1.
% 2.05/0.99  --inst_passive_queue_type               priority_queues
% 2.05/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.05/0.99  --inst_passive_queues_freq              [25;2]
% 2.05/0.99  --inst_dismatching                      true
% 2.05/0.99  --inst_eager_unprocessed_to_passive     true
% 2.05/0.99  --inst_prop_sim_given                   true
% 2.05/0.99  --inst_prop_sim_new                     false
% 2.05/0.99  --inst_subs_new                         false
% 2.05/0.99  --inst_eq_res_simp                      false
% 2.05/0.99  --inst_subs_given                       false
% 2.05/0.99  --inst_orphan_elimination               true
% 2.05/0.99  --inst_learning_loop_flag               true
% 2.05/0.99  --inst_learning_start                   3000
% 2.05/0.99  --inst_learning_factor                  2
% 2.05/0.99  --inst_start_prop_sim_after_learn       3
% 2.05/0.99  --inst_sel_renew                        solver
% 2.05/0.99  --inst_lit_activity_flag                true
% 2.05/0.99  --inst_restr_to_given                   false
% 2.05/0.99  --inst_activity_threshold               500
% 2.05/0.99  --inst_out_proof                        true
% 2.05/0.99  
% 2.05/0.99  ------ Resolution Options
% 2.05/0.99  
% 2.05/0.99  --resolution_flag                       false
% 2.05/0.99  --res_lit_sel                           adaptive
% 2.05/0.99  --res_lit_sel_side                      none
% 2.05/0.99  --res_ordering                          kbo
% 2.05/0.99  --res_to_prop_solver                    active
% 2.05/0.99  --res_prop_simpl_new                    false
% 2.05/0.99  --res_prop_simpl_given                  true
% 2.05/0.99  --res_passive_queue_type                priority_queues
% 2.05/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.05/0.99  --res_passive_queues_freq               [15;5]
% 2.05/0.99  --res_forward_subs                      full
% 2.05/0.99  --res_backward_subs                     full
% 2.05/0.99  --res_forward_subs_resolution           true
% 2.05/0.99  --res_backward_subs_resolution          true
% 2.05/0.99  --res_orphan_elimination                true
% 2.05/0.99  --res_time_limit                        2.
% 2.05/0.99  --res_out_proof                         true
% 2.05/0.99  
% 2.05/0.99  ------ Superposition Options
% 2.05/0.99  
% 2.05/0.99  --superposition_flag                    true
% 2.05/0.99  --sup_passive_queue_type                priority_queues
% 2.05/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.05/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.05/0.99  --demod_completeness_check              fast
% 2.05/0.99  --demod_use_ground                      true
% 2.05/0.99  --sup_to_prop_solver                    passive
% 2.05/0.99  --sup_prop_simpl_new                    true
% 2.05/0.99  --sup_prop_simpl_given                  true
% 2.05/0.99  --sup_fun_splitting                     false
% 2.05/0.99  --sup_smt_interval                      50000
% 2.05/0.99  
% 2.05/0.99  ------ Superposition Simplification Setup
% 2.05/0.99  
% 2.05/0.99  --sup_indices_passive                   []
% 2.05/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.05/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.99  --sup_full_bw                           [BwDemod]
% 2.05/0.99  --sup_immed_triv                        [TrivRules]
% 2.05/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.05/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.99  --sup_immed_bw_main                     []
% 2.05/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.05/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.99  
% 2.05/0.99  ------ Combination Options
% 2.05/0.99  
% 2.05/0.99  --comb_res_mult                         3
% 2.05/0.99  --comb_sup_mult                         2
% 2.05/0.99  --comb_inst_mult                        10
% 2.05/0.99  
% 2.05/0.99  ------ Debug Options
% 2.05/0.99  
% 2.05/0.99  --dbg_backtrace                         false
% 2.05/0.99  --dbg_dump_prop_clauses                 false
% 2.05/0.99  --dbg_dump_prop_clauses_file            -
% 2.05/0.99  --dbg_out_stat                          false
% 2.05/0.99  
% 2.05/0.99  
% 2.05/0.99  
% 2.05/0.99  
% 2.05/0.99  ------ Proving...
% 2.05/0.99  
% 2.05/0.99  
% 2.05/0.99  % SZS status Theorem for theBenchmark.p
% 2.05/0.99  
% 2.05/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.05/0.99  
% 2.05/0.99  fof(f12,axiom,(
% 2.05/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f29,plain,(
% 2.05/0.99    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.05/0.99    inference(ennf_transformation,[],[f12])).
% 2.05/0.99  
% 2.05/0.99  fof(f43,plain,(
% 2.05/0.99    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.05/0.99    inference(nnf_transformation,[],[f29])).
% 2.05/0.99  
% 2.05/0.99  fof(f70,plain,(
% 2.05/0.99    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.05/0.99    inference(cnf_transformation,[],[f43])).
% 2.05/0.99  
% 2.05/0.99  fof(f16,conjecture,(
% 2.05/0.99    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f17,negated_conjecture,(
% 2.05/0.99    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 2.05/0.99    inference(negated_conjecture,[],[f16])).
% 2.05/0.99  
% 2.05/0.99  fof(f36,plain,(
% 2.05/0.99    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.05/0.99    inference(ennf_transformation,[],[f17])).
% 2.05/0.99  
% 2.05/0.99  fof(f37,plain,(
% 2.05/0.99    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.05/0.99    inference(flattening,[],[f36])).
% 2.05/0.99  
% 2.05/0.99  fof(f49,plain,(
% 2.05/0.99    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.05/0.99    inference(nnf_transformation,[],[f37])).
% 2.05/0.99  
% 2.05/0.99  fof(f50,plain,(
% 2.05/0.99    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.05/0.99    inference(flattening,[],[f49])).
% 2.05/0.99  
% 2.05/0.99  fof(f52,plain,(
% 2.05/0.99    ( ! [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_subset_1(sK3,u1_struct_0(X0)) | ~v3_tex_2(sK3,X0)) & (~v1_subset_1(sK3,u1_struct_0(X0)) | v3_tex_2(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.05/0.99    introduced(choice_axiom,[])).
% 2.05/0.99  
% 2.05/0.99  fof(f51,plain,(
% 2.05/0.99    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK2)) | ~v3_tex_2(X1,sK2)) & (~v1_subset_1(X1,u1_struct_0(sK2)) | v3_tex_2(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v1_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.05/0.99    introduced(choice_axiom,[])).
% 2.05/0.99  
% 2.05/0.99  fof(f53,plain,(
% 2.05/0.99    ((v1_subset_1(sK3,u1_struct_0(sK2)) | ~v3_tex_2(sK3,sK2)) & (~v1_subset_1(sK3,u1_struct_0(sK2)) | v3_tex_2(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v1_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.05/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f50,f52,f51])).
% 2.05/0.99  
% 2.05/0.99  fof(f84,plain,(
% 2.05/0.99    ~v1_subset_1(sK3,u1_struct_0(sK2)) | v3_tex_2(sK3,sK2)),
% 2.05/0.99    inference(cnf_transformation,[],[f53])).
% 2.05/0.99  
% 2.05/0.99  fof(f83,plain,(
% 2.05/0.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 2.05/0.99    inference(cnf_transformation,[],[f53])).
% 2.05/0.99  
% 2.05/0.99  fof(f7,axiom,(
% 2.05/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f21,plain,(
% 2.05/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.05/0.99    inference(ennf_transformation,[],[f7])).
% 2.05/0.99  
% 2.05/0.99  fof(f62,plain,(
% 2.05/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.05/0.99    inference(cnf_transformation,[],[f21])).
% 2.05/0.99  
% 2.05/0.99  fof(f6,axiom,(
% 2.05/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f20,plain,(
% 2.05/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.05/0.99    inference(ennf_transformation,[],[f6])).
% 2.05/0.99  
% 2.05/0.99  fof(f61,plain,(
% 2.05/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.05/0.99    inference(cnf_transformation,[],[f20])).
% 2.05/0.99  
% 2.05/0.99  fof(f82,plain,(
% 2.05/0.99    l1_pre_topc(sK2)),
% 2.05/0.99    inference(cnf_transformation,[],[f53])).
% 2.05/0.99  
% 2.05/0.99  fof(f13,axiom,(
% 2.05/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f30,plain,(
% 2.05/0.99    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.99    inference(ennf_transformation,[],[f13])).
% 2.05/0.99  
% 2.05/0.99  fof(f31,plain,(
% 2.05/0.99    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.99    inference(flattening,[],[f30])).
% 2.05/0.99  
% 2.05/0.99  fof(f44,plain,(
% 2.05/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.99    inference(nnf_transformation,[],[f31])).
% 2.05/0.99  
% 2.05/0.99  fof(f45,plain,(
% 2.05/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.99    inference(flattening,[],[f44])).
% 2.05/0.99  
% 2.05/0.99  fof(f46,plain,(
% 2.05/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.99    inference(rectify,[],[f45])).
% 2.05/0.99  
% 2.05/0.99  fof(f47,plain,(
% 2.05/0.99    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK1(X0,X1) != X1 & r1_tarski(X1,sK1(X0,X1)) & v2_tex_2(sK1(X0,X1),X0) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.05/0.99    introduced(choice_axiom,[])).
% 2.05/0.99  
% 2.05/0.99  fof(f48,plain,(
% 2.05/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK1(X0,X1) != X1 & r1_tarski(X1,sK1(X0,X1)) & v2_tex_2(sK1(X0,X1),X0) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).
% 2.05/0.99  
% 2.05/0.99  fof(f73,plain,(
% 2.05/0.99    ( ! [X0,X1] : (v3_tex_2(X1,X0) | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.05/0.99    inference(cnf_transformation,[],[f48])).
% 2.05/0.99  
% 2.05/0.99  fof(f14,axiom,(
% 2.05/0.99    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f32,plain,(
% 2.05/0.99    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.05/0.99    inference(ennf_transformation,[],[f14])).
% 2.05/0.99  
% 2.05/0.99  fof(f33,plain,(
% 2.05/0.99    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.99    inference(flattening,[],[f32])).
% 2.05/0.99  
% 2.05/0.99  fof(f77,plain,(
% 2.05/0.99    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.05/0.99    inference(cnf_transformation,[],[f33])).
% 2.05/0.99  
% 2.05/0.99  fof(f81,plain,(
% 2.05/0.99    v1_tdlat_3(sK2)),
% 2.05/0.99    inference(cnf_transformation,[],[f53])).
% 2.05/0.99  
% 2.05/0.99  fof(f79,plain,(
% 2.05/0.99    ~v2_struct_0(sK2)),
% 2.05/0.99    inference(cnf_transformation,[],[f53])).
% 2.05/0.99  
% 2.05/0.99  fof(f80,plain,(
% 2.05/0.99    v2_pre_topc(sK2)),
% 2.05/0.99    inference(cnf_transformation,[],[f53])).
% 2.05/0.99  
% 2.05/0.99  fof(f72,plain,(
% 2.05/0.99    ( ! [X0,X3,X1] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.05/0.99    inference(cnf_transformation,[],[f48])).
% 2.05/0.99  
% 2.05/0.99  fof(f3,axiom,(
% 2.05/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f58,plain,(
% 2.05/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.05/0.99    inference(cnf_transformation,[],[f3])).
% 2.05/0.99  
% 2.05/0.99  fof(f2,axiom,(
% 2.05/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f57,plain,(
% 2.05/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.05/0.99    inference(cnf_transformation,[],[f2])).
% 2.05/0.99  
% 2.05/0.99  fof(f5,axiom,(
% 2.05/0.99    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f60,plain,(
% 2.05/0.99    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 2.05/0.99    inference(cnf_transformation,[],[f5])).
% 2.05/0.99  
% 2.05/0.99  fof(f85,plain,(
% 2.05/0.99    v1_subset_1(sK3,u1_struct_0(sK2)) | ~v3_tex_2(sK3,sK2)),
% 2.05/0.99    inference(cnf_transformation,[],[f53])).
% 2.05/0.99  
% 2.05/0.99  fof(f1,axiom,(
% 2.05/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f18,plain,(
% 2.05/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.05/0.99    inference(ennf_transformation,[],[f1])).
% 2.05/0.99  
% 2.05/0.99  fof(f38,plain,(
% 2.05/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.05/0.99    inference(nnf_transformation,[],[f18])).
% 2.05/0.99  
% 2.05/0.99  fof(f39,plain,(
% 2.05/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.05/0.99    inference(rectify,[],[f38])).
% 2.05/0.99  
% 2.05/0.99  fof(f40,plain,(
% 2.05/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.05/0.99    introduced(choice_axiom,[])).
% 2.05/0.99  
% 2.05/0.99  fof(f41,plain,(
% 2.05/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.05/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 2.05/0.99  
% 2.05/0.99  fof(f55,plain,(
% 2.05/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.05/0.99    inference(cnf_transformation,[],[f41])).
% 2.05/0.99  
% 2.05/0.99  fof(f4,axiom,(
% 2.05/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f19,plain,(
% 2.05/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.05/0.99    inference(ennf_transformation,[],[f4])).
% 2.05/0.99  
% 2.05/0.99  fof(f59,plain,(
% 2.05/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.05/0.99    inference(cnf_transformation,[],[f19])).
% 2.05/0.99  
% 2.05/0.99  fof(f56,plain,(
% 2.05/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.05/0.99    inference(cnf_transformation,[],[f41])).
% 2.05/0.99  
% 2.05/0.99  fof(f9,axiom,(
% 2.05/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f24,plain,(
% 2.05/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.99    inference(ennf_transformation,[],[f9])).
% 2.05/0.99  
% 2.05/0.99  fof(f25,plain,(
% 2.05/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.99    inference(flattening,[],[f24])).
% 2.05/0.99  
% 2.05/0.99  fof(f64,plain,(
% 2.05/0.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.05/0.99    inference(cnf_transformation,[],[f25])).
% 2.05/0.99  
% 2.05/0.99  fof(f8,axiom,(
% 2.05/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f22,plain,(
% 2.05/0.99    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.05/0.99    inference(ennf_transformation,[],[f8])).
% 2.05/0.99  
% 2.05/0.99  fof(f23,plain,(
% 2.05/0.99    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.05/0.99    inference(flattening,[],[f22])).
% 2.05/0.99  
% 2.05/0.99  fof(f63,plain,(
% 2.05/0.99    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.05/0.99    inference(cnf_transformation,[],[f23])).
% 2.05/0.99  
% 2.05/0.99  fof(f10,axiom,(
% 2.05/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f26,plain,(
% 2.05/0.99    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.99    inference(ennf_transformation,[],[f10])).
% 2.05/0.99  
% 2.05/0.99  fof(f42,plain,(
% 2.05/0.99    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.99    inference(nnf_transformation,[],[f26])).
% 2.05/0.99  
% 2.05/0.99  fof(f67,plain,(
% 2.05/0.99    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.05/0.99    inference(cnf_transformation,[],[f42])).
% 2.05/0.99  
% 2.05/0.99  fof(f15,axiom,(
% 2.05/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f34,plain,(
% 2.05/0.99    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.05/0.99    inference(ennf_transformation,[],[f15])).
% 2.05/0.99  
% 2.05/0.99  fof(f35,plain,(
% 2.05/0.99    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.99    inference(flattening,[],[f34])).
% 2.05/0.99  
% 2.05/0.99  fof(f78,plain,(
% 2.05/0.99    ( ! [X0,X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.05/0.99    inference(cnf_transformation,[],[f35])).
% 2.05/0.99  
% 2.05/0.99  cnf(c_15,plain,
% 2.05/0.99      ( v1_subset_1(X0,X1)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.05/0.99      | X0 = X1 ),
% 2.05/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_26,negated_conjecture,
% 2.05/0.99      ( v3_tex_2(sK3,sK2) | ~ v1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.05/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_237,plain,
% 2.05/0.99      ( v3_tex_2(sK3,sK2) | ~ v1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.05/0.99      inference(prop_impl,[status(thm)],[c_26]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_579,plain,
% 2.05/0.99      ( v3_tex_2(sK3,sK2)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.05/0.99      | X1 = X0
% 2.05/0.99      | u1_struct_0(sK2) != X1
% 2.05/0.99      | sK3 != X0 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_237]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_580,plain,
% 2.05/0.99      ( v3_tex_2(sK3,sK2)
% 2.05/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.99      | u1_struct_0(sK2) = sK3 ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_579]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_27,negated_conjecture,
% 2.05/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.05/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_582,plain,
% 2.05/0.99      ( v3_tex_2(sK3,sK2) | u1_struct_0(sK2) = sK3 ),
% 2.05/0.99      inference(global_propositional_subsumption,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_580,c_27]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1921,plain,
% 2.05/0.99      ( u1_struct_0(sK2) = sK3 | v3_tex_2(sK3,sK2) = iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_582]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_8,plain,
% 2.05/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.05/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_7,plain,
% 2.05/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.05/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_410,plain,
% 2.05/0.99      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.05/0.99      inference(resolution,[status(thm)],[c_8,c_7]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_28,negated_conjecture,
% 2.05/0.99      ( l1_pre_topc(sK2) ),
% 2.05/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_617,plain,
% 2.05/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK2 != X0 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_410,c_28]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_618,plain,
% 2.05/0.99      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_617]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1943,plain,
% 2.05/0.99      ( k2_struct_0(sK2) = sK3 | v3_tex_2(sK3,sK2) = iProver_top ),
% 2.05/0.99      inference(demodulation,[status(thm)],[c_1921,c_618]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1925,plain,
% 2.05/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1937,plain,
% 2.05/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
% 2.05/0.99      inference(light_normalisation,[status(thm)],[c_1925,c_618]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_20,plain,
% 2.05/0.99      ( ~ v2_tex_2(X0,X1)
% 2.05/0.99      | v3_tex_2(X0,X1)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.99      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.99      | ~ l1_pre_topc(X1) ),
% 2.05/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_658,plain,
% 2.05/0.99      ( ~ v2_tex_2(X0,X1)
% 2.05/0.99      | v3_tex_2(X0,X1)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.99      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.99      | sK2 != X1 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_28]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_659,plain,
% 2.05/0.99      ( ~ v2_tex_2(X0,sK2)
% 2.05/0.99      | v3_tex_2(X0,sK2)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.99      | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_658]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_23,plain,
% 2.05/0.99      ( v2_tex_2(X0,X1)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.99      | v2_struct_0(X1)
% 2.05/0.99      | ~ v1_tdlat_3(X1)
% 2.05/0.99      | ~ v2_pre_topc(X1)
% 2.05/0.99      | ~ l1_pre_topc(X1) ),
% 2.05/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_29,negated_conjecture,
% 2.05/0.99      ( v1_tdlat_3(sK2) ),
% 2.05/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_426,plain,
% 2.05/0.99      ( v2_tex_2(X0,X1)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.99      | v2_struct_0(X1)
% 2.05/0.99      | ~ v2_pre_topc(X1)
% 2.05/0.99      | ~ l1_pre_topc(X1)
% 2.05/0.99      | sK2 != X1 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_29]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_427,plain,
% 2.05/0.99      ( v2_tex_2(X0,sK2)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.99      | v2_struct_0(sK2)
% 2.05/0.99      | ~ v2_pre_topc(sK2)
% 2.05/0.99      | ~ l1_pre_topc(sK2) ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_426]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_31,negated_conjecture,
% 2.05/0.99      ( ~ v2_struct_0(sK2) ),
% 2.05/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_30,negated_conjecture,
% 2.05/0.99      ( v2_pre_topc(sK2) ),
% 2.05/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_431,plain,
% 2.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.99      | v2_tex_2(X0,sK2) ),
% 2.05/0.99      inference(global_propositional_subsumption,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_427,c_31,c_30,c_28]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_432,plain,
% 2.05/0.99      ( v2_tex_2(X0,sK2)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.05/0.99      inference(renaming,[status(thm)],[c_431]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_663,plain,
% 2.05/0.99      ( v3_tex_2(X0,sK2)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.99      | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.05/0.99      inference(global_propositional_subsumption,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_659,c_31,c_30,c_28,c_427]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1918,plain,
% 2.05/0.99      ( v3_tex_2(X0,sK2) = iProver_top
% 2.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.05/0.99      | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_663]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2001,plain,
% 2.05/0.99      ( v3_tex_2(X0,sK2) = iProver_top
% 2.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.05/0.99      | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
% 2.05/0.99      inference(light_normalisation,[status(thm)],[c_1918,c_618]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_21,plain,
% 2.05/0.99      ( ~ v2_tex_2(X0,X1)
% 2.05/0.99      | ~ v3_tex_2(X2,X1)
% 2.05/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.99      | ~ r1_tarski(X2,X0)
% 2.05/0.99      | ~ l1_pre_topc(X1)
% 2.05/0.99      | X0 = X2 ),
% 2.05/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_631,plain,
% 2.05/0.99      ( ~ v2_tex_2(X0,X1)
% 2.05/0.99      | ~ v3_tex_2(X2,X1)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.99      | ~ r1_tarski(X2,X0)
% 2.05/0.99      | X2 = X0
% 2.05/0.99      | sK2 != X1 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_28]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_632,plain,
% 2.05/0.99      ( ~ v2_tex_2(X0,sK2)
% 2.05/0.99      | ~ v3_tex_2(X1,sK2)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.99      | ~ r1_tarski(X1,X0)
% 2.05/0.99      | X1 = X0 ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_631]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_636,plain,
% 2.05/0.99      ( ~ v3_tex_2(X1,sK2)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.99      | ~ r1_tarski(X1,X0)
% 2.05/0.99      | X1 = X0 ),
% 2.05/0.99      inference(global_propositional_subsumption,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_632,c_31,c_30,c_28,c_427]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_637,plain,
% 2.05/0.99      ( ~ v3_tex_2(X0,sK2)
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.99      | ~ r1_tarski(X0,X1)
% 2.05/0.99      | X0 = X1 ),
% 2.05/0.99      inference(renaming,[status(thm)],[c_636]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1919,plain,
% 2.05/0.99      ( X0 = X1
% 2.05/0.99      | v3_tex_2(X0,sK2) != iProver_top
% 2.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.05/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.05/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_637]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2008,plain,
% 2.05/0.99      ( X0 = X1
% 2.05/0.99      | v3_tex_2(X1,sK2) != iProver_top
% 2.05/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.05/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 2.05/0.99      inference(light_normalisation,[status(thm)],[c_1919,c_618]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2203,plain,
% 2.05/0.99      ( sK1(sK2,X0) = X1
% 2.05/0.99      | v3_tex_2(X1,sK2) != iProver_top
% 2.05/0.99      | v3_tex_2(X0,sK2) = iProver_top
% 2.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.05/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.05/0.99      | r1_tarski(X1,sK1(sK2,X0)) != iProver_top ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_2001,c_2008]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_3048,plain,
% 2.05/0.99      ( sK1(sK2,sK3) = X0
% 2.05/0.99      | v3_tex_2(X0,sK2) != iProver_top
% 2.05/0.99      | v3_tex_2(sK3,sK2) = iProver_top
% 2.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.05/0.99      | r1_tarski(X0,sK1(sK2,sK3)) != iProver_top ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_1937,c_2203]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_4,plain,
% 2.05/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.05/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1927,plain,
% 2.05/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_3,plain,
% 2.05/0.99      ( k2_subset_1(X0) = X0 ),
% 2.05/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1940,plain,
% 2.05/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.05/0.99      inference(light_normalisation,[status(thm)],[c_1927,c_3]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2370,plain,
% 2.05/0.99      ( k2_struct_0(sK2) = X0
% 2.05/0.99      | v3_tex_2(X0,sK2) != iProver_top
% 2.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.05/0.99      | r1_tarski(X0,k2_struct_0(sK2)) != iProver_top ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_1940,c_2008]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2559,plain,
% 2.05/0.99      ( k2_struct_0(sK2) = sK3
% 2.05/0.99      | v3_tex_2(sK3,sK2) != iProver_top
% 2.05/0.99      | r1_tarski(sK3,k2_struct_0(sK2)) != iProver_top ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_1937,c_2370]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_6,plain,
% 2.05/0.99      ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
% 2.05/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_25,negated_conjecture,
% 2.05/0.99      ( ~ v3_tex_2(sK3,sK2) | v1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.05/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_239,plain,
% 2.05/0.99      ( ~ v3_tex_2(sK3,sK2) | v1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.05/0.99      inference(prop_impl,[status(thm)],[c_25]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_567,plain,
% 2.05/0.99      ( ~ v3_tex_2(sK3,sK2)
% 2.05/0.99      | u1_struct_0(sK2) != X0
% 2.05/0.99      | k2_subset_1(X0) != sK3 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_239]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_568,plain,
% 2.05/0.99      ( ~ v3_tex_2(sK3,sK2) | k2_subset_1(u1_struct_0(sK2)) != sK3 ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_567]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1922,plain,
% 2.05/0.99      ( k2_subset_1(u1_struct_0(sK2)) != sK3
% 2.05/0.99      | v3_tex_2(sK3,sK2) != iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_568]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1948,plain,
% 2.05/0.99      ( k2_subset_1(k2_struct_0(sK2)) != sK3
% 2.05/0.99      | v3_tex_2(sK3,sK2) != iProver_top ),
% 2.05/0.99      inference(light_normalisation,[status(thm)],[c_1922,c_618]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1949,plain,
% 2.05/0.99      ( k2_struct_0(sK2) != sK3 | v3_tex_2(sK3,sK2) != iProver_top ),
% 2.05/0.99      inference(demodulation,[status(thm)],[c_1948,c_3]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2623,plain,
% 2.05/0.99      ( v3_tex_2(sK3,sK2) != iProver_top
% 2.05/0.99      | r1_tarski(sK3,k2_struct_0(sK2)) != iProver_top ),
% 2.05/0.99      inference(global_propositional_subsumption,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_2559,c_1949]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1,plain,
% 2.05/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.05/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1929,plain,
% 2.05/0.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.05/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_5,plain,
% 2.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.05/0.99      | ~ r2_hidden(X2,X0)
% 2.05/0.99      | r2_hidden(X2,X1) ),
% 2.05/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1926,plain,
% 2.05/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.05/0.99      | r2_hidden(X2,X0) != iProver_top
% 2.05/0.99      | r2_hidden(X2,X1) = iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2304,plain,
% 2.05/0.99      ( r2_hidden(X0,k2_struct_0(sK2)) = iProver_top
% 2.05/0.99      | r2_hidden(X0,sK3) != iProver_top ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_1937,c_1926]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_0,plain,
% 2.05/0.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.05/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1930,plain,
% 2.05/0.99      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.05/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2696,plain,
% 2.05/0.99      ( r2_hidden(sK0(X0,k2_struct_0(sK2)),sK3) != iProver_top
% 2.05/0.99      | r1_tarski(X0,k2_struct_0(sK2)) = iProver_top ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_2304,c_1930]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2851,plain,
% 2.05/0.99      ( r1_tarski(sK3,k2_struct_0(sK2)) = iProver_top ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_1929,c_2696]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_3177,plain,
% 2.05/0.99      ( v3_tex_2(X0,sK2) != iProver_top
% 2.05/0.99      | sK1(sK2,sK3) = X0
% 2.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.05/0.99      | r1_tarski(X0,sK1(sK2,sK3)) != iProver_top ),
% 2.05/0.99      inference(global_propositional_subsumption,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_3048,c_2623,c_2851]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_3178,plain,
% 2.05/0.99      ( sK1(sK2,sK3) = X0
% 2.05/0.99      | v3_tex_2(X0,sK2) != iProver_top
% 2.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.05/0.99      | r1_tarski(X0,sK1(sK2,sK3)) != iProver_top ),
% 2.05/0.99      inference(renaming,[status(thm)],[c_3177]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_3188,plain,
% 2.05/0.99      ( sK1(sK2,sK3) = sK3
% 2.05/0.99      | v3_tex_2(sK3,sK2) != iProver_top
% 2.05/0.99      | r1_tarski(sK3,sK1(sK2,sK3)) != iProver_top ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_1937,c_3178]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_3218,plain,
% 2.05/0.99      ( v3_tex_2(sK3,sK2) != iProver_top ),
% 2.05/0.99      inference(global_propositional_subsumption,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_3188,c_2623,c_2851]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_3223,plain,
% 2.05/0.99      ( k2_struct_0(sK2) = sK3 ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_1943,c_3218]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_11,plain,
% 2.05/0.99      ( ~ v4_pre_topc(X0,X1)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.99      | ~ l1_pre_topc(X1)
% 2.05/0.99      | k2_pre_topc(X1,X0) = X0 ),
% 2.05/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_9,plain,
% 2.05/0.99      ( v4_pre_topc(k2_struct_0(X0),X0)
% 2.05/0.99      | ~ v2_pre_topc(X0)
% 2.05/0.99      | ~ l1_pre_topc(X0) ),
% 2.05/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_472,plain,
% 2.05/0.99      ( v4_pre_topc(k2_struct_0(X0),X0) | ~ l1_pre_topc(X0) | sK2 != X0 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_30]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_473,plain,
% 2.05/0.99      ( v4_pre_topc(k2_struct_0(sK2),sK2) | ~ l1_pre_topc(sK2) ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_472]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_83,plain,
% 2.05/0.99      ( v4_pre_topc(k2_struct_0(sK2),sK2)
% 2.05/0.99      | ~ v2_pre_topc(sK2)
% 2.05/0.99      | ~ l1_pre_topc(sK2) ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_475,plain,
% 2.05/0.99      ( v4_pre_topc(k2_struct_0(sK2),sK2) ),
% 2.05/0.99      inference(global_propositional_subsumption,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_473,c_30,c_28,c_83]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_510,plain,
% 2.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.99      | ~ l1_pre_topc(X1)
% 2.05/0.99      | k2_pre_topc(X1,X0) = X0
% 2.05/0.99      | k2_struct_0(sK2) != X0
% 2.05/0.99      | sK2 != X1 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_475]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_511,plain,
% 2.05/0.99      ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.99      | ~ l1_pre_topc(sK2)
% 2.05/0.99      | k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2) ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_510]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_513,plain,
% 2.05/0.99      ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.99      | k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2) ),
% 2.05/0.99      inference(global_propositional_subsumption,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_511,c_28]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1924,plain,
% 2.05/0.99      ( k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2)
% 2.05/0.99      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_513]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1962,plain,
% 2.05/0.99      ( k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2)
% 2.05/0.99      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 2.05/0.99      inference(light_normalisation,[status(thm)],[c_1924,c_618]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1965,plain,
% 2.05/0.99      ( k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2) ),
% 2.05/0.99      inference(forward_subsumption_resolution,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_1962,c_1940]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_12,plain,
% 2.05/0.99      ( v1_tops_1(X0,X1)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.99      | ~ l1_pre_topc(X1)
% 2.05/0.99      | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
% 2.05/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_24,plain,
% 2.05/0.99      ( ~ v2_tex_2(X0,X1)
% 2.05/0.99      | v3_tex_2(X0,X1)
% 2.05/0.99      | ~ v1_tops_1(X0,X1)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.99      | v2_struct_0(X1)
% 2.05/0.99      | ~ v2_pre_topc(X1)
% 2.05/0.99      | ~ l1_pre_topc(X1) ),
% 2.05/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_447,plain,
% 2.05/0.99      ( ~ v2_tex_2(X0,X1)
% 2.05/0.99      | v3_tex_2(X0,X1)
% 2.05/0.99      | ~ v1_tops_1(X0,X1)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.99      | ~ v2_pre_topc(X1)
% 2.05/0.99      | ~ l1_pre_topc(X1)
% 2.05/0.99      | sK2 != X1 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_31]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_448,plain,
% 2.05/0.99      ( ~ v2_tex_2(X0,sK2)
% 2.05/0.99      | v3_tex_2(X0,sK2)
% 2.05/0.99      | ~ v1_tops_1(X0,sK2)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.99      | ~ v2_pre_topc(sK2)
% 2.05/0.99      | ~ l1_pre_topc(sK2) ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_447]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_452,plain,
% 2.05/0.99      ( v3_tex_2(X0,sK2)
% 2.05/0.99      | ~ v1_tops_1(X0,sK2)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.05/0.99      inference(global_propositional_subsumption,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_448,c_31,c_30,c_28,c_427]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_530,plain,
% 2.05/0.99      ( v3_tex_2(X0,sK2)
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.99      | ~ l1_pre_topc(X2)
% 2.05/0.99      | X0 != X1
% 2.05/0.99      | k2_pre_topc(X2,X1) != k2_struct_0(X2)
% 2.05/0.99      | sK2 != X2 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_452]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_531,plain,
% 2.05/0.99      ( v3_tex_2(X0,sK2)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.99      | ~ l1_pre_topc(sK2)
% 2.05/0.99      | k2_pre_topc(sK2,X0) != k2_struct_0(sK2) ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_530]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_535,plain,
% 2.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.99      | v3_tex_2(X0,sK2)
% 2.05/0.99      | k2_pre_topc(sK2,X0) != k2_struct_0(sK2) ),
% 2.05/0.99      inference(global_propositional_subsumption,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_531,c_28]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_536,plain,
% 2.05/0.99      ( v3_tex_2(X0,sK2)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.99      | k2_pre_topc(sK2,X0) != k2_struct_0(sK2) ),
% 2.05/0.99      inference(renaming,[status(thm)],[c_535]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1923,plain,
% 2.05/0.99      ( k2_pre_topc(sK2,X0) != k2_struct_0(sK2)
% 2.05/0.99      | v3_tex_2(X0,sK2) = iProver_top
% 2.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_536]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1994,plain,
% 2.05/0.99      ( k2_pre_topc(sK2,X0) != k2_struct_0(sK2)
% 2.05/0.99      | v3_tex_2(X0,sK2) = iProver_top
% 2.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 2.05/0.99      inference(light_normalisation,[status(thm)],[c_1923,c_618]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2441,plain,
% 2.05/0.99      ( v3_tex_2(k2_struct_0(sK2),sK2) = iProver_top
% 2.05/0.99      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_1965,c_1994]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2486,plain,
% 2.05/0.99      ( v3_tex_2(k2_struct_0(sK2),sK2) = iProver_top ),
% 2.05/0.99      inference(forward_subsumption_resolution,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_2441,c_1940]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_3310,plain,
% 2.05/0.99      ( v3_tex_2(sK3,sK2) = iProver_top ),
% 2.05/0.99      inference(demodulation,[status(thm)],[c_3223,c_2486]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(contradiction,plain,
% 2.05/0.99      ( $false ),
% 2.05/0.99      inference(minisat,[status(thm)],[c_3310,c_2851,c_2623]) ).
% 2.05/0.99  
% 2.05/0.99  
% 2.05/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.05/0.99  
% 2.05/0.99  ------                               Statistics
% 2.05/0.99  
% 2.05/0.99  ------ General
% 2.05/0.99  
% 2.05/0.99  abstr_ref_over_cycles:                  0
% 2.05/0.99  abstr_ref_under_cycles:                 0
% 2.05/0.99  gc_basic_clause_elim:                   0
% 2.05/0.99  forced_gc_time:                         0
% 2.05/0.99  parsing_time:                           0.021
% 2.05/0.99  unif_index_cands_time:                  0.
% 2.05/0.99  unif_index_add_time:                    0.
% 2.05/0.99  orderings_time:                         0.
% 2.05/0.99  out_proof_time:                         0.022
% 2.05/0.99  total_time:                             0.139
% 2.05/0.99  num_of_symbols:                         53
% 2.05/0.99  num_of_terms:                           1938
% 2.05/0.99  
% 2.05/0.99  ------ Preprocessing
% 2.05/0.99  
% 2.05/0.99  num_of_splits:                          0
% 2.05/0.99  num_of_split_atoms:                     0
% 2.05/0.99  num_of_reused_defs:                     0
% 2.05/0.99  num_eq_ax_congr_red:                    25
% 2.05/0.99  num_of_sem_filtered_clauses:            1
% 2.05/0.99  num_of_subtypes:                        0
% 2.05/0.99  monotx_restored_types:                  0
% 2.05/0.99  sat_num_of_epr_types:                   0
% 2.05/0.99  sat_num_of_non_cyclic_types:            0
% 2.05/0.99  sat_guarded_non_collapsed_types:        0
% 2.05/0.99  num_pure_diseq_elim:                    0
% 2.05/0.99  simp_replaced_by:                       0
% 2.05/0.99  res_preprocessed:                       111
% 2.05/0.99  prep_upred:                             0
% 2.05/0.99  prep_unflattend:                        60
% 2.05/0.99  smt_new_axioms:                         0
% 2.05/0.99  pred_elim_cands:                        4
% 2.05/0.99  pred_elim:                              9
% 2.05/0.99  pred_elim_cl:                           14
% 2.05/0.99  pred_elim_cycles:                       13
% 2.05/0.99  merged_defs:                            2
% 2.05/0.99  merged_defs_ncl:                        0
% 2.05/0.99  bin_hyper_res:                          2
% 2.05/0.99  prep_cycles:                            4
% 2.05/0.99  pred_elim_time:                         0.018
% 2.05/0.99  splitting_time:                         0.
% 2.05/0.99  sem_filter_time:                        0.
% 2.05/0.99  monotx_time:                            0.
% 2.05/0.99  subtype_inf_time:                       0.
% 2.05/0.99  
% 2.05/0.99  ------ Problem properties
% 2.05/0.99  
% 2.05/0.99  clauses:                                18
% 2.05/0.99  conjectures:                            1
% 2.05/0.99  epr:                                    1
% 2.05/0.99  horn:                                   14
% 2.05/0.99  ground:                                 6
% 2.05/0.99  unary:                                  5
% 2.05/0.99  binary:                                 5
% 2.05/0.99  lits:                                   41
% 2.05/0.99  lits_eq:                                10
% 2.05/0.99  fd_pure:                                0
% 2.05/0.99  fd_pseudo:                              0
% 2.05/0.99  fd_cond:                                0
% 2.05/0.99  fd_pseudo_cond:                         1
% 2.05/0.99  ac_symbols:                             0
% 2.05/0.99  
% 2.05/0.99  ------ Propositional Solver
% 2.05/0.99  
% 2.05/0.99  prop_solver_calls:                      26
% 2.05/0.99  prop_fast_solver_calls:                 967
% 2.05/0.99  smt_solver_calls:                       0
% 2.05/0.99  smt_fast_solver_calls:                  0
% 2.05/0.99  prop_num_of_clauses:                    880
% 2.05/0.99  prop_preprocess_simplified:             3637
% 2.05/0.99  prop_fo_subsumed:                       42
% 2.05/0.99  prop_solver_time:                       0.
% 2.05/0.99  smt_solver_time:                        0.
% 2.05/0.99  smt_fast_solver_time:                   0.
% 2.05/0.99  prop_fast_solver_time:                  0.
% 2.05/0.99  prop_unsat_core_time:                   0.
% 2.05/0.99  
% 2.05/0.99  ------ QBF
% 2.05/0.99  
% 2.05/0.99  qbf_q_res:                              0
% 2.05/0.99  qbf_num_tautologies:                    0
% 2.05/0.99  qbf_prep_cycles:                        0
% 2.05/0.99  
% 2.05/0.99  ------ BMC1
% 2.05/0.99  
% 2.05/0.99  bmc1_current_bound:                     -1
% 2.05/0.99  bmc1_last_solved_bound:                 -1
% 2.05/0.99  bmc1_unsat_core_size:                   -1
% 2.05/0.99  bmc1_unsat_core_parents_size:           -1
% 2.05/0.99  bmc1_merge_next_fun:                    0
% 2.05/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.05/0.99  
% 2.05/0.99  ------ Instantiation
% 2.05/0.99  
% 2.05/0.99  inst_num_of_clauses:                    213
% 2.05/0.99  inst_num_in_passive:                    68
% 2.05/0.99  inst_num_in_active:                     136
% 2.05/0.99  inst_num_in_unprocessed:                9
% 2.05/0.99  inst_num_of_loops:                      170
% 2.05/0.99  inst_num_of_learning_restarts:          0
% 2.05/0.99  inst_num_moves_active_passive:          31
% 2.05/0.99  inst_lit_activity:                      0
% 2.05/0.99  inst_lit_activity_moves:                0
% 2.05/0.99  inst_num_tautologies:                   0
% 2.05/0.99  inst_num_prop_implied:                  0
% 2.05/0.99  inst_num_existing_simplified:           0
% 2.05/0.99  inst_num_eq_res_simplified:             0
% 2.05/0.99  inst_num_child_elim:                    0
% 2.05/0.99  inst_num_of_dismatching_blockings:      40
% 2.05/0.99  inst_num_of_non_proper_insts:           220
% 2.05/0.99  inst_num_of_duplicates:                 0
% 2.05/0.99  inst_inst_num_from_inst_to_res:         0
% 2.05/0.99  inst_dismatching_checking_time:         0.
% 2.05/0.99  
% 2.05/0.99  ------ Resolution
% 2.05/0.99  
% 2.05/0.99  res_num_of_clauses:                     0
% 2.05/0.99  res_num_in_passive:                     0
% 2.05/0.99  res_num_in_active:                      0
% 2.05/0.99  res_num_of_loops:                       115
% 2.05/0.99  res_forward_subset_subsumed:            34
% 2.05/0.99  res_backward_subset_subsumed:           0
% 2.05/0.99  res_forward_subsumed:                   1
% 2.05/0.99  res_backward_subsumed:                  0
% 2.05/0.99  res_forward_subsumption_resolution:     0
% 2.05/0.99  res_backward_subsumption_resolution:    0
% 2.05/0.99  res_clause_to_clause_subsumption:       221
% 2.05/0.99  res_orphan_elimination:                 0
% 2.05/0.99  res_tautology_del:                      33
% 2.05/0.99  res_num_eq_res_simplified:              0
% 2.05/0.99  res_num_sel_changes:                    0
% 2.05/0.99  res_moves_from_active_to_pass:          0
% 2.05/0.99  
% 2.05/0.99  ------ Superposition
% 2.05/0.99  
% 2.05/0.99  sup_time_total:                         0.
% 2.05/0.99  sup_time_generating:                    0.
% 2.05/0.99  sup_time_sim_full:                      0.
% 2.05/0.99  sup_time_sim_immed:                     0.
% 2.05/0.99  
% 2.05/0.99  sup_num_of_clauses:                     26
% 2.05/0.99  sup_num_in_active:                      9
% 2.05/0.99  sup_num_in_passive:                     17
% 2.05/0.99  sup_num_of_loops:                       32
% 2.05/0.99  sup_fw_superposition:                   26
% 2.05/0.99  sup_bw_superposition:                   6
% 2.05/0.99  sup_immediate_simplified:               4
% 2.05/0.99  sup_given_eliminated:                   0
% 2.05/0.99  comparisons_done:                       0
% 2.05/0.99  comparisons_avoided:                    0
% 2.05/0.99  
% 2.05/0.99  ------ Simplifications
% 2.05/0.99  
% 2.05/0.99  
% 2.05/0.99  sim_fw_subset_subsumed:                 3
% 2.05/0.99  sim_bw_subset_subsumed:                 5
% 2.05/0.99  sim_fw_subsumed:                        3
% 2.05/0.99  sim_bw_subsumed:                        0
% 2.05/0.99  sim_fw_subsumption_res:                 2
% 2.05/0.99  sim_bw_subsumption_res:                 0
% 2.05/0.99  sim_tautology_del:                      2
% 2.05/0.99  sim_eq_tautology_del:                   2
% 2.05/0.99  sim_eq_res_simp:                        1
% 2.05/0.99  sim_fw_demodulated:                     2
% 2.05/0.99  sim_bw_demodulated:                     20
% 2.05/0.99  sim_light_normalised:                   10
% 2.05/0.99  sim_joinable_taut:                      0
% 2.05/0.99  sim_joinable_simp:                      0
% 2.05/0.99  sim_ac_normalised:                      0
% 2.05/0.99  sim_smt_subsumption:                    0
% 2.05/0.99  
%------------------------------------------------------------------------------
