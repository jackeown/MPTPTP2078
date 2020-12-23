%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:18 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :  177 (1202 expanded)
%              Number of clauses        :   99 ( 336 expanded)
%              Number of leaves         :   20 ( 263 expanded)
%              Depth                    :   24
%              Number of atoms          :  729 (6922 expanded)
%              Number of equality atoms :  150 ( 434 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
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
    inference(nnf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f37])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f53,plain,(
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

fof(f52,plain,
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

fof(f54,plain,
    ( ( v1_subset_1(sK3,u1_struct_0(sK2))
      | ~ v3_tex_2(sK3,sK2) )
    & ( ~ v1_subset_1(sK3,u1_struct_0(sK2))
      | v3_tex_2(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v1_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f51,f53,f52])).

fof(f86,plain,
    ( ~ v1_subset_1(sK3,u1_struct_0(sK2))
    | v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f85,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f54])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f84,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f65,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f46,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK1(X0),X0)
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK1(X0),X0)
            & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).

fof(f75,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f82,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f83,plain,(
    v1_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f44,plain,(
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

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( X1 = X3
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f62,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f80,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f87,plain,
    ( v1_subset_1(sK3,u1_struct_0(sK2))
    | ~ v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_247,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_12,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_249,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_313,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_subset_1(X0,X1)
    | X0 = X1 ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_249])).

cnf(c_27,negated_conjecture,
    ( v3_tex_2(sK3,sK2)
    | ~ v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_251,plain,
    ( v3_tex_2(sK3,sK2)
    | ~ v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(prop_impl,[status(thm)],[c_27])).

cnf(c_493,plain,
    ( v3_tex_2(sK3,sK2)
    | ~ r1_tarski(X0,X1)
    | X1 = X0
    | u1_struct_0(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_313,c_251])).

cnf(c_494,plain,
    ( v3_tex_2(sK3,sK2)
    | ~ r1_tarski(sK3,u1_struct_0(sK2))
    | u1_struct_0(sK2) = sK3 ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_887,plain,
    ( v3_tex_2(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | u1_struct_0(sK2) != X1
    | u1_struct_0(sK2) = sK3
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_247,c_494])).

cnf(c_888,plain,
    ( v3_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(sK2) = sK3 ),
    inference(unflattening,[status(thm)],[c_887])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_890,plain,
    ( v3_tex_2(sK3,sK2)
    | u1_struct_0(sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_888,c_28])).

cnf(c_1915,plain,
    ( u1_struct_0(sK2) = sK3
    | v3_tex_2(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_890])).

cnf(c_6,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_5,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_430,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_6,c_5])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_716,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_430,c_29])).

cnf(c_717,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_716])).

cnf(c_1936,plain,
    ( k2_struct_0(sK2) = sK3
    | v3_tex_2(sK3,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1915,c_717])).

cnf(c_1924,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1930,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1924,c_717])).

cnf(c_11,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_22,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_24,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_533,plain,
    ( ~ v3_tex_2(X0,X1)
    | v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_22,c_24])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_569,plain,
    ( ~ v3_tex_2(X0,X1)
    | v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_533,c_32])).

cnf(c_570,plain,
    ( ~ v3_tex_2(X0,sK2)
    | v1_tops_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_569])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_30,negated_conjecture,
    ( v1_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_574,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_tops_1(X0,sK2)
    | ~ v3_tex_2(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_570,c_31,c_30,c_29])).

cnf(c_575,plain,
    ( ~ v3_tex_2(X0,sK2)
    | v1_tops_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_574])).

cnf(c_687,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X2)
    | X0 != X1
    | k2_pre_topc(X2,X1) = u1_struct_0(X2)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_575])).

cnf(c_688,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | k2_pre_topc(sK2,X0) = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_687])).

cnf(c_692,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_tex_2(X0,sK2)
    | k2_pre_topc(sK2,X0) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_688,c_29])).

cnf(c_693,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_pre_topc(sK2,X0) = u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_692])).

cnf(c_1919,plain,
    ( k2_pre_topc(sK2,X0) = u1_struct_0(sK2)
    | v3_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_693])).

cnf(c_1959,plain,
    ( k2_pre_topc(sK2,X0) = k2_struct_0(sK2)
    | v3_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1919,c_717])).

cnf(c_2097,plain,
    ( k2_pre_topc(sK2,sK3) = k2_struct_0(sK2)
    | v3_tex_2(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1930,c_1959])).

cnf(c_2534,plain,
    ( k2_pre_topc(sK2,sK3) = k2_struct_0(sK2)
    | k2_struct_0(sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_1936,c_2097])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1925,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1933,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1925,c_0])).

cnf(c_18,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_730,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | X2 = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_29])).

cnf(c_731,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v3_tex_2(X1,sK2)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_730])).

cnf(c_23,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_614,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_32])).

cnf(c_615,plain,
    ( v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_614])).

cnf(c_735,plain,
    ( ~ v3_tex_2(X1,sK2)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | X1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_731,c_31,c_30,c_29,c_615])).

cnf(c_736,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ r1_tarski(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | X0 = X1 ),
    inference(renaming,[status(thm)],[c_735])).

cnf(c_864,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_247,c_736])).

cnf(c_1916,plain,
    ( X0 = X1
    | v3_tex_2(X1,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_864])).

cnf(c_1988,plain,
    ( X0 = X1
    | v3_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1916,c_717])).

cnf(c_2172,plain,
    ( sK3 = X0
    | v3_tex_2(sK3,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1930,c_1988])).

cnf(c_2632,plain,
    ( k2_struct_0(sK2) = sK3
    | v3_tex_2(sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1933,c_2172])).

cnf(c_2675,plain,
    ( k2_struct_0(sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2534,c_1936,c_1930,c_2632])).

cnf(c_7,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_9,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_445,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | X1 != X2
    | k2_pre_topc(X1,X0) = X0
    | k2_struct_0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_9])).

cnf(c_446,plain,
    ( ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_445])).

cnf(c_647,plain,
    ( ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_446,c_31])).

cnf(c_648,plain,
    ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_647])).

cnf(c_650,plain,
    ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_648,c_29])).

cnf(c_1921,plain,
    ( k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2)
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_650])).

cnf(c_1947,plain,
    ( k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2)
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1921,c_717])).

cnf(c_1950,plain,
    ( k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1947,c_1933])).

cnf(c_10,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_619,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tex_2(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_615,c_31,c_30,c_29])).

cnf(c_620,plain,
    ( v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_619])).

cnf(c_25,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_590,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_32])).

cnf(c_591,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ v1_tops_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_590])).

cnf(c_595,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ v1_tops_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_591,c_31,c_29])).

cnf(c_630,plain,
    ( v3_tex_2(X0,sK2)
    | ~ v1_tops_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_620,c_595])).

cnf(c_666,plain,
    ( v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X2)
    | X0 != X1
    | k2_pre_topc(X2,X1) != u1_struct_0(X2)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_630])).

cnf(c_667,plain,
    ( v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | k2_pre_topc(sK2,X0) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_666])).

cnf(c_671,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_tex_2(X0,sK2)
    | k2_pre_topc(sK2,X0) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_667,c_29])).

cnf(c_672,plain,
    ( v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_pre_topc(sK2,X0) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_671])).

cnf(c_1920,plain,
    ( k2_pre_topc(sK2,X0) != u1_struct_0(sK2)
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_672])).

cnf(c_1966,plain,
    ( k2_pre_topc(sK2,X0) != k2_struct_0(sK2)
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1920,c_717])).

cnf(c_2365,plain,
    ( v3_tex_2(k2_struct_0(sK2),sK2) = iProver_top
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1950,c_1966])).

cnf(c_2538,plain,
    ( v3_tex_2(k2_struct_0(sK2),sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2365,c_1933])).

cnf(c_2679,plain,
    ( v3_tex_2(sK3,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2675,c_2538])).

cnf(c_2,plain,
    ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_26,negated_conjecture,
    ( ~ v3_tex_2(sK3,sK2)
    | v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_253,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(prop_impl,[status(thm)],[c_26])).

cnf(c_481,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | u1_struct_0(sK2) != X0
    | k2_subset_1(X0) != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_253])).

cnf(c_482,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | k2_subset_1(u1_struct_0(sK2)) != sK3 ),
    inference(unflattening,[status(thm)],[c_481])).

cnf(c_1923,plain,
    ( k2_subset_1(u1_struct_0(sK2)) != sK3
    | v3_tex_2(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_482])).

cnf(c_1941,plain,
    ( k2_subset_1(k2_struct_0(sK2)) != sK3
    | v3_tex_2(sK3,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1923,c_717])).

cnf(c_1942,plain,
    ( k2_struct_0(sK2) != sK3
    | v3_tex_2(sK3,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1941,c_0])).

cnf(c_2684,plain,
    ( sK3 != sK3
    | v3_tex_2(sK3,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2675,c_1942])).

cnf(c_2729,plain,
    ( v3_tex_2(sK3,sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2684])).

cnf(c_2741,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2679,c_2729])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:55:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.14/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.00  
% 2.14/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.14/1.00  
% 2.14/1.00  ------  iProver source info
% 2.14/1.00  
% 2.14/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.14/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.14/1.00  git: non_committed_changes: false
% 2.14/1.00  git: last_make_outside_of_git: false
% 2.14/1.00  
% 2.14/1.00  ------ 
% 2.14/1.00  
% 2.14/1.00  ------ Input Options
% 2.14/1.00  
% 2.14/1.00  --out_options                           all
% 2.14/1.00  --tptp_safe_out                         true
% 2.14/1.00  --problem_path                          ""
% 2.14/1.00  --include_path                          ""
% 2.14/1.00  --clausifier                            res/vclausify_rel
% 2.14/1.00  --clausifier_options                    --mode clausify
% 2.14/1.00  --stdin                                 false
% 2.14/1.00  --stats_out                             all
% 2.14/1.00  
% 2.14/1.00  ------ General Options
% 2.14/1.00  
% 2.14/1.00  --fof                                   false
% 2.14/1.00  --time_out_real                         305.
% 2.14/1.00  --time_out_virtual                      -1.
% 2.14/1.00  --symbol_type_check                     false
% 2.14/1.00  --clausify_out                          false
% 2.14/1.00  --sig_cnt_out                           false
% 2.14/1.00  --trig_cnt_out                          false
% 2.14/1.00  --trig_cnt_out_tolerance                1.
% 2.14/1.00  --trig_cnt_out_sk_spl                   false
% 2.14/1.00  --abstr_cl_out                          false
% 2.14/1.00  
% 2.14/1.00  ------ Global Options
% 2.14/1.00  
% 2.14/1.00  --schedule                              default
% 2.14/1.00  --add_important_lit                     false
% 2.14/1.00  --prop_solver_per_cl                    1000
% 2.14/1.00  --min_unsat_core                        false
% 2.14/1.00  --soft_assumptions                      false
% 2.14/1.00  --soft_lemma_size                       3
% 2.14/1.00  --prop_impl_unit_size                   0
% 2.14/1.00  --prop_impl_unit                        []
% 2.14/1.00  --share_sel_clauses                     true
% 2.14/1.00  --reset_solvers                         false
% 2.14/1.00  --bc_imp_inh                            [conj_cone]
% 2.14/1.00  --conj_cone_tolerance                   3.
% 2.14/1.00  --extra_neg_conj                        none
% 2.14/1.00  --large_theory_mode                     true
% 2.14/1.00  --prolific_symb_bound                   200
% 2.14/1.00  --lt_threshold                          2000
% 2.14/1.00  --clause_weak_htbl                      true
% 2.14/1.00  --gc_record_bc_elim                     false
% 2.14/1.00  
% 2.14/1.00  ------ Preprocessing Options
% 2.14/1.00  
% 2.14/1.00  --preprocessing_flag                    true
% 2.14/1.00  --time_out_prep_mult                    0.1
% 2.14/1.00  --splitting_mode                        input
% 2.14/1.00  --splitting_grd                         true
% 2.14/1.00  --splitting_cvd                         false
% 2.14/1.00  --splitting_cvd_svl                     false
% 2.14/1.00  --splitting_nvd                         32
% 2.14/1.00  --sub_typing                            true
% 2.14/1.00  --prep_gs_sim                           true
% 2.14/1.00  --prep_unflatten                        true
% 2.14/1.00  --prep_res_sim                          true
% 2.14/1.00  --prep_upred                            true
% 2.14/1.00  --prep_sem_filter                       exhaustive
% 2.14/1.00  --prep_sem_filter_out                   false
% 2.14/1.00  --pred_elim                             true
% 2.14/1.00  --res_sim_input                         true
% 2.14/1.00  --eq_ax_congr_red                       true
% 2.14/1.00  --pure_diseq_elim                       true
% 2.14/1.00  --brand_transform                       false
% 2.14/1.00  --non_eq_to_eq                          false
% 2.14/1.00  --prep_def_merge                        true
% 2.14/1.00  --prep_def_merge_prop_impl              false
% 2.14/1.00  --prep_def_merge_mbd                    true
% 2.14/1.00  --prep_def_merge_tr_red                 false
% 2.14/1.00  --prep_def_merge_tr_cl                  false
% 2.14/1.00  --smt_preprocessing                     true
% 2.14/1.00  --smt_ac_axioms                         fast
% 2.14/1.00  --preprocessed_out                      false
% 2.14/1.00  --preprocessed_stats                    false
% 2.14/1.00  
% 2.14/1.00  ------ Abstraction refinement Options
% 2.14/1.00  
% 2.14/1.00  --abstr_ref                             []
% 2.14/1.00  --abstr_ref_prep                        false
% 2.14/1.00  --abstr_ref_until_sat                   false
% 2.14/1.00  --abstr_ref_sig_restrict                funpre
% 2.14/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.14/1.00  --abstr_ref_under                       []
% 2.14/1.00  
% 2.14/1.00  ------ SAT Options
% 2.14/1.00  
% 2.14/1.00  --sat_mode                              false
% 2.14/1.00  --sat_fm_restart_options                ""
% 2.14/1.00  --sat_gr_def                            false
% 2.14/1.00  --sat_epr_types                         true
% 2.14/1.00  --sat_non_cyclic_types                  false
% 2.14/1.00  --sat_finite_models                     false
% 2.14/1.00  --sat_fm_lemmas                         false
% 2.14/1.00  --sat_fm_prep                           false
% 2.14/1.00  --sat_fm_uc_incr                        true
% 2.14/1.00  --sat_out_model                         small
% 2.14/1.00  --sat_out_clauses                       false
% 2.14/1.00  
% 2.14/1.00  ------ QBF Options
% 2.14/1.00  
% 2.14/1.00  --qbf_mode                              false
% 2.14/1.00  --qbf_elim_univ                         false
% 2.14/1.00  --qbf_dom_inst                          none
% 2.14/1.00  --qbf_dom_pre_inst                      false
% 2.14/1.00  --qbf_sk_in                             false
% 2.14/1.00  --qbf_pred_elim                         true
% 2.14/1.00  --qbf_split                             512
% 2.14/1.00  
% 2.14/1.00  ------ BMC1 Options
% 2.14/1.00  
% 2.14/1.00  --bmc1_incremental                      false
% 2.14/1.00  --bmc1_axioms                           reachable_all
% 2.14/1.00  --bmc1_min_bound                        0
% 2.14/1.00  --bmc1_max_bound                        -1
% 2.14/1.00  --bmc1_max_bound_default                -1
% 2.14/1.00  --bmc1_symbol_reachability              true
% 2.14/1.00  --bmc1_property_lemmas                  false
% 2.14/1.00  --bmc1_k_induction                      false
% 2.14/1.00  --bmc1_non_equiv_states                 false
% 2.14/1.00  --bmc1_deadlock                         false
% 2.14/1.00  --bmc1_ucm                              false
% 2.14/1.00  --bmc1_add_unsat_core                   none
% 2.14/1.00  --bmc1_unsat_core_children              false
% 2.14/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.14/1.00  --bmc1_out_stat                         full
% 2.14/1.00  --bmc1_ground_init                      false
% 2.14/1.00  --bmc1_pre_inst_next_state              false
% 2.14/1.00  --bmc1_pre_inst_state                   false
% 2.14/1.00  --bmc1_pre_inst_reach_state             false
% 2.14/1.00  --bmc1_out_unsat_core                   false
% 2.14/1.00  --bmc1_aig_witness_out                  false
% 2.14/1.00  --bmc1_verbose                          false
% 2.14/1.00  --bmc1_dump_clauses_tptp                false
% 2.14/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.14/1.00  --bmc1_dump_file                        -
% 2.14/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.14/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.14/1.00  --bmc1_ucm_extend_mode                  1
% 2.14/1.00  --bmc1_ucm_init_mode                    2
% 2.14/1.00  --bmc1_ucm_cone_mode                    none
% 2.14/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.14/1.00  --bmc1_ucm_relax_model                  4
% 2.14/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.14/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.14/1.00  --bmc1_ucm_layered_model                none
% 2.14/1.00  --bmc1_ucm_max_lemma_size               10
% 2.14/1.00  
% 2.14/1.00  ------ AIG Options
% 2.14/1.00  
% 2.14/1.00  --aig_mode                              false
% 2.14/1.00  
% 2.14/1.00  ------ Instantiation Options
% 2.14/1.00  
% 2.14/1.00  --instantiation_flag                    true
% 2.14/1.00  --inst_sos_flag                         false
% 2.14/1.00  --inst_sos_phase                        true
% 2.14/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.14/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.14/1.00  --inst_lit_sel_side                     num_symb
% 2.14/1.00  --inst_solver_per_active                1400
% 2.14/1.00  --inst_solver_calls_frac                1.
% 2.14/1.00  --inst_passive_queue_type               priority_queues
% 2.14/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.14/1.00  --inst_passive_queues_freq              [25;2]
% 2.14/1.00  --inst_dismatching                      true
% 2.14/1.00  --inst_eager_unprocessed_to_passive     true
% 2.14/1.00  --inst_prop_sim_given                   true
% 2.14/1.00  --inst_prop_sim_new                     false
% 2.14/1.00  --inst_subs_new                         false
% 2.14/1.00  --inst_eq_res_simp                      false
% 2.14/1.00  --inst_subs_given                       false
% 2.14/1.00  --inst_orphan_elimination               true
% 2.14/1.00  --inst_learning_loop_flag               true
% 2.14/1.00  --inst_learning_start                   3000
% 2.14/1.00  --inst_learning_factor                  2
% 2.14/1.00  --inst_start_prop_sim_after_learn       3
% 2.14/1.00  --inst_sel_renew                        solver
% 2.14/1.00  --inst_lit_activity_flag                true
% 2.14/1.00  --inst_restr_to_given                   false
% 2.14/1.00  --inst_activity_threshold               500
% 2.14/1.00  --inst_out_proof                        true
% 2.14/1.00  
% 2.14/1.00  ------ Resolution Options
% 2.14/1.00  
% 2.14/1.00  --resolution_flag                       true
% 2.14/1.00  --res_lit_sel                           adaptive
% 2.14/1.00  --res_lit_sel_side                      none
% 2.14/1.00  --res_ordering                          kbo
% 2.14/1.00  --res_to_prop_solver                    active
% 2.14/1.00  --res_prop_simpl_new                    false
% 2.14/1.00  --res_prop_simpl_given                  true
% 2.14/1.00  --res_passive_queue_type                priority_queues
% 2.14/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.14/1.00  --res_passive_queues_freq               [15;5]
% 2.14/1.00  --res_forward_subs                      full
% 2.14/1.00  --res_backward_subs                     full
% 2.14/1.00  --res_forward_subs_resolution           true
% 2.14/1.00  --res_backward_subs_resolution          true
% 2.14/1.00  --res_orphan_elimination                true
% 2.14/1.00  --res_time_limit                        2.
% 2.14/1.00  --res_out_proof                         true
% 2.14/1.00  
% 2.14/1.00  ------ Superposition Options
% 2.14/1.00  
% 2.14/1.00  --superposition_flag                    true
% 2.14/1.00  --sup_passive_queue_type                priority_queues
% 2.14/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.14/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.14/1.00  --demod_completeness_check              fast
% 2.14/1.00  --demod_use_ground                      true
% 2.14/1.00  --sup_to_prop_solver                    passive
% 2.14/1.00  --sup_prop_simpl_new                    true
% 2.14/1.00  --sup_prop_simpl_given                  true
% 2.14/1.00  --sup_fun_splitting                     false
% 2.14/1.00  --sup_smt_interval                      50000
% 2.14/1.00  
% 2.14/1.00  ------ Superposition Simplification Setup
% 2.14/1.00  
% 2.14/1.00  --sup_indices_passive                   []
% 2.14/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.14/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/1.00  --sup_full_bw                           [BwDemod]
% 2.14/1.00  --sup_immed_triv                        [TrivRules]
% 2.14/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.14/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/1.00  --sup_immed_bw_main                     []
% 2.14/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.14/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.14/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.14/1.00  
% 2.14/1.00  ------ Combination Options
% 2.14/1.00  
% 2.14/1.00  --comb_res_mult                         3
% 2.14/1.00  --comb_sup_mult                         2
% 2.14/1.00  --comb_inst_mult                        10
% 2.14/1.00  
% 2.14/1.00  ------ Debug Options
% 2.14/1.00  
% 2.14/1.00  --dbg_backtrace                         false
% 2.14/1.00  --dbg_dump_prop_clauses                 false
% 2.14/1.00  --dbg_dump_prop_clauses_file            -
% 2.14/1.00  --dbg_out_stat                          false
% 2.14/1.00  ------ Parsing...
% 2.14/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.14/1.00  
% 2.14/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 10 0s  sf_e  pe_s  pe_e 
% 2.14/1.00  
% 2.14/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.14/1.00  
% 2.14/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.14/1.00  ------ Proving...
% 2.14/1.00  ------ Problem Properties 
% 2.14/1.00  
% 2.14/1.00  
% 2.14/1.00  clauses                                 14
% 2.14/1.00  conjectures                             1
% 2.14/1.00  EPR                                     0
% 2.14/1.00  Horn                                    11
% 2.14/1.00  unary                                   4
% 2.14/1.00  binary                                  3
% 2.14/1.00  lits                                    33
% 2.14/1.00  lits eq                                 10
% 2.14/1.00  fd_pure                                 0
% 2.14/1.00  fd_pseudo                               0
% 2.14/1.00  fd_cond                                 0
% 2.14/1.00  fd_pseudo_cond                          1
% 2.14/1.00  AC symbols                              0
% 2.14/1.00  
% 2.14/1.00  ------ Schedule dynamic 5 is on 
% 2.14/1.00  
% 2.14/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.14/1.00  
% 2.14/1.00  
% 2.14/1.00  ------ 
% 2.14/1.00  Current options:
% 2.14/1.00  ------ 
% 2.14/1.00  
% 2.14/1.00  ------ Input Options
% 2.14/1.00  
% 2.14/1.00  --out_options                           all
% 2.14/1.00  --tptp_safe_out                         true
% 2.14/1.00  --problem_path                          ""
% 2.14/1.00  --include_path                          ""
% 2.14/1.00  --clausifier                            res/vclausify_rel
% 2.14/1.00  --clausifier_options                    --mode clausify
% 2.14/1.00  --stdin                                 false
% 2.14/1.00  --stats_out                             all
% 2.14/1.00  
% 2.14/1.00  ------ General Options
% 2.14/1.00  
% 2.14/1.00  --fof                                   false
% 2.14/1.00  --time_out_real                         305.
% 2.14/1.00  --time_out_virtual                      -1.
% 2.14/1.00  --symbol_type_check                     false
% 2.14/1.00  --clausify_out                          false
% 2.14/1.00  --sig_cnt_out                           false
% 2.14/1.00  --trig_cnt_out                          false
% 2.14/1.00  --trig_cnt_out_tolerance                1.
% 2.14/1.00  --trig_cnt_out_sk_spl                   false
% 2.14/1.00  --abstr_cl_out                          false
% 2.14/1.00  
% 2.14/1.00  ------ Global Options
% 2.14/1.00  
% 2.14/1.00  --schedule                              default
% 2.14/1.00  --add_important_lit                     false
% 2.14/1.00  --prop_solver_per_cl                    1000
% 2.14/1.00  --min_unsat_core                        false
% 2.14/1.00  --soft_assumptions                      false
% 2.14/1.00  --soft_lemma_size                       3
% 2.14/1.00  --prop_impl_unit_size                   0
% 2.14/1.00  --prop_impl_unit                        []
% 2.14/1.00  --share_sel_clauses                     true
% 2.14/1.00  --reset_solvers                         false
% 2.14/1.00  --bc_imp_inh                            [conj_cone]
% 2.14/1.00  --conj_cone_tolerance                   3.
% 2.14/1.00  --extra_neg_conj                        none
% 2.14/1.00  --large_theory_mode                     true
% 2.14/1.00  --prolific_symb_bound                   200
% 2.14/1.00  --lt_threshold                          2000
% 2.14/1.00  --clause_weak_htbl                      true
% 2.14/1.00  --gc_record_bc_elim                     false
% 2.14/1.00  
% 2.14/1.00  ------ Preprocessing Options
% 2.14/1.00  
% 2.14/1.00  --preprocessing_flag                    true
% 2.14/1.00  --time_out_prep_mult                    0.1
% 2.14/1.00  --splitting_mode                        input
% 2.14/1.00  --splitting_grd                         true
% 2.14/1.00  --splitting_cvd                         false
% 2.14/1.00  --splitting_cvd_svl                     false
% 2.14/1.00  --splitting_nvd                         32
% 2.14/1.00  --sub_typing                            true
% 2.14/1.00  --prep_gs_sim                           true
% 2.14/1.00  --prep_unflatten                        true
% 2.14/1.00  --prep_res_sim                          true
% 2.14/1.00  --prep_upred                            true
% 2.14/1.00  --prep_sem_filter                       exhaustive
% 2.14/1.00  --prep_sem_filter_out                   false
% 2.14/1.00  --pred_elim                             true
% 2.14/1.00  --res_sim_input                         true
% 2.14/1.00  --eq_ax_congr_red                       true
% 2.14/1.00  --pure_diseq_elim                       true
% 2.14/1.00  --brand_transform                       false
% 2.14/1.00  --non_eq_to_eq                          false
% 2.14/1.00  --prep_def_merge                        true
% 2.14/1.00  --prep_def_merge_prop_impl              false
% 2.14/1.00  --prep_def_merge_mbd                    true
% 2.14/1.00  --prep_def_merge_tr_red                 false
% 2.14/1.00  --prep_def_merge_tr_cl                  false
% 2.14/1.00  --smt_preprocessing                     true
% 2.14/1.00  --smt_ac_axioms                         fast
% 2.14/1.00  --preprocessed_out                      false
% 2.14/1.00  --preprocessed_stats                    false
% 2.14/1.00  
% 2.14/1.00  ------ Abstraction refinement Options
% 2.14/1.00  
% 2.14/1.00  --abstr_ref                             []
% 2.14/1.00  --abstr_ref_prep                        false
% 2.14/1.00  --abstr_ref_until_sat                   false
% 2.14/1.00  --abstr_ref_sig_restrict                funpre
% 2.14/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.14/1.00  --abstr_ref_under                       []
% 2.14/1.00  
% 2.14/1.00  ------ SAT Options
% 2.14/1.00  
% 2.14/1.00  --sat_mode                              false
% 2.14/1.00  --sat_fm_restart_options                ""
% 2.14/1.00  --sat_gr_def                            false
% 2.14/1.00  --sat_epr_types                         true
% 2.14/1.00  --sat_non_cyclic_types                  false
% 2.14/1.00  --sat_finite_models                     false
% 2.14/1.00  --sat_fm_lemmas                         false
% 2.14/1.00  --sat_fm_prep                           false
% 2.14/1.00  --sat_fm_uc_incr                        true
% 2.14/1.00  --sat_out_model                         small
% 2.14/1.00  --sat_out_clauses                       false
% 2.14/1.00  
% 2.14/1.00  ------ QBF Options
% 2.14/1.00  
% 2.14/1.00  --qbf_mode                              false
% 2.14/1.00  --qbf_elim_univ                         false
% 2.14/1.00  --qbf_dom_inst                          none
% 2.14/1.00  --qbf_dom_pre_inst                      false
% 2.14/1.00  --qbf_sk_in                             false
% 2.14/1.00  --qbf_pred_elim                         true
% 2.14/1.00  --qbf_split                             512
% 2.14/1.00  
% 2.14/1.00  ------ BMC1 Options
% 2.14/1.00  
% 2.14/1.00  --bmc1_incremental                      false
% 2.14/1.00  --bmc1_axioms                           reachable_all
% 2.14/1.00  --bmc1_min_bound                        0
% 2.14/1.00  --bmc1_max_bound                        -1
% 2.14/1.00  --bmc1_max_bound_default                -1
% 2.14/1.00  --bmc1_symbol_reachability              true
% 2.14/1.00  --bmc1_property_lemmas                  false
% 2.14/1.00  --bmc1_k_induction                      false
% 2.14/1.00  --bmc1_non_equiv_states                 false
% 2.14/1.00  --bmc1_deadlock                         false
% 2.14/1.00  --bmc1_ucm                              false
% 2.14/1.00  --bmc1_add_unsat_core                   none
% 2.14/1.00  --bmc1_unsat_core_children              false
% 2.14/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.14/1.00  --bmc1_out_stat                         full
% 2.14/1.00  --bmc1_ground_init                      false
% 2.14/1.00  --bmc1_pre_inst_next_state              false
% 2.14/1.00  --bmc1_pre_inst_state                   false
% 2.14/1.00  --bmc1_pre_inst_reach_state             false
% 2.14/1.00  --bmc1_out_unsat_core                   false
% 2.14/1.00  --bmc1_aig_witness_out                  false
% 2.14/1.00  --bmc1_verbose                          false
% 2.14/1.00  --bmc1_dump_clauses_tptp                false
% 2.14/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.14/1.00  --bmc1_dump_file                        -
% 2.14/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.14/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.14/1.00  --bmc1_ucm_extend_mode                  1
% 2.14/1.00  --bmc1_ucm_init_mode                    2
% 2.14/1.00  --bmc1_ucm_cone_mode                    none
% 2.14/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.14/1.00  --bmc1_ucm_relax_model                  4
% 2.14/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.14/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.14/1.00  --bmc1_ucm_layered_model                none
% 2.14/1.00  --bmc1_ucm_max_lemma_size               10
% 2.14/1.00  
% 2.14/1.00  ------ AIG Options
% 2.14/1.00  
% 2.14/1.00  --aig_mode                              false
% 2.14/1.00  
% 2.14/1.00  ------ Instantiation Options
% 2.14/1.00  
% 2.14/1.00  --instantiation_flag                    true
% 2.14/1.00  --inst_sos_flag                         false
% 2.14/1.00  --inst_sos_phase                        true
% 2.14/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.14/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.14/1.00  --inst_lit_sel_side                     none
% 2.14/1.00  --inst_solver_per_active                1400
% 2.14/1.00  --inst_solver_calls_frac                1.
% 2.14/1.00  --inst_passive_queue_type               priority_queues
% 2.14/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.14/1.00  --inst_passive_queues_freq              [25;2]
% 2.14/1.00  --inst_dismatching                      true
% 2.14/1.00  --inst_eager_unprocessed_to_passive     true
% 2.14/1.00  --inst_prop_sim_given                   true
% 2.14/1.00  --inst_prop_sim_new                     false
% 2.14/1.00  --inst_subs_new                         false
% 2.14/1.00  --inst_eq_res_simp                      false
% 2.14/1.00  --inst_subs_given                       false
% 2.14/1.00  --inst_orphan_elimination               true
% 2.14/1.00  --inst_learning_loop_flag               true
% 2.14/1.00  --inst_learning_start                   3000
% 2.14/1.00  --inst_learning_factor                  2
% 2.14/1.00  --inst_start_prop_sim_after_learn       3
% 2.14/1.00  --inst_sel_renew                        solver
% 2.14/1.00  --inst_lit_activity_flag                true
% 2.14/1.00  --inst_restr_to_given                   false
% 2.14/1.00  --inst_activity_threshold               500
% 2.14/1.00  --inst_out_proof                        true
% 2.14/1.00  
% 2.14/1.00  ------ Resolution Options
% 2.14/1.00  
% 2.14/1.00  --resolution_flag                       false
% 2.14/1.00  --res_lit_sel                           adaptive
% 2.14/1.00  --res_lit_sel_side                      none
% 2.14/1.00  --res_ordering                          kbo
% 2.14/1.00  --res_to_prop_solver                    active
% 2.14/1.00  --res_prop_simpl_new                    false
% 2.14/1.00  --res_prop_simpl_given                  true
% 2.14/1.00  --res_passive_queue_type                priority_queues
% 2.14/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.14/1.00  --res_passive_queues_freq               [15;5]
% 2.14/1.00  --res_forward_subs                      full
% 2.14/1.00  --res_backward_subs                     full
% 2.14/1.00  --res_forward_subs_resolution           true
% 2.14/1.00  --res_backward_subs_resolution          true
% 2.14/1.00  --res_orphan_elimination                true
% 2.14/1.00  --res_time_limit                        2.
% 2.14/1.00  --res_out_proof                         true
% 2.14/1.00  
% 2.14/1.00  ------ Superposition Options
% 2.14/1.00  
% 2.14/1.00  --superposition_flag                    true
% 2.14/1.00  --sup_passive_queue_type                priority_queues
% 2.14/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.14/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.14/1.00  --demod_completeness_check              fast
% 2.14/1.00  --demod_use_ground                      true
% 2.14/1.00  --sup_to_prop_solver                    passive
% 2.14/1.00  --sup_prop_simpl_new                    true
% 2.14/1.00  --sup_prop_simpl_given                  true
% 2.14/1.00  --sup_fun_splitting                     false
% 2.14/1.00  --sup_smt_interval                      50000
% 2.14/1.00  
% 2.14/1.00  ------ Superposition Simplification Setup
% 2.14/1.00  
% 2.14/1.00  --sup_indices_passive                   []
% 2.14/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.14/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/1.00  --sup_full_bw                           [BwDemod]
% 2.14/1.00  --sup_immed_triv                        [TrivRules]
% 2.14/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.14/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/1.00  --sup_immed_bw_main                     []
% 2.14/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.14/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.14/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.14/1.00  
% 2.14/1.00  ------ Combination Options
% 2.14/1.00  
% 2.14/1.00  --comb_res_mult                         3
% 2.14/1.00  --comb_sup_mult                         2
% 2.14/1.00  --comb_inst_mult                        10
% 2.14/1.00  
% 2.14/1.00  ------ Debug Options
% 2.14/1.00  
% 2.14/1.00  --dbg_backtrace                         false
% 2.14/1.00  --dbg_dump_prop_clauses                 false
% 2.14/1.00  --dbg_dump_prop_clauses_file            -
% 2.14/1.00  --dbg_out_stat                          false
% 2.14/1.00  
% 2.14/1.00  
% 2.14/1.00  
% 2.14/1.00  
% 2.14/1.00  ------ Proving...
% 2.14/1.00  
% 2.14/1.00  
% 2.14/1.00  % SZS status Theorem for theBenchmark.p
% 2.14/1.00  
% 2.14/1.00   Resolution empty clause
% 2.14/1.00  
% 2.14/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.14/1.00  
% 2.14/1.00  fof(f4,axiom,(
% 2.14/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.14/1.00  
% 2.14/1.00  fof(f38,plain,(
% 2.14/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.14/1.00    inference(nnf_transformation,[],[f4])).
% 2.14/1.00  
% 2.14/1.00  fof(f58,plain,(
% 2.14/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.14/1.00    inference(cnf_transformation,[],[f38])).
% 2.14/1.00  
% 2.14/1.00  fof(f10,axiom,(
% 2.14/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.14/1.00  
% 2.14/1.00  fof(f25,plain,(
% 2.14/1.00    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.14/1.00    inference(ennf_transformation,[],[f10])).
% 2.14/1.00  
% 2.14/1.00  fof(f40,plain,(
% 2.14/1.00    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.14/1.00    inference(nnf_transformation,[],[f25])).
% 2.14/1.00  
% 2.14/1.00  fof(f68,plain,(
% 2.14/1.00    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.14/1.00    inference(cnf_transformation,[],[f40])).
% 2.14/1.00  
% 2.14/1.00  fof(f59,plain,(
% 2.14/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.14/1.00    inference(cnf_transformation,[],[f38])).
% 2.14/1.00  
% 2.14/1.00  fof(f16,conjecture,(
% 2.14/1.00    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 2.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.14/1.00  
% 2.14/1.00  fof(f17,negated_conjecture,(
% 2.14/1.00    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 2.14/1.00    inference(negated_conjecture,[],[f16])).
% 2.14/1.00  
% 2.14/1.00  fof(f36,plain,(
% 2.14/1.00    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.14/1.00    inference(ennf_transformation,[],[f17])).
% 2.14/1.00  
% 2.14/1.00  fof(f37,plain,(
% 2.14/1.00    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.14/1.00    inference(flattening,[],[f36])).
% 2.14/1.00  
% 2.14/1.00  fof(f50,plain,(
% 2.14/1.00    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.14/1.00    inference(nnf_transformation,[],[f37])).
% 2.14/1.00  
% 2.14/1.00  fof(f51,plain,(
% 2.14/1.00    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.14/1.00    inference(flattening,[],[f50])).
% 2.14/1.00  
% 2.14/1.00  fof(f53,plain,(
% 2.14/1.00    ( ! [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_subset_1(sK3,u1_struct_0(X0)) | ~v3_tex_2(sK3,X0)) & (~v1_subset_1(sK3,u1_struct_0(X0)) | v3_tex_2(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.14/1.00    introduced(choice_axiom,[])).
% 2.14/1.00  
% 2.14/1.00  fof(f52,plain,(
% 2.14/1.00    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK2)) | ~v3_tex_2(X1,sK2)) & (~v1_subset_1(X1,u1_struct_0(sK2)) | v3_tex_2(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v1_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.14/1.00    introduced(choice_axiom,[])).
% 2.14/1.00  
% 2.14/1.00  fof(f54,plain,(
% 2.14/1.00    ((v1_subset_1(sK3,u1_struct_0(sK2)) | ~v3_tex_2(sK3,sK2)) & (~v1_subset_1(sK3,u1_struct_0(sK2)) | v3_tex_2(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v1_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.14/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f51,f53,f52])).
% 2.14/1.00  
% 2.14/1.00  fof(f86,plain,(
% 2.14/1.00    ~v1_subset_1(sK3,u1_struct_0(sK2)) | v3_tex_2(sK3,sK2)),
% 2.14/1.00    inference(cnf_transformation,[],[f54])).
% 2.14/1.00  
% 2.14/1.00  fof(f85,plain,(
% 2.14/1.00    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 2.14/1.00    inference(cnf_transformation,[],[f54])).
% 2.14/1.00  
% 2.14/1.00  fof(f6,axiom,(
% 2.14/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.14/1.00  
% 2.14/1.00  fof(f19,plain,(
% 2.14/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.14/1.00    inference(ennf_transformation,[],[f6])).
% 2.14/1.00  
% 2.14/1.00  fof(f61,plain,(
% 2.14/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.14/1.00    inference(cnf_transformation,[],[f19])).
% 2.14/1.00  
% 2.14/1.00  fof(f5,axiom,(
% 2.14/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.14/1.00  
% 2.14/1.00  fof(f18,plain,(
% 2.14/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.14/1.00    inference(ennf_transformation,[],[f5])).
% 2.14/1.00  
% 2.14/1.00  fof(f60,plain,(
% 2.14/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.14/1.00    inference(cnf_transformation,[],[f18])).
% 2.14/1.00  
% 2.14/1.00  fof(f84,plain,(
% 2.14/1.00    l1_pre_topc(sK2)),
% 2.14/1.00    inference(cnf_transformation,[],[f54])).
% 2.14/1.00  
% 2.14/1.00  fof(f9,axiom,(
% 2.14/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 2.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.14/1.00  
% 2.14/1.00  fof(f24,plain,(
% 2.14/1.00    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.14/1.00    inference(ennf_transformation,[],[f9])).
% 2.14/1.00  
% 2.14/1.00  fof(f39,plain,(
% 2.14/1.00    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.14/1.00    inference(nnf_transformation,[],[f24])).
% 2.14/1.00  
% 2.14/1.00  fof(f65,plain,(
% 2.14/1.00    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.14/1.00    inference(cnf_transformation,[],[f39])).
% 2.14/1.00  
% 2.14/1.00  fof(f12,axiom,(
% 2.14/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 2.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.14/1.00  
% 2.14/1.00  fof(f28,plain,(
% 2.14/1.00    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.14/1.00    inference(ennf_transformation,[],[f12])).
% 2.14/1.00  
% 2.14/1.00  fof(f29,plain,(
% 2.14/1.00    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.14/1.00    inference(flattening,[],[f28])).
% 2.14/1.00  
% 2.14/1.00  fof(f46,plain,(
% 2.14/1.00    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.14/1.00    inference(nnf_transformation,[],[f29])).
% 2.14/1.00  
% 2.14/1.00  fof(f47,plain,(
% 2.14/1.00    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.14/1.00    inference(rectify,[],[f46])).
% 2.14/1.00  
% 2.14/1.00  fof(f48,plain,(
% 2.14/1.00    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.14/1.00    introduced(choice_axiom,[])).
% 2.14/1.00  
% 2.14/1.00  fof(f49,plain,(
% 2.14/1.00    ! [X0] : (((v1_tdlat_3(X0) | (~v3_pre_topc(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.14/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).
% 2.14/1.00  
% 2.14/1.00  fof(f75,plain,(
% 2.14/1.00    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.14/1.00    inference(cnf_transformation,[],[f49])).
% 2.14/1.00  
% 2.14/1.00  fof(f14,axiom,(
% 2.14/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 2.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.14/1.00  
% 2.14/1.00  fof(f32,plain,(
% 2.14/1.00    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.14/1.00    inference(ennf_transformation,[],[f14])).
% 2.14/1.00  
% 2.14/1.00  fof(f33,plain,(
% 2.14/1.00    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.14/1.00    inference(flattening,[],[f32])).
% 2.14/1.00  
% 2.14/1.00  fof(f79,plain,(
% 2.14/1.00    ( ! [X0,X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/1.00    inference(cnf_transformation,[],[f33])).
% 2.14/1.00  
% 2.14/1.00  fof(f81,plain,(
% 2.14/1.00    ~v2_struct_0(sK2)),
% 2.14/1.00    inference(cnf_transformation,[],[f54])).
% 2.14/1.00  
% 2.14/1.00  fof(f82,plain,(
% 2.14/1.00    v2_pre_topc(sK2)),
% 2.14/1.00    inference(cnf_transformation,[],[f54])).
% 2.14/1.00  
% 2.14/1.00  fof(f83,plain,(
% 2.14/1.00    v1_tdlat_3(sK2)),
% 2.14/1.00    inference(cnf_transformation,[],[f54])).
% 2.14/1.00  
% 2.14/1.00  fof(f2,axiom,(
% 2.14/1.00    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.14/1.00  
% 2.14/1.00  fof(f56,plain,(
% 2.14/1.00    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.14/1.00    inference(cnf_transformation,[],[f2])).
% 2.14/1.00  
% 2.14/1.00  fof(f1,axiom,(
% 2.14/1.00    ! [X0] : k2_subset_1(X0) = X0),
% 2.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.14/1.00  
% 2.14/1.00  fof(f55,plain,(
% 2.14/1.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.14/1.00    inference(cnf_transformation,[],[f1])).
% 2.14/1.00  
% 2.14/1.00  fof(f11,axiom,(
% 2.14/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 2.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.14/1.00  
% 2.14/1.00  fof(f26,plain,(
% 2.14/1.00    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.14/1.00    inference(ennf_transformation,[],[f11])).
% 2.14/1.00  
% 2.14/1.00  fof(f27,plain,(
% 2.14/1.00    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.14/1.00    inference(flattening,[],[f26])).
% 2.14/1.00  
% 2.14/1.00  fof(f41,plain,(
% 2.14/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.14/1.00    inference(nnf_transformation,[],[f27])).
% 2.14/1.00  
% 2.14/1.00  fof(f42,plain,(
% 2.14/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.14/1.00    inference(flattening,[],[f41])).
% 2.14/1.00  
% 2.14/1.00  fof(f43,plain,(
% 2.14/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.14/1.00    inference(rectify,[],[f42])).
% 2.14/1.00  
% 2.14/1.00  fof(f44,plain,(
% 2.14/1.00    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK0(X0,X1) != X1 & r1_tarski(X1,sK0(X0,X1)) & v2_tex_2(sK0(X0,X1),X0) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.14/1.00    introduced(choice_axiom,[])).
% 2.14/1.00  
% 2.14/1.00  fof(f45,plain,(
% 2.14/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK0(X0,X1) != X1 & r1_tarski(X1,sK0(X0,X1)) & v2_tex_2(sK0(X0,X1),X0) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.14/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 2.14/1.00  
% 2.14/1.00  fof(f70,plain,(
% 2.14/1.00    ( ! [X0,X3,X1] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.14/1.00    inference(cnf_transformation,[],[f45])).
% 2.14/1.00  
% 2.14/1.00  fof(f13,axiom,(
% 2.14/1.00    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 2.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.14/1.00  
% 2.14/1.00  fof(f30,plain,(
% 2.14/1.00    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.14/1.00    inference(ennf_transformation,[],[f13])).
% 2.14/1.00  
% 2.14/1.00  fof(f31,plain,(
% 2.14/1.00    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.14/1.00    inference(flattening,[],[f30])).
% 2.14/1.00  
% 2.14/1.00  fof(f78,plain,(
% 2.14/1.00    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/1.00    inference(cnf_transformation,[],[f31])).
% 2.14/1.00  
% 2.14/1.00  fof(f7,axiom,(
% 2.14/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 2.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.14/1.00  
% 2.14/1.00  fof(f20,plain,(
% 2.14/1.00    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.14/1.00    inference(ennf_transformation,[],[f7])).
% 2.14/1.00  
% 2.14/1.00  fof(f21,plain,(
% 2.14/1.00    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.14/1.00    inference(flattening,[],[f20])).
% 2.14/1.00  
% 2.14/1.00  fof(f62,plain,(
% 2.14/1.00    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.14/1.00    inference(cnf_transformation,[],[f21])).
% 2.14/1.00  
% 2.14/1.00  fof(f8,axiom,(
% 2.14/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.14/1.00  
% 2.14/1.00  fof(f22,plain,(
% 2.14/1.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.14/1.00    inference(ennf_transformation,[],[f8])).
% 2.14/1.00  
% 2.14/1.00  fof(f23,plain,(
% 2.14/1.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.14/1.00    inference(flattening,[],[f22])).
% 2.14/1.00  
% 2.14/1.00  fof(f63,plain,(
% 2.14/1.00    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.14/1.00    inference(cnf_transformation,[],[f23])).
% 2.14/1.00  
% 2.14/1.00  fof(f66,plain,(
% 2.14/1.00    ( ! [X0,X1] : (v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.14/1.00    inference(cnf_transformation,[],[f39])).
% 2.14/1.00  
% 2.14/1.00  fof(f15,axiom,(
% 2.14/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 2.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.14/1.00  
% 2.14/1.00  fof(f34,plain,(
% 2.14/1.00    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.14/1.00    inference(ennf_transformation,[],[f15])).
% 2.14/1.00  
% 2.14/1.00  fof(f35,plain,(
% 2.14/1.00    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.14/1.00    inference(flattening,[],[f34])).
% 2.14/1.00  
% 2.14/1.00  fof(f80,plain,(
% 2.14/1.00    ( ! [X0,X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/1.00    inference(cnf_transformation,[],[f35])).
% 2.14/1.00  
% 2.14/1.00  fof(f3,axiom,(
% 2.14/1.00    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 2.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.14/1.00  
% 2.14/1.00  fof(f57,plain,(
% 2.14/1.00    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 2.14/1.00    inference(cnf_transformation,[],[f3])).
% 2.14/1.00  
% 2.14/1.00  fof(f87,plain,(
% 2.14/1.00    v1_subset_1(sK3,u1_struct_0(sK2)) | ~v3_tex_2(sK3,sK2)),
% 2.14/1.00    inference(cnf_transformation,[],[f54])).
% 2.14/1.00  
% 2.14/1.00  cnf(c_4,plain,
% 2.14/1.00      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.14/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_247,plain,
% 2.14/1.00      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.14/1.00      inference(prop_impl,[status(thm)],[c_4]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_12,plain,
% 2.14/1.00      ( v1_subset_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | X0 = X1 ),
% 2.14/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_3,plain,
% 2.14/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.14/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_249,plain,
% 2.14/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.14/1.00      inference(prop_impl,[status(thm)],[c_3]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_313,plain,
% 2.14/1.00      ( ~ r1_tarski(X0,X1) | v1_subset_1(X0,X1) | X0 = X1 ),
% 2.14/1.00      inference(bin_hyper_res,[status(thm)],[c_12,c_249]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_27,negated_conjecture,
% 2.14/1.00      ( v3_tex_2(sK3,sK2) | ~ v1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.14/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_251,plain,
% 2.14/1.00      ( v3_tex_2(sK3,sK2) | ~ v1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.14/1.00      inference(prop_impl,[status(thm)],[c_27]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_493,plain,
% 2.14/1.00      ( v3_tex_2(sK3,sK2)
% 2.14/1.00      | ~ r1_tarski(X0,X1)
% 2.14/1.00      | X1 = X0
% 2.14/1.00      | u1_struct_0(sK2) != X1
% 2.14/1.00      | sK3 != X0 ),
% 2.14/1.00      inference(resolution_lifted,[status(thm)],[c_313,c_251]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_494,plain,
% 2.14/1.00      ( v3_tex_2(sK3,sK2)
% 2.14/1.00      | ~ r1_tarski(sK3,u1_struct_0(sK2))
% 2.14/1.00      | u1_struct_0(sK2) = sK3 ),
% 2.14/1.00      inference(unflattening,[status(thm)],[c_493]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_887,plain,
% 2.14/1.00      ( v3_tex_2(sK3,sK2)
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.14/1.00      | u1_struct_0(sK2) != X1
% 2.14/1.00      | u1_struct_0(sK2) = sK3
% 2.14/1.00      | sK3 != X0 ),
% 2.14/1.00      inference(resolution_lifted,[status(thm)],[c_247,c_494]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_888,plain,
% 2.14/1.00      ( v3_tex_2(sK3,sK2)
% 2.14/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.14/1.00      | u1_struct_0(sK2) = sK3 ),
% 2.14/1.00      inference(unflattening,[status(thm)],[c_887]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_28,negated_conjecture,
% 2.14/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.14/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_890,plain,
% 2.14/1.00      ( v3_tex_2(sK3,sK2) | u1_struct_0(sK2) = sK3 ),
% 2.14/1.00      inference(global_propositional_subsumption,[status(thm)],[c_888,c_28]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_1915,plain,
% 2.14/1.00      ( u1_struct_0(sK2) = sK3 | v3_tex_2(sK3,sK2) = iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_890]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_6,plain,
% 2.14/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.14/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_5,plain,
% 2.14/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.14/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_430,plain,
% 2.14/1.00      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.14/1.00      inference(resolution,[status(thm)],[c_6,c_5]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_29,negated_conjecture,
% 2.14/1.00      ( l1_pre_topc(sK2) ),
% 2.14/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_716,plain,
% 2.14/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK2 != X0 ),
% 2.14/1.00      inference(resolution_lifted,[status(thm)],[c_430,c_29]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_717,plain,
% 2.14/1.00      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 2.14/1.00      inference(unflattening,[status(thm)],[c_716]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_1936,plain,
% 2.14/1.00      ( k2_struct_0(sK2) = sK3 | v3_tex_2(sK3,sK2) = iProver_top ),
% 2.14/1.00      inference(demodulation,[status(thm)],[c_1915,c_717]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_1924,plain,
% 2.14/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_1930,plain,
% 2.14/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
% 2.14/1.00      inference(light_normalisation,[status(thm)],[c_1924,c_717]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_11,plain,
% 2.14/1.00      ( ~ v1_tops_1(X0,X1)
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
% 2.14/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_22,plain,
% 2.14/1.00      ( v3_pre_topc(X0,X1)
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.00      | ~ v1_tdlat_3(X1)
% 2.14/1.00      | ~ v2_pre_topc(X1)
% 2.14/1.00      | ~ l1_pre_topc(X1) ),
% 2.14/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_24,plain,
% 2.14/1.00      ( ~ v3_pre_topc(X0,X1)
% 2.14/1.00      | ~ v3_tex_2(X0,X1)
% 2.14/1.00      | v1_tops_1(X0,X1)
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.00      | v2_struct_0(X1)
% 2.14/1.00      | ~ v2_pre_topc(X1)
% 2.14/1.00      | ~ l1_pre_topc(X1) ),
% 2.14/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_533,plain,
% 2.14/1.00      ( ~ v3_tex_2(X0,X1)
% 2.14/1.00      | v1_tops_1(X0,X1)
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.00      | v2_struct_0(X1)
% 2.14/1.00      | ~ v1_tdlat_3(X1)
% 2.14/1.00      | ~ v2_pre_topc(X1)
% 2.14/1.00      | ~ l1_pre_topc(X1) ),
% 2.14/1.00      inference(resolution,[status(thm)],[c_22,c_24]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_32,negated_conjecture,
% 2.14/1.00      ( ~ v2_struct_0(sK2) ),
% 2.14/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_569,plain,
% 2.14/1.00      ( ~ v3_tex_2(X0,X1)
% 2.14/1.00      | v1_tops_1(X0,X1)
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.00      | ~ v1_tdlat_3(X1)
% 2.14/1.00      | ~ v2_pre_topc(X1)
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | sK2 != X1 ),
% 2.14/1.00      inference(resolution_lifted,[status(thm)],[c_533,c_32]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_570,plain,
% 2.14/1.00      ( ~ v3_tex_2(X0,sK2)
% 2.14/1.00      | v1_tops_1(X0,sK2)
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.14/1.00      | ~ v1_tdlat_3(sK2)
% 2.14/1.00      | ~ v2_pre_topc(sK2)
% 2.14/1.00      | ~ l1_pre_topc(sK2) ),
% 2.14/1.00      inference(unflattening,[status(thm)],[c_569]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_31,negated_conjecture,
% 2.14/1.00      ( v2_pre_topc(sK2) ),
% 2.14/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_30,negated_conjecture,
% 2.14/1.00      ( v1_tdlat_3(sK2) ),
% 2.14/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_574,plain,
% 2.14/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.14/1.00      | v1_tops_1(X0,sK2)
% 2.14/1.00      | ~ v3_tex_2(X0,sK2) ),
% 2.14/1.00      inference(global_propositional_subsumption,
% 2.14/1.00                [status(thm)],
% 2.14/1.00                [c_570,c_31,c_30,c_29]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_575,plain,
% 2.14/1.00      ( ~ v3_tex_2(X0,sK2)
% 2.14/1.00      | v1_tops_1(X0,sK2)
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.14/1.00      inference(renaming,[status(thm)],[c_574]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_687,plain,
% 2.14/1.00      ( ~ v3_tex_2(X0,sK2)
% 2.14/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.14/1.00      | ~ l1_pre_topc(X2)
% 2.14/1.00      | X0 != X1
% 2.14/1.00      | k2_pre_topc(X2,X1) = u1_struct_0(X2)
% 2.14/1.00      | sK2 != X2 ),
% 2.14/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_575]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_688,plain,
% 2.14/1.00      ( ~ v3_tex_2(X0,sK2)
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.14/1.00      | ~ l1_pre_topc(sK2)
% 2.14/1.00      | k2_pre_topc(sK2,X0) = u1_struct_0(sK2) ),
% 2.14/1.00      inference(unflattening,[status(thm)],[c_687]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_692,plain,
% 2.14/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.14/1.00      | ~ v3_tex_2(X0,sK2)
% 2.14/1.00      | k2_pre_topc(sK2,X0) = u1_struct_0(sK2) ),
% 2.14/1.00      inference(global_propositional_subsumption,[status(thm)],[c_688,c_29]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_693,plain,
% 2.14/1.00      ( ~ v3_tex_2(X0,sK2)
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.14/1.00      | k2_pre_topc(sK2,X0) = u1_struct_0(sK2) ),
% 2.14/1.00      inference(renaming,[status(thm)],[c_692]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_1919,plain,
% 2.14/1.00      ( k2_pre_topc(sK2,X0) = u1_struct_0(sK2)
% 2.14/1.00      | v3_tex_2(X0,sK2) != iProver_top
% 2.14/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_693]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_1959,plain,
% 2.14/1.00      ( k2_pre_topc(sK2,X0) = k2_struct_0(sK2)
% 2.14/1.00      | v3_tex_2(X0,sK2) != iProver_top
% 2.14/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 2.14/1.00      inference(light_normalisation,[status(thm)],[c_1919,c_717]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2097,plain,
% 2.14/1.00      ( k2_pre_topc(sK2,sK3) = k2_struct_0(sK2)
% 2.14/1.00      | v3_tex_2(sK3,sK2) != iProver_top ),
% 2.14/1.00      inference(superposition,[status(thm)],[c_1930,c_1959]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2534,plain,
% 2.14/1.00      ( k2_pre_topc(sK2,sK3) = k2_struct_0(sK2) | k2_struct_0(sK2) = sK3 ),
% 2.14/1.00      inference(superposition,[status(thm)],[c_1936,c_2097]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_1,plain,
% 2.14/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.14/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_1925,plain,
% 2.14/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_0,plain,
% 2.14/1.00      ( k2_subset_1(X0) = X0 ),
% 2.14/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_1933,plain,
% 2.14/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.14/1.00      inference(light_normalisation,[status(thm)],[c_1925,c_0]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_18,plain,
% 2.14/1.00      ( ~ v2_tex_2(X0,X1)
% 2.14/1.00      | ~ v3_tex_2(X2,X1)
% 2.14/1.00      | ~ r1_tarski(X2,X0)
% 2.14/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | X0 = X2 ),
% 2.14/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_730,plain,
% 2.14/1.00      ( ~ v2_tex_2(X0,X1)
% 2.14/1.00      | ~ v3_tex_2(X2,X1)
% 2.14/1.00      | ~ r1_tarski(X2,X0)
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.00      | X2 = X0
% 2.14/1.00      | sK2 != X1 ),
% 2.14/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_731,plain,
% 2.14/1.00      ( ~ v2_tex_2(X0,sK2)
% 2.14/1.00      | ~ v3_tex_2(X1,sK2)
% 2.14/1.00      | ~ r1_tarski(X1,X0)
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.14/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.14/1.00      | X1 = X0 ),
% 2.14/1.00      inference(unflattening,[status(thm)],[c_730]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_23,plain,
% 2.14/1.00      ( v2_tex_2(X0,X1)
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.00      | v2_struct_0(X1)
% 2.14/1.00      | ~ v1_tdlat_3(X1)
% 2.14/1.00      | ~ v2_pre_topc(X1)
% 2.14/1.00      | ~ l1_pre_topc(X1) ),
% 2.14/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_614,plain,
% 2.14/1.00      ( v2_tex_2(X0,X1)
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.00      | ~ v1_tdlat_3(X1)
% 2.14/1.00      | ~ v2_pre_topc(X1)
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | sK2 != X1 ),
% 2.14/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_32]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_615,plain,
% 2.14/1.00      ( v2_tex_2(X0,sK2)
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.14/1.00      | ~ v1_tdlat_3(sK2)
% 2.14/1.00      | ~ v2_pre_topc(sK2)
% 2.14/1.00      | ~ l1_pre_topc(sK2) ),
% 2.14/1.00      inference(unflattening,[status(thm)],[c_614]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_735,plain,
% 2.14/1.00      ( ~ v3_tex_2(X1,sK2)
% 2.14/1.00      | ~ r1_tarski(X1,X0)
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.14/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.14/1.00      | X1 = X0 ),
% 2.14/1.00      inference(global_propositional_subsumption,
% 2.14/1.00                [status(thm)],
% 2.14/1.00                [c_731,c_31,c_30,c_29,c_615]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_736,plain,
% 2.14/1.00      ( ~ v3_tex_2(X0,sK2)
% 2.14/1.00      | ~ r1_tarski(X0,X1)
% 2.14/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.14/1.00      | X0 = X1 ),
% 2.14/1.00      inference(renaming,[status(thm)],[c_735]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_864,plain,
% 2.14/1.00      ( ~ v3_tex_2(X0,sK2)
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.14/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.14/1.00      | X1 = X0 ),
% 2.14/1.00      inference(resolution,[status(thm)],[c_247,c_736]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_1916,plain,
% 2.14/1.00      ( X0 = X1
% 2.14/1.00      | v3_tex_2(X1,sK2) != iProver_top
% 2.14/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 2.14/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.14/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_864]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_1988,plain,
% 2.14/1.00      ( X0 = X1
% 2.14/1.00      | v3_tex_2(X0,sK2) != iProver_top
% 2.14/1.00      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.14/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.14/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 2.14/1.00      inference(light_normalisation,[status(thm)],[c_1916,c_717]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2172,plain,
% 2.14/1.00      ( sK3 = X0
% 2.14/1.00      | v3_tex_2(sK3,sK2) != iProver_top
% 2.14/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.14/1.00      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
% 2.14/1.00      inference(superposition,[status(thm)],[c_1930,c_1988]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2632,plain,
% 2.14/1.00      ( k2_struct_0(sK2) = sK3
% 2.14/1.00      | v3_tex_2(sK3,sK2) != iProver_top
% 2.14/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 2.14/1.00      inference(superposition,[status(thm)],[c_1933,c_2172]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2675,plain,
% 2.14/1.00      ( k2_struct_0(sK2) = sK3 ),
% 2.14/1.00      inference(global_propositional_subsumption,
% 2.14/1.00                [status(thm)],
% 2.14/1.00                [c_2534,c_1936,c_1930,c_2632]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_7,plain,
% 2.14/1.00      ( v4_pre_topc(k2_struct_0(X0),X0)
% 2.14/1.00      | ~ v2_pre_topc(X0)
% 2.14/1.00      | ~ l1_pre_topc(X0) ),
% 2.14/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_9,plain,
% 2.14/1.00      ( ~ v4_pre_topc(X0,X1)
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | k2_pre_topc(X1,X0) = X0 ),
% 2.14/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_445,plain,
% 2.14/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.00      | ~ v2_pre_topc(X2)
% 2.14/1.00      | ~ l1_pre_topc(X2)
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | X1 != X2
% 2.14/1.00      | k2_pre_topc(X1,X0) = X0
% 2.14/1.00      | k2_struct_0(X2) != X0 ),
% 2.14/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_9]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_446,plain,
% 2.14/1.00      ( ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.14/1.00      | ~ v2_pre_topc(X0)
% 2.14/1.00      | ~ l1_pre_topc(X0)
% 2.14/1.00      | k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
% 2.14/1.00      inference(unflattening,[status(thm)],[c_445]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_647,plain,
% 2.14/1.00      ( ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.14/1.00      | ~ l1_pre_topc(X0)
% 2.14/1.00      | k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0)
% 2.14/1.00      | sK2 != X0 ),
% 2.14/1.00      inference(resolution_lifted,[status(thm)],[c_446,c_31]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_648,plain,
% 2.14/1.00      ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.14/1.00      | ~ l1_pre_topc(sK2)
% 2.14/1.00      | k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2) ),
% 2.14/1.00      inference(unflattening,[status(thm)],[c_647]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_650,plain,
% 2.14/1.00      ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.14/1.00      | k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2) ),
% 2.14/1.00      inference(global_propositional_subsumption,[status(thm)],[c_648,c_29]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_1921,plain,
% 2.14/1.00      ( k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2)
% 2.14/1.00      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_650]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_1947,plain,
% 2.14/1.00      ( k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2)
% 2.14/1.00      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 2.14/1.00      inference(light_normalisation,[status(thm)],[c_1921,c_717]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_1950,plain,
% 2.14/1.00      ( k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2) ),
% 2.14/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_1947,c_1933]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_10,plain,
% 2.14/1.00      ( v1_tops_1(X0,X1)
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | k2_pre_topc(X1,X0) != u1_struct_0(X1) ),
% 2.14/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_619,plain,
% 2.14/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | v2_tex_2(X0,sK2) ),
% 2.14/1.00      inference(global_propositional_subsumption,
% 2.14/1.00                [status(thm)],
% 2.14/1.00                [c_615,c_31,c_30,c_29]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_620,plain,
% 2.14/1.00      ( v2_tex_2(X0,sK2) | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.14/1.00      inference(renaming,[status(thm)],[c_619]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_25,plain,
% 2.14/1.00      ( ~ v2_tex_2(X0,X1)
% 2.14/1.00      | v3_tex_2(X0,X1)
% 2.14/1.00      | ~ v1_tops_1(X0,X1)
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.00      | v2_struct_0(X1)
% 2.14/1.00      | ~ v2_pre_topc(X1)
% 2.14/1.00      | ~ l1_pre_topc(X1) ),
% 2.14/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_590,plain,
% 2.14/1.00      ( ~ v2_tex_2(X0,X1)
% 2.14/1.00      | v3_tex_2(X0,X1)
% 2.14/1.00      | ~ v1_tops_1(X0,X1)
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.00      | ~ v2_pre_topc(X1)
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | sK2 != X1 ),
% 2.14/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_32]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_591,plain,
% 2.14/1.00      ( ~ v2_tex_2(X0,sK2)
% 2.14/1.00      | v3_tex_2(X0,sK2)
% 2.14/1.00      | ~ v1_tops_1(X0,sK2)
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.14/1.00      | ~ v2_pre_topc(sK2)
% 2.14/1.00      | ~ l1_pre_topc(sK2) ),
% 2.14/1.00      inference(unflattening,[status(thm)],[c_590]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_595,plain,
% 2.14/1.00      ( ~ v2_tex_2(X0,sK2)
% 2.14/1.00      | v3_tex_2(X0,sK2)
% 2.14/1.00      | ~ v1_tops_1(X0,sK2)
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.14/1.00      inference(global_propositional_subsumption,
% 2.14/1.00                [status(thm)],
% 2.14/1.00                [c_591,c_31,c_29]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_630,plain,
% 2.14/1.00      ( v3_tex_2(X0,sK2)
% 2.14/1.00      | ~ v1_tops_1(X0,sK2)
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.14/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_620,c_595]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_666,plain,
% 2.14/1.00      ( v3_tex_2(X0,sK2)
% 2.14/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.14/1.00      | ~ l1_pre_topc(X2)
% 2.14/1.00      | X0 != X1
% 2.14/1.00      | k2_pre_topc(X2,X1) != u1_struct_0(X2)
% 2.14/1.00      | sK2 != X2 ),
% 2.14/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_630]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_667,plain,
% 2.14/1.00      ( v3_tex_2(X0,sK2)
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.14/1.00      | ~ l1_pre_topc(sK2)
% 2.14/1.00      | k2_pre_topc(sK2,X0) != u1_struct_0(sK2) ),
% 2.14/1.00      inference(unflattening,[status(thm)],[c_666]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_671,plain,
% 2.14/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.14/1.00      | v3_tex_2(X0,sK2)
% 2.14/1.00      | k2_pre_topc(sK2,X0) != u1_struct_0(sK2) ),
% 2.14/1.00      inference(global_propositional_subsumption,[status(thm)],[c_667,c_29]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_672,plain,
% 2.14/1.00      ( v3_tex_2(X0,sK2)
% 2.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.14/1.00      | k2_pre_topc(sK2,X0) != u1_struct_0(sK2) ),
% 2.14/1.00      inference(renaming,[status(thm)],[c_671]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_1920,plain,
% 2.14/1.00      ( k2_pre_topc(sK2,X0) != u1_struct_0(sK2)
% 2.14/1.00      | v3_tex_2(X0,sK2) = iProver_top
% 2.14/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_672]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_1966,plain,
% 2.14/1.00      ( k2_pre_topc(sK2,X0) != k2_struct_0(sK2)
% 2.14/1.00      | v3_tex_2(X0,sK2) = iProver_top
% 2.14/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 2.14/1.00      inference(light_normalisation,[status(thm)],[c_1920,c_717]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2365,plain,
% 2.14/1.00      ( v3_tex_2(k2_struct_0(sK2),sK2) = iProver_top
% 2.14/1.00      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 2.14/1.00      inference(superposition,[status(thm)],[c_1950,c_1966]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2538,plain,
% 2.14/1.00      ( v3_tex_2(k2_struct_0(sK2),sK2) = iProver_top ),
% 2.14/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_2365,c_1933]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2679,plain,
% 2.14/1.00      ( v3_tex_2(sK3,sK2) = iProver_top ),
% 2.14/1.00      inference(demodulation,[status(thm)],[c_2675,c_2538]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2,plain,
% 2.14/1.00      ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
% 2.14/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_26,negated_conjecture,
% 2.14/1.00      ( ~ v3_tex_2(sK3,sK2) | v1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.14/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_253,plain,
% 2.14/1.00      ( ~ v3_tex_2(sK3,sK2) | v1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.14/1.00      inference(prop_impl,[status(thm)],[c_26]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_481,plain,
% 2.14/1.00      ( ~ v3_tex_2(sK3,sK2) | u1_struct_0(sK2) != X0 | k2_subset_1(X0) != sK3 ),
% 2.14/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_253]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_482,plain,
% 2.14/1.00      ( ~ v3_tex_2(sK3,sK2) | k2_subset_1(u1_struct_0(sK2)) != sK3 ),
% 2.14/1.00      inference(unflattening,[status(thm)],[c_481]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_1923,plain,
% 2.14/1.00      ( k2_subset_1(u1_struct_0(sK2)) != sK3
% 2.14/1.00      | v3_tex_2(sK3,sK2) != iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_482]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_1941,plain,
% 2.14/1.00      ( k2_subset_1(k2_struct_0(sK2)) != sK3
% 2.14/1.00      | v3_tex_2(sK3,sK2) != iProver_top ),
% 2.14/1.00      inference(light_normalisation,[status(thm)],[c_1923,c_717]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_1942,plain,
% 2.14/1.00      ( k2_struct_0(sK2) != sK3 | v3_tex_2(sK3,sK2) != iProver_top ),
% 2.14/1.00      inference(demodulation,[status(thm)],[c_1941,c_0]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2684,plain,
% 2.14/1.00      ( sK3 != sK3 | v3_tex_2(sK3,sK2) != iProver_top ),
% 2.14/1.00      inference(demodulation,[status(thm)],[c_2675,c_1942]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2729,plain,
% 2.14/1.00      ( v3_tex_2(sK3,sK2) != iProver_top ),
% 2.14/1.00      inference(equality_resolution_simp,[status(thm)],[c_2684]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2741,plain,
% 2.14/1.00      ( $false ),
% 2.14/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_2679,c_2729]) ).
% 2.14/1.00  
% 2.14/1.00  
% 2.14/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.14/1.00  
% 2.14/1.00  ------                               Statistics
% 2.14/1.00  
% 2.14/1.00  ------ General
% 2.14/1.00  
% 2.14/1.00  abstr_ref_over_cycles:                  0
% 2.14/1.00  abstr_ref_under_cycles:                 0
% 2.14/1.00  gc_basic_clause_elim:                   0
% 2.14/1.00  forced_gc_time:                         0
% 2.14/1.00  parsing_time:                           0.012
% 2.14/1.00  unif_index_cands_time:                  0.
% 2.14/1.00  unif_index_add_time:                    0.
% 2.14/1.00  orderings_time:                         0.
% 2.14/1.00  out_proof_time:                         0.016
% 2.14/1.00  total_time:                             0.119
% 2.14/1.00  num_of_symbols:                         53
% 2.14/1.00  num_of_terms:                           1431
% 2.14/1.00  
% 2.14/1.00  ------ Preprocessing
% 2.14/1.00  
% 2.14/1.00  num_of_splits:                          0
% 2.14/1.00  num_of_split_atoms:                     0
% 2.14/1.00  num_of_reused_defs:                     0
% 2.14/1.00  num_eq_ax_congr_red:                    16
% 2.14/1.00  num_of_sem_filtered_clauses:            1
% 2.14/1.00  num_of_subtypes:                        0
% 2.14/1.00  monotx_restored_types:                  0
% 2.14/1.00  sat_num_of_epr_types:                   0
% 2.14/1.00  sat_num_of_non_cyclic_types:            0
% 2.14/1.00  sat_guarded_non_collapsed_types:        0
% 2.14/1.00  num_pure_diseq_elim:                    0
% 2.14/1.00  simp_replaced_by:                       0
% 2.14/1.00  res_preprocessed:                       96
% 2.14/1.00  prep_upred:                             0
% 2.14/1.00  prep_unflattend:                        57
% 2.14/1.00  smt_new_axioms:                         0
% 2.14/1.00  pred_elim_cands:                        2
% 2.14/1.00  pred_elim:                              11
% 2.14/1.00  pred_elim_cl:                           19
% 2.14/1.00  pred_elim_cycles:                       13
% 2.14/1.00  merged_defs:                            4
% 2.14/1.00  merged_defs_ncl:                        0
% 2.14/1.00  bin_hyper_res:                          5
% 2.14/1.00  prep_cycles:                            4
% 2.14/1.00  pred_elim_time:                         0.019
% 2.14/1.00  splitting_time:                         0.
% 2.14/1.00  sem_filter_time:                        0.
% 2.14/1.00  monotx_time:                            0.
% 2.14/1.00  subtype_inf_time:                       0.
% 2.14/1.00  
% 2.14/1.00  ------ Problem properties
% 2.14/1.00  
% 2.14/1.00  clauses:                                14
% 2.14/1.00  conjectures:                            1
% 2.14/1.00  epr:                                    0
% 2.14/1.00  horn:                                   11
% 2.14/1.00  ground:                                 6
% 2.14/1.00  unary:                                  4
% 2.14/1.00  binary:                                 3
% 2.14/1.00  lits:                                   33
% 2.14/1.00  lits_eq:                                10
% 2.14/1.00  fd_pure:                                0
% 2.14/1.00  fd_pseudo:                              0
% 2.14/1.00  fd_cond:                                0
% 2.14/1.00  fd_pseudo_cond:                         1
% 2.14/1.00  ac_symbols:                             0
% 2.14/1.00  
% 2.14/1.00  ------ Propositional Solver
% 2.14/1.00  
% 2.14/1.00  prop_solver_calls:                      24
% 2.14/1.00  prop_fast_solver_calls:                 890
% 2.14/1.00  smt_solver_calls:                       0
% 2.14/1.00  smt_fast_solver_calls:                  0
% 2.14/1.00  prop_num_of_clauses:                    684
% 2.14/1.00  prop_preprocess_simplified:             2958
% 2.14/1.00  prop_fo_subsumed:                       42
% 2.14/1.00  prop_solver_time:                       0.
% 2.14/1.00  smt_solver_time:                        0.
% 2.14/1.00  smt_fast_solver_time:                   0.
% 2.14/1.00  prop_fast_solver_time:                  0.
% 2.14/1.00  prop_unsat_core_time:                   0.
% 2.14/1.00  
% 2.14/1.00  ------ QBF
% 2.14/1.00  
% 2.14/1.00  qbf_q_res:                              0
% 2.14/1.00  qbf_num_tautologies:                    0
% 2.14/1.00  qbf_prep_cycles:                        0
% 2.14/1.00  
% 2.14/1.00  ------ BMC1
% 2.14/1.00  
% 2.14/1.00  bmc1_current_bound:                     -1
% 2.14/1.00  bmc1_last_solved_bound:                 -1
% 2.14/1.00  bmc1_unsat_core_size:                   -1
% 2.14/1.00  bmc1_unsat_core_parents_size:           -1
% 2.14/1.00  bmc1_merge_next_fun:                    0
% 2.14/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.14/1.00  
% 2.14/1.00  ------ Instantiation
% 2.14/1.00  
% 2.14/1.00  inst_num_of_clauses:                    137
% 2.14/1.00  inst_num_in_passive:                    31
% 2.14/1.00  inst_num_in_active:                     79
% 2.14/1.00  inst_num_in_unprocessed:                27
% 2.14/1.00  inst_num_of_loops:                      100
% 2.14/1.00  inst_num_of_learning_restarts:          0
% 2.14/1.00  inst_num_moves_active_passive:          19
% 2.14/1.00  inst_lit_activity:                      0
% 2.14/1.00  inst_lit_activity_moves:                0
% 2.14/1.00  inst_num_tautologies:                   0
% 2.14/1.00  inst_num_prop_implied:                  0
% 2.14/1.00  inst_num_existing_simplified:           0
% 2.14/1.00  inst_num_eq_res_simplified:             0
% 2.14/1.00  inst_num_child_elim:                    0
% 2.14/1.00  inst_num_of_dismatching_blockings:      21
% 2.14/1.00  inst_num_of_non_proper_insts:           119
% 2.14/1.00  inst_num_of_duplicates:                 0
% 2.14/1.00  inst_inst_num_from_inst_to_res:         0
% 2.14/1.00  inst_dismatching_checking_time:         0.
% 2.14/1.00  
% 2.14/1.00  ------ Resolution
% 2.14/1.00  
% 2.14/1.00  res_num_of_clauses:                     0
% 2.14/1.00  res_num_in_passive:                     0
% 2.14/1.00  res_num_in_active:                      0
% 2.14/1.00  res_num_of_loops:                       100
% 2.14/1.00  res_forward_subset_subsumed:            7
% 2.14/1.00  res_backward_subset_subsumed:           0
% 2.14/1.00  res_forward_subsumed:                   3
% 2.14/1.00  res_backward_subsumed:                  0
% 2.14/1.00  res_forward_subsumption_resolution:     0
% 2.14/1.00  res_backward_subsumption_resolution:    1
% 2.14/1.00  res_clause_to_clause_subsumption:       110
% 2.14/1.00  res_orphan_elimination:                 0
% 2.14/1.00  res_tautology_del:                      25
% 2.14/1.00  res_num_eq_res_simplified:              0
% 2.14/1.00  res_num_sel_changes:                    0
% 2.14/1.00  res_moves_from_active_to_pass:          0
% 2.14/1.00  
% 2.14/1.00  ------ Superposition
% 2.14/1.00  
% 2.14/1.00  sup_time_total:                         0.
% 2.14/1.00  sup_time_generating:                    0.
% 2.14/1.00  sup_time_sim_full:                      0.
% 2.14/1.00  sup_time_sim_immed:                     0.
% 2.14/1.00  
% 2.14/1.00  sup_num_of_clauses:                     7
% 2.14/1.00  sup_num_in_active:                      2
% 2.14/1.00  sup_num_in_passive:                     5
% 2.14/1.00  sup_num_of_loops:                       18
% 2.14/1.00  sup_fw_superposition:                   8
% 2.14/1.00  sup_bw_superposition:                   6
% 2.14/1.00  sup_immediate_simplified:               1
% 2.14/1.00  sup_given_eliminated:                   0
% 2.14/1.00  comparisons_done:                       0
% 2.14/1.00  comparisons_avoided:                    0
% 2.14/1.00  
% 2.14/1.00  ------ Simplifications
% 2.14/1.00  
% 2.14/1.00  
% 2.14/1.00  sim_fw_subset_subsumed:                 3
% 2.14/1.00  sim_bw_subset_subsumed:                 3
% 2.14/1.00  sim_fw_subsumed:                        2
% 2.14/1.00  sim_bw_subsumed:                        0
% 2.14/1.00  sim_fw_subsumption_res:                 3
% 2.14/1.00  sim_bw_subsumption_res:                 0
% 2.14/1.00  sim_tautology_del:                      0
% 2.14/1.00  sim_eq_tautology_del:                   2
% 2.14/1.00  sim_eq_res_simp:                        1
% 2.14/1.00  sim_fw_demodulated:                     2
% 2.14/1.00  sim_bw_demodulated:                     14
% 2.14/1.00  sim_light_normalised:                   11
% 2.14/1.00  sim_joinable_taut:                      0
% 2.14/1.00  sim_joinable_simp:                      0
% 2.14/1.00  sim_ac_normalised:                      0
% 2.14/1.00  sim_smt_subsumption:                    0
% 2.14/1.00  
%------------------------------------------------------------------------------
