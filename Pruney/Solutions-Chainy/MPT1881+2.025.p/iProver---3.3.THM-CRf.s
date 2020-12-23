%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:15 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :  157 (1251 expanded)
%              Number of clauses        :   96 ( 367 expanded)
%              Number of leaves         :   18 ( 272 expanded)
%              Depth                    :   26
%              Number of atoms          :  582 (6985 expanded)
%              Number of equality atoms :  152 ( 396 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( v1_subset_1(sK2,u1_struct_0(X0))
          | ~ v3_tex_2(sK2,X0) )
        & ( ~ v1_subset_1(sK2,u1_struct_0(X0))
          | v3_tex_2(sK2,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
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
          ( ( v1_subset_1(X1,u1_struct_0(sK1))
            | ~ v3_tex_2(X1,sK1) )
          & ( ~ v1_subset_1(X1,u1_struct_0(sK1))
            | v3_tex_2(X1,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v1_tdlat_3(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( v1_subset_1(sK2,u1_struct_0(sK1))
      | ~ v3_tex_2(sK2,sK1) )
    & ( ~ v1_subset_1(sK2,u1_struct_0(sK1))
      | v3_tex_2(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v1_tdlat_3(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f42,f44,f43])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f71,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,(
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

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f69,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    ~ v2_struct_0(sK1) ),
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

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f70,plain,(
    v1_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f25])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( X1 = X3
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f73,plain,
    ( ~ v1_subset_1(sK2,u1_struct_0(sK1))
    | v3_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f74,plain,
    ( v1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v3_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1863,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_219,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_6,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_7,plain,
    ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_382,plain,
    ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_6,c_7])).

cnf(c_12,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_221,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_278,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_subset_1(X0,X1)
    | X0 = X1 ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_221])).

cnf(c_507,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ l1_pre_topc(X2)
    | X1 = X0
    | u1_struct_0(X2) != X1
    | k2_struct_0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_382,c_278])).

cnf(c_508,plain,
    ( ~ r1_tarski(k2_struct_0(X0),u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_507])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_603,plain,
    ( ~ r1_tarski(k2_struct_0(X0),u1_struct_0(X0))
    | u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_508,c_25])).

cnf(c_604,plain,
    ( ~ r1_tarski(k2_struct_0(sK1),u1_struct_0(sK1))
    | u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_603])).

cnf(c_814,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | u1_struct_0(sK1) != X1
    | u1_struct_0(sK1) = k2_struct_0(sK1)
    | k2_struct_0(sK1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_219,c_604])).

cnf(c_815,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_814])).

cnf(c_80,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_83,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_817,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_815,c_25,c_80,c_83])).

cnf(c_1871,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1863,c_817])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1864,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1874,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1864,c_0])).

cnf(c_8,plain,
    ( ~ l1_pre_topc(X0)
    | k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_620,plain,
    ( k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_25])).

cnf(c_621,plain,
    ( k2_pre_topc(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_620])).

cnf(c_10,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_21,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_433,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_434,plain,
    ( ~ v2_tex_2(X0,sK1)
    | v3_tex_2(X0,sK1)
    | ~ v1_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_20,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_26,negated_conjecture,
    ( v1_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_412,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_26])).

cnf(c_413,plain,
    ( v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_417,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_413,c_28,c_27,c_25])).

cnf(c_418,plain,
    ( v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_417])).

cnf(c_438,plain,
    ( v3_tex_2(X0,sK1)
    | ~ v1_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_434,c_28,c_25,c_418])).

cnf(c_459,plain,
    ( v3_tex_2(X0,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X2)
    | X0 != X1
    | k2_pre_topc(X2,X1) != u1_struct_0(X2)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_438])).

cnf(c_460,plain,
    ( v3_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k2_pre_topc(sK1,X0) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_464,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_tex_2(X0,sK1)
    | k2_pre_topc(sK1,X0) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_460,c_25])).

cnf(c_465,plain,
    ( v3_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_464])).

cnf(c_1862,plain,
    ( k2_pre_topc(sK1,X0) != u1_struct_0(sK1)
    | v3_tex_2(X0,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_465])).

cnf(c_1897,plain,
    ( k2_pre_topc(sK1,X0) != k2_struct_0(sK1)
    | v3_tex_2(X0,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1862,c_817])).

cnf(c_2118,plain,
    ( v3_tex_2(k2_struct_0(sK1),sK1) = iProver_top
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_621,c_1897])).

cnf(c_2221,plain,
    ( v3_tex_2(k2_struct_0(sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1874,c_2118])).

cnf(c_18,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_634,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | X2 = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_635,plain,
    ( ~ v2_tex_2(X0,sK1)
    | ~ v3_tex_2(X1,sK1)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_634])).

cnf(c_639,plain,
    ( ~ v3_tex_2(X1,sK1)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | X1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_635,c_28,c_27,c_25,c_413])).

cnf(c_640,plain,
    ( ~ v3_tex_2(X0,sK1)
    | ~ r1_tarski(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | X0 = X1 ),
    inference(renaming,[status(thm)],[c_639])).

cnf(c_777,plain,
    ( ~ v3_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_219,c_640])).

cnf(c_1856,plain,
    ( X0 = X1
    | v3_tex_2(X1,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_777])).

cnf(c_1918,plain,
    ( X0 = X1
    | v3_tex_2(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1856,c_817])).

cnf(c_2222,plain,
    ( k2_struct_0(sK1) = X0
    | v3_tex_2(k2_struct_0(sK1),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1874,c_1918])).

cnf(c_2233,plain,
    ( k2_struct_0(sK1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(X0)) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2221,c_2222])).

cnf(c_2313,plain,
    ( k2_struct_0(sK1) = sK2
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1871,c_2233])).

cnf(c_23,negated_conjecture,
    ( v3_tex_2(sK2,sK1)
    | ~ v1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_223,plain,
    ( v3_tex_2(sK2,sK1)
    | ~ v1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(prop_impl,[status(thm)],[c_23])).

cnf(c_541,plain,
    ( v3_tex_2(sK2,sK1)
    | ~ r1_tarski(X0,X1)
    | X1 = X0
    | u1_struct_0(sK1) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_278,c_223])).

cnf(c_542,plain,
    ( v3_tex_2(sK2,sK1)
    | ~ r1_tarski(sK2,u1_struct_0(sK1))
    | u1_struct_0(sK1) = sK2 ),
    inference(unflattening,[status(thm)],[c_541])).

cnf(c_800,plain,
    ( v3_tex_2(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | u1_struct_0(sK1) != X1
    | u1_struct_0(sK1) = sK2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_219,c_542])).

cnf(c_801,plain,
    ( v3_tex_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(sK1) = sK2 ),
    inference(unflattening,[status(thm)],[c_800])).

cnf(c_803,plain,
    ( v3_tex_2(sK2,sK1)
    | u1_struct_0(sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_801,c_24])).

cnf(c_1855,plain,
    ( u1_struct_0(sK1) = sK2
    | v3_tex_2(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_803])).

cnf(c_1878,plain,
    ( k2_struct_0(sK1) = sK2
    | v3_tex_2(sK2,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1855,c_817])).

cnf(c_22,negated_conjecture,
    ( ~ v3_tex_2(sK2,sK1)
    | v1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_225,plain,
    ( ~ v3_tex_2(sK2,sK1)
    | v1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(prop_impl,[status(thm)],[c_22])).

cnf(c_522,plain,
    ( ~ v3_tex_2(sK2,sK1)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | k2_struct_0(X0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_382,c_225])).

cnf(c_590,plain,
    ( ~ v3_tex_2(sK2,sK1)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | k2_struct_0(X0) != sK2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_522,c_25])).

cnf(c_591,plain,
    ( ~ v3_tex_2(sK2,sK1)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_struct_0(sK1) != sK2 ),
    inference(unflattening,[status(thm)],[c_590])).

cnf(c_1232,plain,
    ( ~ v3_tex_2(sK2,sK1)
    | k2_struct_0(sK1) != sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_591])).

cnf(c_1853,plain,
    ( k2_struct_0(sK1) != sK2
    | v3_tex_2(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1232])).

cnf(c_32,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_33,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_79,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_81,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_struct_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(c_82,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_84,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | l1_struct_0(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_82])).

cnf(c_523,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | k2_struct_0(X0) != sK2
    | v3_tex_2(sK2,sK1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_522])).

cnf(c_525,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_struct_0(sK1) != sK2
    | v3_tex_2(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_523])).

cnf(c_1639,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_1647,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1639])).

cnf(c_1633,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1652,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1633])).

cnf(c_1986,plain,
    ( ~ v3_tex_2(sK2,sK1)
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1)))
    | k2_struct_0(sK1) = sK2 ),
    inference(instantiation,[status(thm)],[c_777])).

cnf(c_1987,plain,
    ( k2_struct_0(sK1) = sK2
    | v3_tex_2(sK2,sK1) != iProver_top
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1986])).

cnf(c_2035,plain,
    ( v3_tex_2(sK2,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1853,c_32,c_33,c_81,c_84,c_525,c_1647,c_1652,c_1871,c_1987])).

cnf(c_2374,plain,
    ( k2_struct_0(sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2313,c_32,c_33,c_81,c_84,c_525,c_1647,c_1652,c_1878,c_1871,c_1987])).

cnf(c_2378,plain,
    ( v3_tex_2(sK2,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2374,c_2221])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2378,c_2035])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:03:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.70/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/0.98  
% 1.70/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.70/0.98  
% 1.70/0.98  ------  iProver source info
% 1.70/0.98  
% 1.70/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.70/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.70/0.98  git: non_committed_changes: false
% 1.70/0.98  git: last_make_outside_of_git: false
% 1.70/0.98  
% 1.70/0.98  ------ 
% 1.70/0.98  
% 1.70/0.98  ------ Input Options
% 1.70/0.98  
% 1.70/0.98  --out_options                           all
% 1.70/0.98  --tptp_safe_out                         true
% 1.70/0.98  --problem_path                          ""
% 1.70/0.98  --include_path                          ""
% 1.70/0.98  --clausifier                            res/vclausify_rel
% 1.70/0.98  --clausifier_options                    --mode clausify
% 1.70/0.98  --stdin                                 false
% 1.70/0.98  --stats_out                             all
% 1.70/0.98  
% 1.70/0.98  ------ General Options
% 1.70/0.98  
% 1.70/0.98  --fof                                   false
% 1.70/0.98  --time_out_real                         305.
% 1.70/0.98  --time_out_virtual                      -1.
% 1.70/0.98  --symbol_type_check                     false
% 1.70/0.98  --clausify_out                          false
% 1.70/0.98  --sig_cnt_out                           false
% 1.70/0.98  --trig_cnt_out                          false
% 1.70/0.98  --trig_cnt_out_tolerance                1.
% 1.70/0.98  --trig_cnt_out_sk_spl                   false
% 1.70/0.98  --abstr_cl_out                          false
% 1.70/0.98  
% 1.70/0.98  ------ Global Options
% 1.70/0.98  
% 1.70/0.98  --schedule                              default
% 1.70/0.98  --add_important_lit                     false
% 1.70/0.98  --prop_solver_per_cl                    1000
% 1.70/0.98  --min_unsat_core                        false
% 1.70/0.98  --soft_assumptions                      false
% 1.70/0.98  --soft_lemma_size                       3
% 1.70/0.98  --prop_impl_unit_size                   0
% 1.70/0.98  --prop_impl_unit                        []
% 1.70/0.98  --share_sel_clauses                     true
% 1.70/0.98  --reset_solvers                         false
% 1.70/0.98  --bc_imp_inh                            [conj_cone]
% 1.70/0.98  --conj_cone_tolerance                   3.
% 1.70/0.98  --extra_neg_conj                        none
% 1.70/0.98  --large_theory_mode                     true
% 1.70/0.98  --prolific_symb_bound                   200
% 1.70/0.98  --lt_threshold                          2000
% 1.70/0.98  --clause_weak_htbl                      true
% 1.70/0.98  --gc_record_bc_elim                     false
% 1.70/0.98  
% 1.70/0.98  ------ Preprocessing Options
% 1.70/0.98  
% 1.70/0.98  --preprocessing_flag                    true
% 1.70/0.98  --time_out_prep_mult                    0.1
% 1.70/0.98  --splitting_mode                        input
% 1.70/0.98  --splitting_grd                         true
% 1.70/0.98  --splitting_cvd                         false
% 1.70/0.98  --splitting_cvd_svl                     false
% 1.70/0.98  --splitting_nvd                         32
% 1.70/0.98  --sub_typing                            true
% 1.70/0.98  --prep_gs_sim                           true
% 1.70/0.98  --prep_unflatten                        true
% 1.70/0.98  --prep_res_sim                          true
% 1.70/0.98  --prep_upred                            true
% 1.70/0.98  --prep_sem_filter                       exhaustive
% 1.70/0.98  --prep_sem_filter_out                   false
% 1.70/0.98  --pred_elim                             true
% 1.70/0.98  --res_sim_input                         true
% 1.70/0.98  --eq_ax_congr_red                       true
% 1.70/0.98  --pure_diseq_elim                       true
% 1.70/0.98  --brand_transform                       false
% 1.70/0.98  --non_eq_to_eq                          false
% 1.70/0.98  --prep_def_merge                        true
% 1.70/0.98  --prep_def_merge_prop_impl              false
% 1.70/0.98  --prep_def_merge_mbd                    true
% 1.70/0.98  --prep_def_merge_tr_red                 false
% 1.70/0.98  --prep_def_merge_tr_cl                  false
% 1.70/0.98  --smt_preprocessing                     true
% 1.70/0.98  --smt_ac_axioms                         fast
% 1.70/0.98  --preprocessed_out                      false
% 1.70/0.98  --preprocessed_stats                    false
% 1.70/0.98  
% 1.70/0.98  ------ Abstraction refinement Options
% 1.70/0.98  
% 1.70/0.98  --abstr_ref                             []
% 1.70/0.98  --abstr_ref_prep                        false
% 1.70/0.98  --abstr_ref_until_sat                   false
% 1.70/0.98  --abstr_ref_sig_restrict                funpre
% 1.70/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.70/0.98  --abstr_ref_under                       []
% 1.70/0.98  
% 1.70/0.98  ------ SAT Options
% 1.70/0.98  
% 1.70/0.98  --sat_mode                              false
% 1.70/0.98  --sat_fm_restart_options                ""
% 1.70/0.98  --sat_gr_def                            false
% 1.70/0.98  --sat_epr_types                         true
% 1.70/0.98  --sat_non_cyclic_types                  false
% 1.70/0.98  --sat_finite_models                     false
% 1.70/0.98  --sat_fm_lemmas                         false
% 1.70/0.98  --sat_fm_prep                           false
% 1.70/0.98  --sat_fm_uc_incr                        true
% 1.70/0.98  --sat_out_model                         small
% 1.70/0.98  --sat_out_clauses                       false
% 1.70/0.98  
% 1.70/0.98  ------ QBF Options
% 1.70/0.98  
% 1.70/0.98  --qbf_mode                              false
% 1.70/0.98  --qbf_elim_univ                         false
% 1.70/0.98  --qbf_dom_inst                          none
% 1.70/0.98  --qbf_dom_pre_inst                      false
% 1.70/0.98  --qbf_sk_in                             false
% 1.70/0.98  --qbf_pred_elim                         true
% 1.70/0.98  --qbf_split                             512
% 1.70/0.98  
% 1.70/0.98  ------ BMC1 Options
% 1.70/0.98  
% 1.70/0.98  --bmc1_incremental                      false
% 1.70/0.98  --bmc1_axioms                           reachable_all
% 1.70/0.98  --bmc1_min_bound                        0
% 1.70/0.98  --bmc1_max_bound                        -1
% 1.70/0.98  --bmc1_max_bound_default                -1
% 1.70/0.98  --bmc1_symbol_reachability              true
% 1.70/0.98  --bmc1_property_lemmas                  false
% 1.70/0.98  --bmc1_k_induction                      false
% 1.70/0.98  --bmc1_non_equiv_states                 false
% 1.70/0.98  --bmc1_deadlock                         false
% 1.70/0.98  --bmc1_ucm                              false
% 1.70/0.98  --bmc1_add_unsat_core                   none
% 1.70/0.98  --bmc1_unsat_core_children              false
% 1.70/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.70/0.98  --bmc1_out_stat                         full
% 1.70/0.98  --bmc1_ground_init                      false
% 1.70/0.98  --bmc1_pre_inst_next_state              false
% 1.70/0.98  --bmc1_pre_inst_state                   false
% 1.70/0.98  --bmc1_pre_inst_reach_state             false
% 1.70/0.98  --bmc1_out_unsat_core                   false
% 1.70/0.98  --bmc1_aig_witness_out                  false
% 1.70/0.98  --bmc1_verbose                          false
% 1.70/0.98  --bmc1_dump_clauses_tptp                false
% 1.70/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.70/0.98  --bmc1_dump_file                        -
% 1.70/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.70/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.70/0.98  --bmc1_ucm_extend_mode                  1
% 1.70/0.98  --bmc1_ucm_init_mode                    2
% 1.70/0.98  --bmc1_ucm_cone_mode                    none
% 1.70/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.70/0.98  --bmc1_ucm_relax_model                  4
% 1.70/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.70/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.70/0.98  --bmc1_ucm_layered_model                none
% 1.70/0.98  --bmc1_ucm_max_lemma_size               10
% 1.70/0.98  
% 1.70/0.98  ------ AIG Options
% 1.70/0.98  
% 1.70/0.98  --aig_mode                              false
% 1.70/0.98  
% 1.70/0.98  ------ Instantiation Options
% 1.70/0.98  
% 1.70/0.98  --instantiation_flag                    true
% 1.70/0.98  --inst_sos_flag                         false
% 1.70/0.98  --inst_sos_phase                        true
% 1.70/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.70/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.70/0.98  --inst_lit_sel_side                     num_symb
% 1.70/0.98  --inst_solver_per_active                1400
% 1.70/0.98  --inst_solver_calls_frac                1.
% 1.70/0.98  --inst_passive_queue_type               priority_queues
% 1.70/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.70/0.98  --inst_passive_queues_freq              [25;2]
% 1.70/0.98  --inst_dismatching                      true
% 1.70/0.98  --inst_eager_unprocessed_to_passive     true
% 1.70/0.98  --inst_prop_sim_given                   true
% 1.70/0.98  --inst_prop_sim_new                     false
% 1.70/0.98  --inst_subs_new                         false
% 1.70/0.98  --inst_eq_res_simp                      false
% 1.70/0.98  --inst_subs_given                       false
% 1.70/0.98  --inst_orphan_elimination               true
% 1.70/0.98  --inst_learning_loop_flag               true
% 1.70/0.98  --inst_learning_start                   3000
% 1.70/0.98  --inst_learning_factor                  2
% 1.70/0.98  --inst_start_prop_sim_after_learn       3
% 1.70/0.98  --inst_sel_renew                        solver
% 1.70/0.98  --inst_lit_activity_flag                true
% 1.70/0.98  --inst_restr_to_given                   false
% 1.70/0.98  --inst_activity_threshold               500
% 1.70/0.98  --inst_out_proof                        true
% 1.70/0.98  
% 1.70/0.98  ------ Resolution Options
% 1.70/0.98  
% 1.70/0.98  --resolution_flag                       true
% 1.70/0.98  --res_lit_sel                           adaptive
% 1.70/0.98  --res_lit_sel_side                      none
% 1.70/0.98  --res_ordering                          kbo
% 1.70/0.98  --res_to_prop_solver                    active
% 1.70/0.98  --res_prop_simpl_new                    false
% 1.70/0.98  --res_prop_simpl_given                  true
% 1.70/0.98  --res_passive_queue_type                priority_queues
% 1.70/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.70/0.98  --res_passive_queues_freq               [15;5]
% 1.70/0.98  --res_forward_subs                      full
% 1.70/0.98  --res_backward_subs                     full
% 1.70/0.98  --res_forward_subs_resolution           true
% 1.70/0.98  --res_backward_subs_resolution          true
% 1.70/0.98  --res_orphan_elimination                true
% 1.70/0.98  --res_time_limit                        2.
% 1.70/0.98  --res_out_proof                         true
% 1.70/0.98  
% 1.70/0.98  ------ Superposition Options
% 1.70/0.98  
% 1.70/0.98  --superposition_flag                    true
% 1.70/0.98  --sup_passive_queue_type                priority_queues
% 1.70/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.70/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.70/0.98  --demod_completeness_check              fast
% 1.70/0.98  --demod_use_ground                      true
% 1.70/0.98  --sup_to_prop_solver                    passive
% 1.70/0.98  --sup_prop_simpl_new                    true
% 1.70/0.98  --sup_prop_simpl_given                  true
% 1.70/0.98  --sup_fun_splitting                     false
% 1.70/0.98  --sup_smt_interval                      50000
% 1.70/0.98  
% 1.70/0.98  ------ Superposition Simplification Setup
% 1.70/0.98  
% 1.70/0.98  --sup_indices_passive                   []
% 1.70/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.70/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.98  --sup_full_bw                           [BwDemod]
% 1.70/0.98  --sup_immed_triv                        [TrivRules]
% 1.70/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.70/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.98  --sup_immed_bw_main                     []
% 1.70/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.70/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.70/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.70/0.98  
% 1.70/0.98  ------ Combination Options
% 1.70/0.98  
% 1.70/0.98  --comb_res_mult                         3
% 1.70/0.98  --comb_sup_mult                         2
% 1.70/0.98  --comb_inst_mult                        10
% 1.70/0.98  
% 1.70/0.98  ------ Debug Options
% 1.70/0.98  
% 1.70/0.98  --dbg_backtrace                         false
% 1.70/0.98  --dbg_dump_prop_clauses                 false
% 1.70/0.98  --dbg_dump_prop_clauses_file            -
% 1.70/0.98  --dbg_out_stat                          false
% 1.70/0.98  ------ Parsing...
% 1.70/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.70/0.98  
% 1.70/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 1.70/0.98  
% 1.70/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.70/0.98  
% 1.70/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.70/0.98  ------ Proving...
% 1.70/0.98  ------ Problem Properties 
% 1.70/0.98  
% 1.70/0.98  
% 1.70/0.98  clauses                                 15
% 1.70/0.98  conjectures                             1
% 1.70/0.98  EPR                                     0
% 1.70/0.98  Horn                                    12
% 1.70/0.98  unary                                   6
% 1.70/0.98  binary                                  3
% 1.70/0.98  lits                                    32
% 1.70/0.98  lits eq                                 10
% 1.70/0.98  fd_pure                                 0
% 1.70/0.98  fd_pseudo                               0
% 1.70/0.98  fd_cond                                 0
% 1.70/0.98  fd_pseudo_cond                          1
% 1.70/0.98  AC symbols                              0
% 1.70/0.98  
% 1.70/0.98  ------ Schedule dynamic 5 is on 
% 1.70/0.98  
% 1.70/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.70/0.98  
% 1.70/0.98  
% 1.70/0.98  ------ 
% 1.70/0.98  Current options:
% 1.70/0.98  ------ 
% 1.70/0.98  
% 1.70/0.98  ------ Input Options
% 1.70/0.98  
% 1.70/0.98  --out_options                           all
% 1.70/0.98  --tptp_safe_out                         true
% 1.70/0.98  --problem_path                          ""
% 1.70/0.98  --include_path                          ""
% 1.70/0.98  --clausifier                            res/vclausify_rel
% 1.70/0.98  --clausifier_options                    --mode clausify
% 1.70/0.98  --stdin                                 false
% 1.70/0.98  --stats_out                             all
% 1.70/0.98  
% 1.70/0.98  ------ General Options
% 1.70/0.98  
% 1.70/0.98  --fof                                   false
% 1.70/0.98  --time_out_real                         305.
% 1.70/0.98  --time_out_virtual                      -1.
% 1.70/0.98  --symbol_type_check                     false
% 1.70/0.98  --clausify_out                          false
% 1.70/0.98  --sig_cnt_out                           false
% 1.70/0.98  --trig_cnt_out                          false
% 1.70/0.98  --trig_cnt_out_tolerance                1.
% 1.70/0.98  --trig_cnt_out_sk_spl                   false
% 1.70/0.98  --abstr_cl_out                          false
% 1.70/0.98  
% 1.70/0.98  ------ Global Options
% 1.70/0.98  
% 1.70/0.98  --schedule                              default
% 1.70/0.98  --add_important_lit                     false
% 1.70/0.98  --prop_solver_per_cl                    1000
% 1.70/0.98  --min_unsat_core                        false
% 1.70/0.98  --soft_assumptions                      false
% 1.70/0.98  --soft_lemma_size                       3
% 1.70/0.98  --prop_impl_unit_size                   0
% 1.70/0.98  --prop_impl_unit                        []
% 1.70/0.98  --share_sel_clauses                     true
% 1.70/0.98  --reset_solvers                         false
% 1.70/0.98  --bc_imp_inh                            [conj_cone]
% 1.70/0.98  --conj_cone_tolerance                   3.
% 1.70/0.98  --extra_neg_conj                        none
% 1.70/0.98  --large_theory_mode                     true
% 1.70/0.98  --prolific_symb_bound                   200
% 1.70/0.98  --lt_threshold                          2000
% 1.70/0.98  --clause_weak_htbl                      true
% 1.70/0.98  --gc_record_bc_elim                     false
% 1.70/0.98  
% 1.70/0.98  ------ Preprocessing Options
% 1.70/0.98  
% 1.70/0.98  --preprocessing_flag                    true
% 1.70/0.98  --time_out_prep_mult                    0.1
% 1.70/0.98  --splitting_mode                        input
% 1.70/0.98  --splitting_grd                         true
% 1.70/0.98  --splitting_cvd                         false
% 1.70/0.98  --splitting_cvd_svl                     false
% 1.70/0.98  --splitting_nvd                         32
% 1.70/0.98  --sub_typing                            true
% 1.70/0.98  --prep_gs_sim                           true
% 1.70/0.98  --prep_unflatten                        true
% 1.70/0.98  --prep_res_sim                          true
% 1.70/0.98  --prep_upred                            true
% 1.70/0.98  --prep_sem_filter                       exhaustive
% 1.70/0.98  --prep_sem_filter_out                   false
% 1.70/0.98  --pred_elim                             true
% 1.70/0.98  --res_sim_input                         true
% 1.70/0.98  --eq_ax_congr_red                       true
% 1.70/0.98  --pure_diseq_elim                       true
% 1.70/0.98  --brand_transform                       false
% 1.70/0.98  --non_eq_to_eq                          false
% 1.70/0.98  --prep_def_merge                        true
% 1.70/0.98  --prep_def_merge_prop_impl              false
% 1.70/0.98  --prep_def_merge_mbd                    true
% 1.70/0.98  --prep_def_merge_tr_red                 false
% 1.70/0.98  --prep_def_merge_tr_cl                  false
% 1.70/0.98  --smt_preprocessing                     true
% 1.70/0.98  --smt_ac_axioms                         fast
% 1.70/0.98  --preprocessed_out                      false
% 1.70/0.98  --preprocessed_stats                    false
% 1.70/0.98  
% 1.70/0.98  ------ Abstraction refinement Options
% 1.70/0.98  
% 1.70/0.98  --abstr_ref                             []
% 1.70/0.98  --abstr_ref_prep                        false
% 1.70/0.98  --abstr_ref_until_sat                   false
% 1.70/0.98  --abstr_ref_sig_restrict                funpre
% 1.70/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.70/0.98  --abstr_ref_under                       []
% 1.70/0.98  
% 1.70/0.98  ------ SAT Options
% 1.70/0.98  
% 1.70/0.98  --sat_mode                              false
% 1.70/0.98  --sat_fm_restart_options                ""
% 1.70/0.98  --sat_gr_def                            false
% 1.70/0.98  --sat_epr_types                         true
% 1.70/0.98  --sat_non_cyclic_types                  false
% 1.70/0.98  --sat_finite_models                     false
% 1.70/0.98  --sat_fm_lemmas                         false
% 1.70/0.98  --sat_fm_prep                           false
% 1.70/0.98  --sat_fm_uc_incr                        true
% 1.70/0.98  --sat_out_model                         small
% 1.70/0.98  --sat_out_clauses                       false
% 1.70/0.98  
% 1.70/0.98  ------ QBF Options
% 1.70/0.98  
% 1.70/0.98  --qbf_mode                              false
% 1.70/0.98  --qbf_elim_univ                         false
% 1.70/0.98  --qbf_dom_inst                          none
% 1.70/0.98  --qbf_dom_pre_inst                      false
% 1.70/0.98  --qbf_sk_in                             false
% 1.70/0.98  --qbf_pred_elim                         true
% 1.70/0.98  --qbf_split                             512
% 1.70/0.98  
% 1.70/0.98  ------ BMC1 Options
% 1.70/0.98  
% 1.70/0.98  --bmc1_incremental                      false
% 1.70/0.98  --bmc1_axioms                           reachable_all
% 1.70/0.98  --bmc1_min_bound                        0
% 1.70/0.98  --bmc1_max_bound                        -1
% 1.70/0.98  --bmc1_max_bound_default                -1
% 1.70/0.98  --bmc1_symbol_reachability              true
% 1.70/0.98  --bmc1_property_lemmas                  false
% 1.70/0.98  --bmc1_k_induction                      false
% 1.70/0.98  --bmc1_non_equiv_states                 false
% 1.70/0.98  --bmc1_deadlock                         false
% 1.70/0.98  --bmc1_ucm                              false
% 1.70/0.98  --bmc1_add_unsat_core                   none
% 1.70/0.98  --bmc1_unsat_core_children              false
% 1.70/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.70/0.98  --bmc1_out_stat                         full
% 1.70/0.98  --bmc1_ground_init                      false
% 1.70/0.98  --bmc1_pre_inst_next_state              false
% 1.70/0.98  --bmc1_pre_inst_state                   false
% 1.70/0.98  --bmc1_pre_inst_reach_state             false
% 1.70/0.98  --bmc1_out_unsat_core                   false
% 1.70/0.98  --bmc1_aig_witness_out                  false
% 1.70/0.98  --bmc1_verbose                          false
% 1.70/0.98  --bmc1_dump_clauses_tptp                false
% 1.70/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.70/0.98  --bmc1_dump_file                        -
% 1.70/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.70/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.70/0.98  --bmc1_ucm_extend_mode                  1
% 1.70/0.98  --bmc1_ucm_init_mode                    2
% 1.70/0.98  --bmc1_ucm_cone_mode                    none
% 1.70/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.70/0.98  --bmc1_ucm_relax_model                  4
% 1.70/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.70/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.70/0.98  --bmc1_ucm_layered_model                none
% 1.70/0.98  --bmc1_ucm_max_lemma_size               10
% 1.70/0.98  
% 1.70/0.98  ------ AIG Options
% 1.70/0.98  
% 1.70/0.98  --aig_mode                              false
% 1.70/0.98  
% 1.70/0.98  ------ Instantiation Options
% 1.70/0.98  
% 1.70/0.98  --instantiation_flag                    true
% 1.70/0.98  --inst_sos_flag                         false
% 1.70/0.98  --inst_sos_phase                        true
% 1.70/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.70/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.70/0.98  --inst_lit_sel_side                     none
% 1.70/0.98  --inst_solver_per_active                1400
% 1.70/0.98  --inst_solver_calls_frac                1.
% 1.70/0.98  --inst_passive_queue_type               priority_queues
% 1.70/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.70/0.98  --inst_passive_queues_freq              [25;2]
% 1.70/0.98  --inst_dismatching                      true
% 1.70/0.98  --inst_eager_unprocessed_to_passive     true
% 1.70/0.98  --inst_prop_sim_given                   true
% 1.70/0.98  --inst_prop_sim_new                     false
% 1.70/0.98  --inst_subs_new                         false
% 1.70/0.98  --inst_eq_res_simp                      false
% 1.70/0.98  --inst_subs_given                       false
% 1.70/0.98  --inst_orphan_elimination               true
% 1.70/0.98  --inst_learning_loop_flag               true
% 1.70/0.98  --inst_learning_start                   3000
% 1.70/0.98  --inst_learning_factor                  2
% 1.70/0.98  --inst_start_prop_sim_after_learn       3
% 1.70/0.98  --inst_sel_renew                        solver
% 1.70/0.98  --inst_lit_activity_flag                true
% 1.70/0.98  --inst_restr_to_given                   false
% 1.70/0.98  --inst_activity_threshold               500
% 1.70/0.98  --inst_out_proof                        true
% 1.70/0.98  
% 1.70/0.98  ------ Resolution Options
% 1.70/0.98  
% 1.70/0.98  --resolution_flag                       false
% 1.70/0.98  --res_lit_sel                           adaptive
% 1.70/0.98  --res_lit_sel_side                      none
% 1.70/0.98  --res_ordering                          kbo
% 1.70/0.98  --res_to_prop_solver                    active
% 1.70/0.98  --res_prop_simpl_new                    false
% 1.70/0.98  --res_prop_simpl_given                  true
% 1.70/0.98  --res_passive_queue_type                priority_queues
% 1.70/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.70/0.98  --res_passive_queues_freq               [15;5]
% 1.70/0.98  --res_forward_subs                      full
% 1.70/0.98  --res_backward_subs                     full
% 1.70/0.98  --res_forward_subs_resolution           true
% 1.70/0.98  --res_backward_subs_resolution          true
% 1.70/0.98  --res_orphan_elimination                true
% 1.70/0.98  --res_time_limit                        2.
% 1.70/0.98  --res_out_proof                         true
% 1.70/0.98  
% 1.70/0.98  ------ Superposition Options
% 1.70/0.98  
% 1.70/0.98  --superposition_flag                    true
% 1.70/0.98  --sup_passive_queue_type                priority_queues
% 1.70/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.70/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.70/0.98  --demod_completeness_check              fast
% 1.70/0.98  --demod_use_ground                      true
% 1.70/0.98  --sup_to_prop_solver                    passive
% 1.70/0.98  --sup_prop_simpl_new                    true
% 1.70/0.98  --sup_prop_simpl_given                  true
% 1.70/0.98  --sup_fun_splitting                     false
% 1.70/0.98  --sup_smt_interval                      50000
% 1.70/0.98  
% 1.70/0.98  ------ Superposition Simplification Setup
% 1.70/0.98  
% 1.70/0.98  --sup_indices_passive                   []
% 1.70/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.70/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.98  --sup_full_bw                           [BwDemod]
% 1.70/0.98  --sup_immed_triv                        [TrivRules]
% 1.70/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.70/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.98  --sup_immed_bw_main                     []
% 1.70/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.70/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.70/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.70/0.98  
% 1.70/0.98  ------ Combination Options
% 1.70/0.98  
% 1.70/0.98  --comb_res_mult                         3
% 1.70/0.98  --comb_sup_mult                         2
% 1.70/0.98  --comb_inst_mult                        10
% 1.70/0.98  
% 1.70/0.98  ------ Debug Options
% 1.70/0.98  
% 1.70/0.98  --dbg_backtrace                         false
% 1.70/0.98  --dbg_dump_prop_clauses                 false
% 1.70/0.98  --dbg_dump_prop_clauses_file            -
% 1.70/0.98  --dbg_out_stat                          false
% 1.70/0.98  
% 1.70/0.98  
% 1.70/0.98  
% 1.70/0.98  
% 1.70/0.98  ------ Proving...
% 1.70/0.98  
% 1.70/0.98  
% 1.70/0.98  % SZS status Theorem for theBenchmark.p
% 1.70/0.98  
% 1.70/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.70/0.98  
% 1.70/0.98  fof(f15,conjecture,(
% 1.70/0.98    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 1.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.98  
% 1.70/0.98  fof(f16,negated_conjecture,(
% 1.70/0.98    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 1.70/0.98    inference(negated_conjecture,[],[f15])).
% 1.70/0.98  
% 1.70/0.98  fof(f31,plain,(
% 1.70/0.98    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.70/0.98    inference(ennf_transformation,[],[f16])).
% 1.70/0.98  
% 1.70/0.98  fof(f32,plain,(
% 1.70/0.98    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.70/0.98    inference(flattening,[],[f31])).
% 1.70/0.98  
% 1.70/0.98  fof(f41,plain,(
% 1.70/0.98    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.70/0.98    inference(nnf_transformation,[],[f32])).
% 1.70/0.98  
% 1.70/0.98  fof(f42,plain,(
% 1.70/0.98    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.70/0.98    inference(flattening,[],[f41])).
% 1.70/0.98  
% 1.70/0.98  fof(f44,plain,(
% 1.70/0.98    ( ! [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_subset_1(sK2,u1_struct_0(X0)) | ~v3_tex_2(sK2,X0)) & (~v1_subset_1(sK2,u1_struct_0(X0)) | v3_tex_2(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.70/0.98    introduced(choice_axiom,[])).
% 1.70/0.98  
% 1.70/0.98  fof(f43,plain,(
% 1.70/0.98    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK1)) | ~v3_tex_2(X1,sK1)) & (~v1_subset_1(X1,u1_struct_0(sK1)) | v3_tex_2(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v1_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.70/0.98    introduced(choice_axiom,[])).
% 1.70/0.98  
% 1.70/0.98  fof(f45,plain,(
% 1.70/0.98    ((v1_subset_1(sK2,u1_struct_0(sK1)) | ~v3_tex_2(sK2,sK1)) & (~v1_subset_1(sK2,u1_struct_0(sK1)) | v3_tex_2(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v1_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.70/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f42,f44,f43])).
% 1.70/0.98  
% 1.70/0.98  fof(f72,plain,(
% 1.70/0.98    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.70/0.98    inference(cnf_transformation,[],[f45])).
% 1.70/0.98  
% 1.70/0.98  fof(f4,axiom,(
% 1.70/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.98  
% 1.70/0.98  fof(f33,plain,(
% 1.70/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.70/0.98    inference(nnf_transformation,[],[f4])).
% 1.70/0.98  
% 1.70/0.98  fof(f49,plain,(
% 1.70/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.70/0.98    inference(cnf_transformation,[],[f33])).
% 1.70/0.98  
% 1.70/0.98  fof(f6,axiom,(
% 1.70/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.98  
% 1.70/0.98  fof(f18,plain,(
% 1.70/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.70/0.98    inference(ennf_transformation,[],[f6])).
% 1.70/0.98  
% 1.70/0.98  fof(f52,plain,(
% 1.70/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.70/0.98    inference(cnf_transformation,[],[f18])).
% 1.70/0.98  
% 1.70/0.98  fof(f7,axiom,(
% 1.70/0.98    ! [X0] : (l1_struct_0(X0) => ~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)))),
% 1.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.98  
% 1.70/0.98  fof(f19,plain,(
% 1.70/0.98    ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0))),
% 1.70/0.98    inference(ennf_transformation,[],[f7])).
% 1.70/0.98  
% 1.70/0.98  fof(f53,plain,(
% 1.70/0.98    ( ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 1.70/0.98    inference(cnf_transformation,[],[f19])).
% 1.70/0.98  
% 1.70/0.98  fof(f11,axiom,(
% 1.70/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.98  
% 1.70/0.98  fof(f24,plain,(
% 1.70/0.98    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.70/0.98    inference(ennf_transformation,[],[f11])).
% 1.70/0.98  
% 1.70/0.98  fof(f35,plain,(
% 1.70/0.98    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.70/0.98    inference(nnf_transformation,[],[f24])).
% 1.70/0.98  
% 1.70/0.98  fof(f59,plain,(
% 1.70/0.98    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.70/0.98    inference(cnf_transformation,[],[f35])).
% 1.70/0.98  
% 1.70/0.98  fof(f50,plain,(
% 1.70/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.70/0.98    inference(cnf_transformation,[],[f33])).
% 1.70/0.98  
% 1.70/0.98  fof(f71,plain,(
% 1.70/0.98    l1_pre_topc(sK1)),
% 1.70/0.98    inference(cnf_transformation,[],[f45])).
% 1.70/0.98  
% 1.70/0.98  fof(f5,axiom,(
% 1.70/0.98    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.98  
% 1.70/0.98  fof(f17,plain,(
% 1.70/0.98    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 1.70/0.98    inference(ennf_transformation,[],[f5])).
% 1.70/0.98  
% 1.70/0.98  fof(f51,plain,(
% 1.70/0.98    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 1.70/0.98    inference(cnf_transformation,[],[f17])).
% 1.70/0.98  
% 1.70/0.98  fof(f2,axiom,(
% 1.70/0.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.98  
% 1.70/0.98  fof(f47,plain,(
% 1.70/0.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.70/0.98    inference(cnf_transformation,[],[f2])).
% 1.70/0.98  
% 1.70/0.98  fof(f1,axiom,(
% 1.70/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 1.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.98  
% 1.70/0.98  fof(f46,plain,(
% 1.70/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.70/0.98    inference(cnf_transformation,[],[f1])).
% 1.70/0.98  
% 1.70/0.98  fof(f8,axiom,(
% 1.70/0.98    ! [X0] : (l1_pre_topc(X0) => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)))),
% 1.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.98  
% 1.70/0.98  fof(f20,plain,(
% 1.70/0.98    ! [X0] : (k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0))),
% 1.70/0.98    inference(ennf_transformation,[],[f8])).
% 1.70/0.98  
% 1.70/0.98  fof(f54,plain,(
% 1.70/0.98    ( ! [X0] : (k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 1.70/0.98    inference(cnf_transformation,[],[f20])).
% 1.70/0.98  
% 1.70/0.98  fof(f10,axiom,(
% 1.70/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 1.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.98  
% 1.70/0.98  fof(f23,plain,(
% 1.70/0.98    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.70/0.98    inference(ennf_transformation,[],[f10])).
% 1.70/0.98  
% 1.70/0.98  fof(f34,plain,(
% 1.70/0.98    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.70/0.98    inference(nnf_transformation,[],[f23])).
% 1.70/0.98  
% 1.70/0.98  fof(f57,plain,(
% 1.70/0.98    ( ! [X0,X1] : (v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.70/0.98    inference(cnf_transformation,[],[f34])).
% 1.70/0.98  
% 1.70/0.98  fof(f14,axiom,(
% 1.70/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 1.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.98  
% 1.70/0.98  fof(f29,plain,(
% 1.70/0.98    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.70/0.98    inference(ennf_transformation,[],[f14])).
% 1.70/0.98  
% 1.70/0.98  fof(f30,plain,(
% 1.70/0.98    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.70/0.98    inference(flattening,[],[f29])).
% 1.70/0.98  
% 1.70/0.98  fof(f67,plain,(
% 1.70/0.98    ( ! [X0,X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.98    inference(cnf_transformation,[],[f30])).
% 1.70/0.98  
% 1.70/0.98  fof(f69,plain,(
% 1.70/0.98    v2_pre_topc(sK1)),
% 1.70/0.98    inference(cnf_transformation,[],[f45])).
% 1.70/0.98  
% 1.70/0.98  fof(f68,plain,(
% 1.70/0.98    ~v2_struct_0(sK1)),
% 1.70/0.98    inference(cnf_transformation,[],[f45])).
% 1.70/0.98  
% 1.70/0.98  fof(f13,axiom,(
% 1.70/0.98    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 1.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.98  
% 1.70/0.98  fof(f27,plain,(
% 1.70/0.98    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.70/0.98    inference(ennf_transformation,[],[f13])).
% 1.70/0.98  
% 1.70/0.98  fof(f28,plain,(
% 1.70/0.98    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.70/0.98    inference(flattening,[],[f27])).
% 1.70/0.98  
% 1.70/0.98  fof(f66,plain,(
% 1.70/0.98    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.98    inference(cnf_transformation,[],[f28])).
% 1.70/0.98  
% 1.70/0.98  fof(f70,plain,(
% 1.70/0.98    v1_tdlat_3(sK1)),
% 1.70/0.98    inference(cnf_transformation,[],[f45])).
% 1.70/0.98  
% 1.70/0.98  fof(f12,axiom,(
% 1.70/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 1.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.98  
% 1.70/0.98  fof(f25,plain,(
% 1.70/0.98    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.70/0.98    inference(ennf_transformation,[],[f12])).
% 1.70/0.98  
% 1.70/0.98  fof(f26,plain,(
% 1.70/0.98    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.70/0.98    inference(flattening,[],[f25])).
% 1.70/0.98  
% 1.70/0.98  fof(f36,plain,(
% 1.70/0.98    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.70/0.98    inference(nnf_transformation,[],[f26])).
% 1.70/0.98  
% 1.70/0.98  fof(f37,plain,(
% 1.70/0.98    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.70/0.98    inference(flattening,[],[f36])).
% 1.70/0.98  
% 1.70/0.98  fof(f38,plain,(
% 1.70/0.98    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.70/0.98    inference(rectify,[],[f37])).
% 1.70/0.98  
% 1.70/0.98  fof(f39,plain,(
% 1.70/0.98    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK0(X0,X1) != X1 & r1_tarski(X1,sK0(X0,X1)) & v2_tex_2(sK0(X0,X1),X0) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.70/0.98    introduced(choice_axiom,[])).
% 1.70/0.98  
% 1.70/0.98  fof(f40,plain,(
% 1.70/0.98    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK0(X0,X1) != X1 & r1_tarski(X1,sK0(X0,X1)) & v2_tex_2(sK0(X0,X1),X0) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.70/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 1.70/0.98  
% 1.70/0.98  fof(f61,plain,(
% 1.70/0.98    ( ! [X0,X3,X1] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.70/0.98    inference(cnf_transformation,[],[f40])).
% 1.70/0.98  
% 1.70/0.98  fof(f73,plain,(
% 1.70/0.98    ~v1_subset_1(sK2,u1_struct_0(sK1)) | v3_tex_2(sK2,sK1)),
% 1.70/0.98    inference(cnf_transformation,[],[f45])).
% 1.70/0.98  
% 1.70/0.98  fof(f74,plain,(
% 1.70/0.98    v1_subset_1(sK2,u1_struct_0(sK1)) | ~v3_tex_2(sK2,sK1)),
% 1.70/0.98    inference(cnf_transformation,[],[f45])).
% 1.70/0.98  
% 1.70/0.98  cnf(c_24,negated_conjecture,
% 1.70/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.70/0.98      inference(cnf_transformation,[],[f72]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_1863,plain,
% 1.70/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.70/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_4,plain,
% 1.70/0.98      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.70/0.98      inference(cnf_transformation,[],[f49]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_219,plain,
% 1.70/0.98      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.70/0.98      inference(prop_impl,[status(thm)],[c_4]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_6,plain,
% 1.70/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.70/0.98      inference(cnf_transformation,[],[f52]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_7,plain,
% 1.70/0.98      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
% 1.70/0.98      | ~ l1_struct_0(X0) ),
% 1.70/0.98      inference(cnf_transformation,[],[f53]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_382,plain,
% 1.70/0.98      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
% 1.70/0.98      | ~ l1_pre_topc(X0) ),
% 1.70/0.98      inference(resolution,[status(thm)],[c_6,c_7]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_12,plain,
% 1.70/0.98      ( v1_subset_1(X0,X1)
% 1.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.70/0.98      | X0 = X1 ),
% 1.70/0.98      inference(cnf_transformation,[],[f59]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_3,plain,
% 1.70/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.70/0.98      inference(cnf_transformation,[],[f50]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_221,plain,
% 1.70/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.70/0.98      inference(prop_impl,[status(thm)],[c_3]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_278,plain,
% 1.70/0.98      ( ~ r1_tarski(X0,X1) | v1_subset_1(X0,X1) | X0 = X1 ),
% 1.70/0.98      inference(bin_hyper_res,[status(thm)],[c_12,c_221]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_507,plain,
% 1.70/0.98      ( ~ r1_tarski(X0,X1)
% 1.70/0.98      | ~ l1_pre_topc(X2)
% 1.70/0.98      | X1 = X0
% 1.70/0.98      | u1_struct_0(X2) != X1
% 1.70/0.98      | k2_struct_0(X2) != X0 ),
% 1.70/0.98      inference(resolution_lifted,[status(thm)],[c_382,c_278]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_508,plain,
% 1.70/0.98      ( ~ r1_tarski(k2_struct_0(X0),u1_struct_0(X0))
% 1.70/0.98      | ~ l1_pre_topc(X0)
% 1.70/0.98      | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.70/0.98      inference(unflattening,[status(thm)],[c_507]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_25,negated_conjecture,
% 1.70/0.98      ( l1_pre_topc(sK1) ),
% 1.70/0.98      inference(cnf_transformation,[],[f71]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_603,plain,
% 1.70/0.98      ( ~ r1_tarski(k2_struct_0(X0),u1_struct_0(X0))
% 1.70/0.98      | u1_struct_0(X0) = k2_struct_0(X0)
% 1.70/0.98      | sK1 != X0 ),
% 1.70/0.98      inference(resolution_lifted,[status(thm)],[c_508,c_25]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_604,plain,
% 1.70/0.98      ( ~ r1_tarski(k2_struct_0(sK1),u1_struct_0(sK1))
% 1.70/0.98      | u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 1.70/0.98      inference(unflattening,[status(thm)],[c_603]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_814,plain,
% 1.70/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.70/0.98      | u1_struct_0(sK1) != X1
% 1.70/0.98      | u1_struct_0(sK1) = k2_struct_0(sK1)
% 1.70/0.98      | k2_struct_0(sK1) != X0 ),
% 1.70/0.98      inference(resolution_lifted,[status(thm)],[c_219,c_604]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_815,plain,
% 1.70/0.98      ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/0.98      | u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 1.70/0.98      inference(unflattening,[status(thm)],[c_814]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_80,plain,
% 1.70/0.98      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 1.70/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_5,plain,
% 1.70/0.98      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 1.70/0.98      | ~ l1_struct_0(X0) ),
% 1.70/0.98      inference(cnf_transformation,[],[f51]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_83,plain,
% 1.70/0.98      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/0.98      | ~ l1_struct_0(sK1) ),
% 1.70/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_817,plain,
% 1.70/0.98      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 1.70/0.98      inference(global_propositional_subsumption,
% 1.70/0.98                [status(thm)],
% 1.70/0.98                [c_815,c_25,c_80,c_83]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_1871,plain,
% 1.70/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 1.70/0.98      inference(light_normalisation,[status(thm)],[c_1863,c_817]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_1,plain,
% 1.70/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 1.70/0.98      inference(cnf_transformation,[],[f47]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_1864,plain,
% 1.70/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 1.70/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_0,plain,
% 1.70/0.98      ( k2_subset_1(X0) = X0 ),
% 1.70/0.98      inference(cnf_transformation,[],[f46]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_1874,plain,
% 1.70/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.70/0.98      inference(light_normalisation,[status(thm)],[c_1864,c_0]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_8,plain,
% 1.70/0.98      ( ~ l1_pre_topc(X0)
% 1.70/0.98      | k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
% 1.70/0.98      inference(cnf_transformation,[],[f54]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_620,plain,
% 1.70/0.98      ( k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) | sK1 != X0 ),
% 1.70/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_25]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_621,plain,
% 1.70/0.98      ( k2_pre_topc(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1) ),
% 1.70/0.98      inference(unflattening,[status(thm)],[c_620]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_10,plain,
% 1.70/0.98      ( v1_tops_1(X0,X1)
% 1.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.70/0.98      | ~ l1_pre_topc(X1)
% 1.70/0.98      | k2_pre_topc(X1,X0) != u1_struct_0(X1) ),
% 1.70/0.98      inference(cnf_transformation,[],[f57]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_21,plain,
% 1.70/0.98      ( ~ v2_tex_2(X0,X1)
% 1.70/0.98      | v3_tex_2(X0,X1)
% 1.70/0.98      | ~ v1_tops_1(X0,X1)
% 1.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.70/0.98      | v2_struct_0(X1)
% 1.70/0.98      | ~ v2_pre_topc(X1)
% 1.70/0.98      | ~ l1_pre_topc(X1) ),
% 1.70/0.98      inference(cnf_transformation,[],[f67]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_27,negated_conjecture,
% 1.70/0.98      ( v2_pre_topc(sK1) ),
% 1.70/0.98      inference(cnf_transformation,[],[f69]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_433,plain,
% 1.70/0.98      ( ~ v2_tex_2(X0,X1)
% 1.70/0.98      | v3_tex_2(X0,X1)
% 1.70/0.98      | ~ v1_tops_1(X0,X1)
% 1.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.70/0.98      | v2_struct_0(X1)
% 1.70/0.98      | ~ l1_pre_topc(X1)
% 1.70/0.98      | sK1 != X1 ),
% 1.70/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_434,plain,
% 1.70/0.98      ( ~ v2_tex_2(X0,sK1)
% 1.70/0.98      | v3_tex_2(X0,sK1)
% 1.70/0.98      | ~ v1_tops_1(X0,sK1)
% 1.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/0.98      | v2_struct_0(sK1)
% 1.70/0.98      | ~ l1_pre_topc(sK1) ),
% 1.70/0.98      inference(unflattening,[status(thm)],[c_433]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_28,negated_conjecture,
% 1.70/0.98      ( ~ v2_struct_0(sK1) ),
% 1.70/0.98      inference(cnf_transformation,[],[f68]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_20,plain,
% 1.70/0.98      ( v2_tex_2(X0,X1)
% 1.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.70/0.98      | v2_struct_0(X1)
% 1.70/0.98      | ~ v1_tdlat_3(X1)
% 1.70/0.98      | ~ v2_pre_topc(X1)
% 1.70/0.98      | ~ l1_pre_topc(X1) ),
% 1.70/0.98      inference(cnf_transformation,[],[f66]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_26,negated_conjecture,
% 1.70/0.98      ( v1_tdlat_3(sK1) ),
% 1.70/0.98      inference(cnf_transformation,[],[f70]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_412,plain,
% 1.70/0.98      ( v2_tex_2(X0,X1)
% 1.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.70/0.98      | v2_struct_0(X1)
% 1.70/0.98      | ~ v2_pre_topc(X1)
% 1.70/0.98      | ~ l1_pre_topc(X1)
% 1.70/0.98      | sK1 != X1 ),
% 1.70/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_26]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_413,plain,
% 1.70/0.98      ( v2_tex_2(X0,sK1)
% 1.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/0.98      | v2_struct_0(sK1)
% 1.70/0.98      | ~ v2_pre_topc(sK1)
% 1.70/0.98      | ~ l1_pre_topc(sK1) ),
% 1.70/0.98      inference(unflattening,[status(thm)],[c_412]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_417,plain,
% 1.70/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/0.98      | v2_tex_2(X0,sK1) ),
% 1.70/0.98      inference(global_propositional_subsumption,
% 1.70/0.98                [status(thm)],
% 1.70/0.98                [c_413,c_28,c_27,c_25]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_418,plain,
% 1.70/0.98      ( v2_tex_2(X0,sK1)
% 1.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.70/0.98      inference(renaming,[status(thm)],[c_417]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_438,plain,
% 1.70/0.98      ( v3_tex_2(X0,sK1)
% 1.70/0.98      | ~ v1_tops_1(X0,sK1)
% 1.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.70/0.98      inference(global_propositional_subsumption,
% 1.70/0.98                [status(thm)],
% 1.70/0.98                [c_434,c_28,c_25,c_418]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_459,plain,
% 1.70/0.98      ( v3_tex_2(X0,sK1)
% 1.70/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/0.98      | ~ l1_pre_topc(X2)
% 1.70/0.98      | X0 != X1
% 1.70/0.98      | k2_pre_topc(X2,X1) != u1_struct_0(X2)
% 1.70/0.98      | sK1 != X2 ),
% 1.70/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_438]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_460,plain,
% 1.70/0.98      ( v3_tex_2(X0,sK1)
% 1.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/0.98      | ~ l1_pre_topc(sK1)
% 1.70/0.98      | k2_pre_topc(sK1,X0) != u1_struct_0(sK1) ),
% 1.70/0.98      inference(unflattening,[status(thm)],[c_459]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_464,plain,
% 1.70/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/0.98      | v3_tex_2(X0,sK1)
% 1.70/0.98      | k2_pre_topc(sK1,X0) != u1_struct_0(sK1) ),
% 1.70/0.98      inference(global_propositional_subsumption,
% 1.70/0.98                [status(thm)],
% 1.70/0.98                [c_460,c_25]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_465,plain,
% 1.70/0.98      ( v3_tex_2(X0,sK1)
% 1.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/0.98      | k2_pre_topc(sK1,X0) != u1_struct_0(sK1) ),
% 1.70/0.98      inference(renaming,[status(thm)],[c_464]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_1862,plain,
% 1.70/0.98      ( k2_pre_topc(sK1,X0) != u1_struct_0(sK1)
% 1.70/0.98      | v3_tex_2(X0,sK1) = iProver_top
% 1.70/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.70/0.98      inference(predicate_to_equality,[status(thm)],[c_465]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_1897,plain,
% 1.70/0.98      ( k2_pre_topc(sK1,X0) != k2_struct_0(sK1)
% 1.70/0.98      | v3_tex_2(X0,sK1) = iProver_top
% 1.70/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 1.70/0.98      inference(light_normalisation,[status(thm)],[c_1862,c_817]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_2118,plain,
% 1.70/0.98      ( v3_tex_2(k2_struct_0(sK1),sK1) = iProver_top
% 1.70/0.98      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 1.70/0.98      inference(superposition,[status(thm)],[c_621,c_1897]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_2221,plain,
% 1.70/0.98      ( v3_tex_2(k2_struct_0(sK1),sK1) = iProver_top ),
% 1.70/0.98      inference(superposition,[status(thm)],[c_1874,c_2118]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_18,plain,
% 1.70/0.98      ( ~ v2_tex_2(X0,X1)
% 1.70/0.98      | ~ v3_tex_2(X2,X1)
% 1.70/0.98      | ~ r1_tarski(X2,X0)
% 1.70/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.70/0.98      | ~ l1_pre_topc(X1)
% 1.70/0.98      | X0 = X2 ),
% 1.70/0.98      inference(cnf_transformation,[],[f61]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_634,plain,
% 1.70/0.98      ( ~ v2_tex_2(X0,X1)
% 1.70/0.98      | ~ v3_tex_2(X2,X1)
% 1.70/0.98      | ~ r1_tarski(X2,X0)
% 1.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.70/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.70/0.98      | X2 = X0
% 1.70/0.98      | sK1 != X1 ),
% 1.70/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_635,plain,
% 1.70/0.98      ( ~ v2_tex_2(X0,sK1)
% 1.70/0.98      | ~ v3_tex_2(X1,sK1)
% 1.70/0.98      | ~ r1_tarski(X1,X0)
% 1.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/0.98      | X1 = X0 ),
% 1.70/0.98      inference(unflattening,[status(thm)],[c_634]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_639,plain,
% 1.70/0.98      ( ~ v3_tex_2(X1,sK1)
% 1.70/0.98      | ~ r1_tarski(X1,X0)
% 1.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/0.98      | X1 = X0 ),
% 1.70/0.98      inference(global_propositional_subsumption,
% 1.70/0.98                [status(thm)],
% 1.70/0.98                [c_635,c_28,c_27,c_25,c_413]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_640,plain,
% 1.70/0.98      ( ~ v3_tex_2(X0,sK1)
% 1.70/0.98      | ~ r1_tarski(X0,X1)
% 1.70/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/0.98      | X0 = X1 ),
% 1.70/0.98      inference(renaming,[status(thm)],[c_639]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_777,plain,
% 1.70/0.98      ( ~ v3_tex_2(X0,sK1)
% 1.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/0.98      | X1 = X0 ),
% 1.70/0.98      inference(resolution,[status(thm)],[c_219,c_640]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_1856,plain,
% 1.70/0.98      ( X0 = X1
% 1.70/0.98      | v3_tex_2(X1,sK1) != iProver_top
% 1.70/0.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 1.70/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.70/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.70/0.98      inference(predicate_to_equality,[status(thm)],[c_777]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_1918,plain,
% 1.70/0.98      ( X0 = X1
% 1.70/0.98      | v3_tex_2(X0,sK1) != iProver_top
% 1.70/0.98      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.70/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 1.70/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 1.70/0.98      inference(light_normalisation,[status(thm)],[c_1856,c_817]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_2222,plain,
% 1.70/0.98      ( k2_struct_0(sK1) = X0
% 1.70/0.98      | v3_tex_2(k2_struct_0(sK1),sK1) != iProver_top
% 1.70/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 1.70/0.98      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(X0)) != iProver_top ),
% 1.70/0.98      inference(superposition,[status(thm)],[c_1874,c_1918]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_2233,plain,
% 1.70/0.98      ( k2_struct_0(sK1) = X0
% 1.70/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 1.70/0.98      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(X0)) != iProver_top ),
% 1.70/0.98      inference(backward_subsumption_resolution,
% 1.70/0.98                [status(thm)],
% 1.70/0.98                [c_2221,c_2222]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_2313,plain,
% 1.70/0.98      ( k2_struct_0(sK1) = sK2
% 1.70/0.98      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(sK2)) != iProver_top ),
% 1.70/0.98      inference(superposition,[status(thm)],[c_1871,c_2233]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_23,negated_conjecture,
% 1.70/0.98      ( v3_tex_2(sK2,sK1) | ~ v1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.70/0.98      inference(cnf_transformation,[],[f73]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_223,plain,
% 1.70/0.98      ( v3_tex_2(sK2,sK1) | ~ v1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.70/0.98      inference(prop_impl,[status(thm)],[c_23]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_541,plain,
% 1.70/0.98      ( v3_tex_2(sK2,sK1)
% 1.70/0.98      | ~ r1_tarski(X0,X1)
% 1.70/0.98      | X1 = X0
% 1.70/0.98      | u1_struct_0(sK1) != X1
% 1.70/0.98      | sK2 != X0 ),
% 1.70/0.98      inference(resolution_lifted,[status(thm)],[c_278,c_223]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_542,plain,
% 1.70/0.98      ( v3_tex_2(sK2,sK1)
% 1.70/0.98      | ~ r1_tarski(sK2,u1_struct_0(sK1))
% 1.70/0.98      | u1_struct_0(sK1) = sK2 ),
% 1.70/0.98      inference(unflattening,[status(thm)],[c_541]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_800,plain,
% 1.70/0.98      ( v3_tex_2(sK2,sK1)
% 1.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.70/0.98      | u1_struct_0(sK1) != X1
% 1.70/0.98      | u1_struct_0(sK1) = sK2
% 1.70/0.98      | sK2 != X0 ),
% 1.70/0.98      inference(resolution_lifted,[status(thm)],[c_219,c_542]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_801,plain,
% 1.70/0.98      ( v3_tex_2(sK2,sK1)
% 1.70/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/0.98      | u1_struct_0(sK1) = sK2 ),
% 1.70/0.98      inference(unflattening,[status(thm)],[c_800]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_803,plain,
% 1.70/0.98      ( v3_tex_2(sK2,sK1) | u1_struct_0(sK1) = sK2 ),
% 1.70/0.98      inference(global_propositional_subsumption,
% 1.70/0.98                [status(thm)],
% 1.70/0.98                [c_801,c_24]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_1855,plain,
% 1.70/0.98      ( u1_struct_0(sK1) = sK2 | v3_tex_2(sK2,sK1) = iProver_top ),
% 1.70/0.98      inference(predicate_to_equality,[status(thm)],[c_803]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_1878,plain,
% 1.70/0.98      ( k2_struct_0(sK1) = sK2 | v3_tex_2(sK2,sK1) = iProver_top ),
% 1.70/0.98      inference(demodulation,[status(thm)],[c_1855,c_817]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_22,negated_conjecture,
% 1.70/0.98      ( ~ v3_tex_2(sK2,sK1) | v1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.70/0.98      inference(cnf_transformation,[],[f74]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_225,plain,
% 1.70/0.98      ( ~ v3_tex_2(sK2,sK1) | v1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.70/0.98      inference(prop_impl,[status(thm)],[c_22]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_522,plain,
% 1.70/0.98      ( ~ v3_tex_2(sK2,sK1)
% 1.70/0.98      | ~ l1_pre_topc(X0)
% 1.70/0.98      | u1_struct_0(X0) != u1_struct_0(sK1)
% 1.70/0.98      | k2_struct_0(X0) != sK2 ),
% 1.70/0.98      inference(resolution_lifted,[status(thm)],[c_382,c_225]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_590,plain,
% 1.70/0.98      ( ~ v3_tex_2(sK2,sK1)
% 1.70/0.98      | u1_struct_0(X0) != u1_struct_0(sK1)
% 1.70/0.98      | k2_struct_0(X0) != sK2
% 1.70/0.98      | sK1 != X0 ),
% 1.70/0.98      inference(resolution_lifted,[status(thm)],[c_522,c_25]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_591,plain,
% 1.70/0.98      ( ~ v3_tex_2(sK2,sK1)
% 1.70/0.98      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.70/0.98      | k2_struct_0(sK1) != sK2 ),
% 1.70/0.98      inference(unflattening,[status(thm)],[c_590]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_1232,plain,
% 1.70/0.98      ( ~ v3_tex_2(sK2,sK1) | k2_struct_0(sK1) != sK2 ),
% 1.70/0.98      inference(equality_resolution_simp,[status(thm)],[c_591]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_1853,plain,
% 1.70/0.98      ( k2_struct_0(sK1) != sK2 | v3_tex_2(sK2,sK1) != iProver_top ),
% 1.70/0.98      inference(predicate_to_equality,[status(thm)],[c_1232]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_32,plain,
% 1.70/0.98      ( l1_pre_topc(sK1) = iProver_top ),
% 1.70/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_33,plain,
% 1.70/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.70/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_79,plain,
% 1.70/0.98      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 1.70/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_81,plain,
% 1.70/0.98      ( l1_pre_topc(sK1) != iProver_top
% 1.70/0.98      | l1_struct_0(sK1) = iProver_top ),
% 1.70/0.98      inference(instantiation,[status(thm)],[c_79]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_82,plain,
% 1.70/0.98      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 1.70/0.98      | l1_struct_0(X0) != iProver_top ),
% 1.70/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_84,plain,
% 1.70/0.98      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 1.70/0.98      | l1_struct_0(sK1) != iProver_top ),
% 1.70/0.98      inference(instantiation,[status(thm)],[c_82]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_523,plain,
% 1.70/0.98      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 1.70/0.98      | k2_struct_0(X0) != sK2
% 1.70/0.98      | v3_tex_2(sK2,sK1) != iProver_top
% 1.70/0.98      | l1_pre_topc(X0) != iProver_top ),
% 1.70/0.98      inference(predicate_to_equality,[status(thm)],[c_522]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_525,plain,
% 1.70/0.98      ( u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.70/0.98      | k2_struct_0(sK1) != sK2
% 1.70/0.98      | v3_tex_2(sK2,sK1) != iProver_top
% 1.70/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 1.70/0.98      inference(instantiation,[status(thm)],[c_523]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_1639,plain,
% 1.70/0.98      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 1.70/0.98      theory(equality) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_1647,plain,
% 1.70/0.98      ( u1_struct_0(sK1) = u1_struct_0(sK1) | sK1 != sK1 ),
% 1.70/0.98      inference(instantiation,[status(thm)],[c_1639]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_1633,plain,( X0 = X0 ),theory(equality) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_1652,plain,
% 1.70/0.98      ( sK1 = sK1 ),
% 1.70/0.98      inference(instantiation,[status(thm)],[c_1633]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_1986,plain,
% 1.70/0.98      ( ~ v3_tex_2(sK2,sK1)
% 1.70/0.98      | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1)))
% 1.70/0.98      | k2_struct_0(sK1) = sK2 ),
% 1.70/0.98      inference(instantiation,[status(thm)],[c_777]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_1987,plain,
% 1.70/0.98      ( k2_struct_0(sK1) = sK2
% 1.70/0.98      | v3_tex_2(sK2,sK1) != iProver_top
% 1.70/0.98      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.70/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.70/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 1.70/0.98      inference(predicate_to_equality,[status(thm)],[c_1986]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_2035,plain,
% 1.70/0.98      ( v3_tex_2(sK2,sK1) != iProver_top ),
% 1.70/0.98      inference(global_propositional_subsumption,
% 1.70/0.98                [status(thm)],
% 1.70/0.98                [c_1853,c_32,c_33,c_81,c_84,c_525,c_1647,c_1652,c_1871,
% 1.70/0.98                 c_1987]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_2374,plain,
% 1.70/0.98      ( k2_struct_0(sK1) = sK2 ),
% 1.70/0.98      inference(global_propositional_subsumption,
% 1.70/0.98                [status(thm)],
% 1.70/0.98                [c_2313,c_32,c_33,c_81,c_84,c_525,c_1647,c_1652,c_1878,
% 1.70/0.98                 c_1871,c_1987]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_2378,plain,
% 1.70/0.98      ( v3_tex_2(sK2,sK1) = iProver_top ),
% 1.70/0.98      inference(demodulation,[status(thm)],[c_2374,c_2221]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(contradiction,plain,
% 1.70/0.98      ( $false ),
% 1.70/0.98      inference(minisat,[status(thm)],[c_2378,c_2035]) ).
% 1.70/0.98  
% 1.70/0.98  
% 1.70/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.70/0.98  
% 1.70/0.98  ------                               Statistics
% 1.70/0.98  
% 1.70/0.98  ------ General
% 1.70/0.98  
% 1.70/0.98  abstr_ref_over_cycles:                  0
% 1.70/0.98  abstr_ref_under_cycles:                 0
% 1.70/0.98  gc_basic_clause_elim:                   0
% 1.70/0.98  forced_gc_time:                         0
% 1.70/0.98  parsing_time:                           0.011
% 1.70/0.98  unif_index_cands_time:                  0.
% 1.70/0.98  unif_index_add_time:                    0.
% 1.70/0.98  orderings_time:                         0.
% 1.70/0.98  out_proof_time:                         0.011
% 1.70/0.98  total_time:                             0.102
% 1.70/0.98  num_of_symbols:                         50
% 1.70/0.98  num_of_terms:                           1237
% 1.70/0.98  
% 1.70/0.98  ------ Preprocessing
% 1.70/0.98  
% 1.70/0.98  num_of_splits:                          0
% 1.70/0.98  num_of_split_atoms:                     0
% 1.70/0.98  num_of_reused_defs:                     0
% 1.70/0.98  num_eq_ax_congr_red:                    12
% 1.70/0.98  num_of_sem_filtered_clauses:            1
% 1.70/0.98  num_of_subtypes:                        0
% 1.70/0.98  monotx_restored_types:                  0
% 1.70/0.98  sat_num_of_epr_types:                   0
% 1.70/0.98  sat_num_of_non_cyclic_types:            0
% 1.70/0.98  sat_guarded_non_collapsed_types:        0
% 1.70/0.98  num_pure_diseq_elim:                    0
% 1.70/0.98  simp_replaced_by:                       0
% 1.70/0.98  res_preprocessed:                       95
% 1.70/0.98  prep_upred:                             0
% 1.70/0.98  prep_unflattend:                        64
% 1.70/0.98  smt_new_axioms:                         0
% 1.70/0.98  pred_elim_cands:                        2
% 1.70/0.98  pred_elim:                              9
% 1.70/0.98  pred_elim_cl:                           14
% 1.70/0.98  pred_elim_cycles:                       11
% 1.70/0.98  merged_defs:                            4
% 1.70/0.98  merged_defs_ncl:                        0
% 1.70/0.98  bin_hyper_res:                          5
% 1.70/0.98  prep_cycles:                            4
% 1.70/0.98  pred_elim_time:                         0.026
% 1.70/0.98  splitting_time:                         0.
% 1.70/0.98  sem_filter_time:                        0.
% 1.70/0.98  monotx_time:                            0.001
% 1.70/0.98  subtype_inf_time:                       0.
% 1.70/0.98  
% 1.70/0.98  ------ Problem properties
% 1.70/0.98  
% 1.70/0.98  clauses:                                15
% 1.70/0.98  conjectures:                            1
% 1.70/0.98  epr:                                    0
% 1.70/0.98  horn:                                   12
% 1.70/0.98  ground:                                 8
% 1.70/0.98  unary:                                  6
% 1.70/0.98  binary:                                 3
% 1.70/0.98  lits:                                   32
% 1.70/0.98  lits_eq:                                10
% 1.70/0.98  fd_pure:                                0
% 1.70/0.98  fd_pseudo:                              0
% 1.70/0.98  fd_cond:                                0
% 1.70/0.98  fd_pseudo_cond:                         1
% 1.70/0.98  ac_symbols:                             0
% 1.70/0.98  
% 1.70/0.98  ------ Propositional Solver
% 1.70/0.98  
% 1.70/0.98  prop_solver_calls:                      23
% 1.70/0.98  prop_fast_solver_calls:                 814
% 1.70/0.98  smt_solver_calls:                       0
% 1.70/0.98  smt_fast_solver_calls:                  0
% 1.70/0.98  prop_num_of_clauses:                    583
% 1.70/0.98  prop_preprocess_simplified:             2696
% 1.70/0.98  prop_fo_subsumed:                       45
% 1.70/0.98  prop_solver_time:                       0.
% 1.70/0.98  smt_solver_time:                        0.
% 1.70/0.98  smt_fast_solver_time:                   0.
% 1.70/0.98  prop_fast_solver_time:                  0.
% 1.70/0.98  prop_unsat_core_time:                   0.
% 1.70/0.98  
% 1.70/0.98  ------ QBF
% 1.70/0.98  
% 1.70/0.98  qbf_q_res:                              0
% 1.70/0.98  qbf_num_tautologies:                    0
% 1.70/0.98  qbf_prep_cycles:                        0
% 1.70/0.98  
% 1.70/0.98  ------ BMC1
% 1.70/0.98  
% 1.70/0.98  bmc1_current_bound:                     -1
% 1.70/0.98  bmc1_last_solved_bound:                 -1
% 1.70/0.98  bmc1_unsat_core_size:                   -1
% 1.70/0.98  bmc1_unsat_core_parents_size:           -1
% 1.70/0.98  bmc1_merge_next_fun:                    0
% 1.70/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.70/0.98  
% 1.70/0.98  ------ Instantiation
% 1.70/0.98  
% 1.70/0.98  inst_num_of_clauses:                    116
% 1.70/0.98  inst_num_in_passive:                    34
% 1.70/0.98  inst_num_in_active:                     65
% 1.70/0.98  inst_num_in_unprocessed:                17
% 1.70/0.98  inst_num_of_loops:                      70
% 1.70/0.98  inst_num_of_learning_restarts:          0
% 1.70/0.98  inst_num_moves_active_passive:          3
% 1.70/0.98  inst_lit_activity:                      0
% 1.70/0.98  inst_lit_activity_moves:                0
% 1.70/0.98  inst_num_tautologies:                   0
% 1.70/0.98  inst_num_prop_implied:                  0
% 1.70/0.98  inst_num_existing_simplified:           0
% 1.70/0.98  inst_num_eq_res_simplified:             0
% 1.70/0.98  inst_num_child_elim:                    0
% 1.70/0.98  inst_num_of_dismatching_blockings:      3
% 1.70/0.98  inst_num_of_non_proper_insts:           76
% 1.70/0.98  inst_num_of_duplicates:                 0
% 1.70/0.98  inst_inst_num_from_inst_to_res:         0
% 1.70/0.98  inst_dismatching_checking_time:         0.
% 1.70/0.98  
% 1.70/0.98  ------ Resolution
% 1.70/0.98  
% 1.70/0.98  res_num_of_clauses:                     0
% 1.70/0.98  res_num_in_passive:                     0
% 1.70/0.98  res_num_in_active:                      0
% 1.70/0.98  res_num_of_loops:                       99
% 1.70/0.98  res_forward_subset_subsumed:            5
% 1.70/0.98  res_backward_subset_subsumed:           0
% 1.70/0.98  res_forward_subsumed:                   3
% 1.70/0.98  res_backward_subsumed:                  0
% 1.70/0.98  res_forward_subsumption_resolution:     0
% 1.70/0.98  res_backward_subsumption_resolution:    0
% 1.70/0.98  res_clause_to_clause_subsumption:       96
% 1.70/0.98  res_orphan_elimination:                 0
% 1.70/0.98  res_tautology_del:                      18
% 1.70/0.98  res_num_eq_res_simplified:              1
% 1.70/0.98  res_num_sel_changes:                    0
% 1.70/0.98  res_moves_from_active_to_pass:          0
% 1.70/0.98  
% 1.70/0.98  ------ Superposition
% 1.70/0.98  
% 1.70/0.98  sup_time_total:                         0.
% 1.70/0.98  sup_time_generating:                    0.
% 1.70/0.98  sup_time_sim_full:                      0.
% 1.70/0.98  sup_time_sim_immed:                     0.
% 1.70/0.98  
% 1.70/0.98  sup_num_of_clauses:                     8
% 1.70/0.98  sup_num_in_active:                      3
% 1.70/0.98  sup_num_in_passive:                     5
% 1.70/0.98  sup_num_of_loops:                       12
% 1.70/0.98  sup_fw_superposition:                   4
% 1.70/0.98  sup_bw_superposition:                   2
% 1.70/0.98  sup_immediate_simplified:               2
% 1.70/0.98  sup_given_eliminated:                   0
% 1.70/0.98  comparisons_done:                       0
% 1.70/0.98  comparisons_avoided:                    0
% 1.70/0.98  
% 1.70/0.98  ------ Simplifications
% 1.70/0.98  
% 1.70/0.98  
% 1.70/0.98  sim_fw_subset_subsumed:                 1
% 1.70/0.98  sim_bw_subset_subsumed:                 2
% 1.70/0.98  sim_fw_subsumed:                        3
% 1.70/0.98  sim_bw_subsumed:                        0
% 1.70/0.98  sim_fw_subsumption_res:                 0
% 1.70/0.98  sim_bw_subsumption_res:                 1
% 1.70/0.98  sim_tautology_del:                      0
% 1.70/0.98  sim_eq_tautology_del:                   1
% 1.70/0.98  sim_eq_res_simp:                        0
% 1.70/0.98  sim_fw_demodulated:                     2
% 1.70/0.98  sim_bw_demodulated:                     8
% 1.70/0.98  sim_light_normalised:                   10
% 1.70/0.98  sim_joinable_taut:                      0
% 1.70/0.98  sim_joinable_simp:                      0
% 1.70/0.98  sim_ac_normalised:                      0
% 1.70/0.98  sim_smt_subsumption:                    0
% 1.70/0.98  
%------------------------------------------------------------------------------
