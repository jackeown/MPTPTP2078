%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:50 EST 2020

% Result     : Theorem 0.36s
% Output     : CNFRefutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  167 (1917 expanded)
%              Number of clauses        :  116 ( 478 expanded)
%              Number of leaves         :   11 ( 506 expanded)
%              Depth                    :   29
%              Number of atoms          :  904 (18216 expanded)
%              Number of equality atoms :   95 ( 279 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   24 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => ~ ( u1_struct_0(X2) = X1
                      & v4_tex_2(X2,X0) ) )
              & v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & v4_tex_2(X2,X0)
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & v4_tex_2(X2,X0)
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & v4_tex_2(X2,X0)
          & m1_pre_topc(X2,X0)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK0(X0,X1)) = X1
        & v4_tex_2(sK0(X0,X1),X0)
        & m1_pre_topc(sK0(X0,X1),X0)
        & v1_pre_topc(sK0(X0,X1))
        & ~ v2_struct_0(sK0(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK0(X0,X1)) = X1
            & v4_tex_2(sK0(X0,X1),X0)
            & m1_pre_topc(sK0(X0,X1),X0)
            & v1_pre_topc(sK0(X0,X1))
            & ~ v2_struct_0(sK0(X0,X1)) )
          | ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f24])).

fof(f41,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK0(X0,X1)) = X1
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
         => ? [X2] :
              ( v4_tex_2(X2,X0)
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( v4_tex_2(X2,X0)
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & v1_pre_topc(X2)
                & ~ v2_struct_0(X2) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & v1_tdlat_3(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & v1_tdlat_3(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & v1_tdlat_3(X1)
          & ~ v2_struct_0(X1) )
     => ( ! [X2] :
            ( ~ v4_tex_2(X2,X0)
            | ~ m1_pre_topc(sK3,X2)
            | ~ m1_pre_topc(X2,X0)
            | ~ v1_pre_topc(X2)
            | v2_struct_0(X2) )
        & m1_pre_topc(sK3,X0)
        & v1_tdlat_3(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( ~ v4_tex_2(X2,X0)
                | ~ m1_pre_topc(X1,X2)
                | ~ m1_pre_topc(X2,X0)
                | ~ v1_pre_topc(X2)
                | v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( ~ v4_tex_2(X2,sK2)
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,sK2)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & m1_pre_topc(X1,sK2)
          & v1_tdlat_3(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v3_tdlat_3(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ! [X2] :
        ( ~ v4_tex_2(X2,sK2)
        | ~ m1_pre_topc(sK3,X2)
        | ~ m1_pre_topc(X2,sK2)
        | ~ v1_pre_topc(X2)
        | v2_struct_0(X2) )
    & m1_pre_topc(sK3,sK2)
    & v1_tdlat_3(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v3_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f29,f28])).

fof(f46,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f50,plain,(
    v1_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f51,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ~ ( v3_tex_2(X2,X0)
                      & r1_tarski(X1,X2) ) )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v3_tex_2(X2,X0)
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_tex_2(sK1(X0,X1),X0)
        & r1_tarski(X1,sK1(X0,X1))
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(sK1(X0,X1),X0)
            & r1_tarski(X1,sK1(X0,X1))
            & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f26])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v3_tex_2(sK1(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,sK1(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK0(X0,X1),X0)
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK0(X0,X1))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(sK0(X0,X1))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v4_tex_2(sK0(X0,X1),X0)
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X2] :
      ( ~ v4_tex_2(X2,sK2)
      | ~ m1_pre_topc(sK3,X2)
      | ~ m1_pre_topc(X2,sK2)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_6,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(sK0(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_5,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_150,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(sK0(X1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6,c_5])).

cnf(c_151,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(sK0(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_150])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_648,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(sK0(X1,X0)) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_151,c_20])).

cnf(c_649,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(sK0(sK2,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_648])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_653,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(sK0(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_649,c_21,c_18])).

cnf(c_3,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_165,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_tex_2(u1_struct_0(X0),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3,c_0])).

cnf(c_166,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_165])).

cnf(c_796,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_166,c_18])).

cnf(c_797,plain,
    ( v2_tex_2(u1_struct_0(X0),sK2)
    | ~ m1_pre_topc(X0,sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ v1_tdlat_3(X0) ),
    inference(unflattening,[status(thm)],[c_796])).

cnf(c_801,plain,
    ( v2_struct_0(X0)
    | ~ m1_pre_topc(X0,sK2)
    | v2_tex_2(u1_struct_0(X0),sK2)
    | ~ v1_tdlat_3(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_797,c_21])).

cnf(c_802,plain,
    ( v2_tex_2(u1_struct_0(X0),sK2)
    | ~ m1_pre_topc(X0,sK2)
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0) ),
    inference(renaming,[status(thm)],[c_801])).

cnf(c_16,negated_conjecture,
    ( v1_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_868,plain,
    ( v2_tex_2(u1_struct_0(X0),sK2)
    | ~ m1_pre_topc(X0,sK2)
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_802,c_16])).

cnf(c_869,plain,
    ( v2_tex_2(u1_struct_0(sK3),sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_868])).

cnf(c_17,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_15,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_472,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_166,c_16])).

cnf(c_473,plain,
    ( v2_tex_2(u1_struct_0(sK3),X0)
    | ~ m1_pre_topc(sK3,X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_475,plain,
    ( v2_tex_2(u1_struct_0(sK3),sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_473])).

cnf(c_871,plain,
    ( v2_tex_2(u1_struct_0(sK3),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_869,c_21,c_18,c_17,c_15,c_475])).

cnf(c_11,plain,
    ( v3_tex_2(sK1(X0,X1),X0)
    | ~ v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_tdlat_3(X0)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_19,negated_conjecture,
    ( v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_551,plain,
    ( v3_tex_2(sK1(X0,X1),X0)
    | ~ v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_19])).

cnf(c_552,plain,
    ( v3_tex_2(sK1(sK2,X0),sK2)
    | ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_551])).

cnf(c_556,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | v3_tex_2(sK1(sK2,X0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_552,c_21,c_20,c_18])).

cnf(c_557,plain,
    ( v3_tex_2(sK1(sK2,X0),sK2)
    | ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_556])).

cnf(c_881,plain,
    ( v3_tex_2(sK1(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(sK3) != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_871,c_557])).

cnf(c_882,plain,
    ( v3_tex_2(sK1(sK2,u1_struct_0(sK3)),sK2)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_881])).

cnf(c_963,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK1(sK2,u1_struct_0(sK3)) != X0
    | u1_struct_0(sK0(sK2,X0)) = X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_653,c_882])).

cnf(c_964,plain,
    ( ~ m1_subset_1(sK1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(sK0(sK2,sK1(sK2,u1_struct_0(sK3)))) = sK1(sK2,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_963])).

cnf(c_13,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_509,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_510,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_509])).

cnf(c_514,plain,
    ( m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_510,c_21,c_20,c_18])).

cnf(c_515,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_514])).

cnf(c_891,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(sK3) != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_871,c_515])).

cnf(c_892,plain,
    ( m1_subset_1(sK1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_891])).

cnf(c_966,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(sK0(sK2,sK1(sK2,u1_struct_0(sK3)))) = sK1(sK2,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_964,c_892])).

cnf(c_1044,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(sK0(sK2,sK1(sK2,u1_struct_0(sK3)))) = sK1(sK2,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_966])).

cnf(c_1210,plain,
    ( u1_struct_0(sK0(sK2,sK1(sK2,u1_struct_0(sK3)))) = sK1(sK2,u1_struct_0(sK3))
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1044])).

cnf(c_840,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_18])).

cnf(c_841,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_840])).

cnf(c_1048,plain,
    ( ~ m1_pre_topc(X0_47,sK2)
    | m1_subset_1(u1_struct_0(X0_47),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_841])).

cnf(c_1260,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_1048])).

cnf(c_1347,plain,
    ( u1_struct_0(sK0(sK2,sK1(sK2,u1_struct_0(sK3)))) = sK1(sK2,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1210,c_15,c_1044,c_1260])).

cnf(c_2,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_12,plain,
    ( ~ v2_tex_2(X0,X1)
    | r1_tarski(X0,sK1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_530,plain,
    ( ~ v2_tex_2(X0,X1)
    | r1_tarski(X0,sK1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_531,plain,
    ( ~ v2_tex_2(X0,sK2)
    | r1_tarski(X0,sK1(sK2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_535,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(X0,sK1(sK2,X0))
    | ~ v2_tex_2(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_531,c_21,c_20,c_18])).

cnf(c_536,plain,
    ( ~ v2_tex_2(X0,sK2)
    | r1_tarski(X0,sK1(sK2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_535])).

cnf(c_585,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X3,X2)
    | m1_pre_topc(X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | sK1(sK2,X0) != u1_struct_0(X3)
    | u1_struct_0(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_536])).

cnf(c_586,plain,
    ( ~ v2_tex_2(u1_struct_0(X0),sK2)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1(sK2,u1_struct_0(X0)) != u1_struct_0(X2) ),
    inference(unflattening,[status(thm)],[c_585])).

cnf(c_622,plain,
    ( ~ v2_tex_2(u1_struct_0(X0),sK2)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X1)
    | sK1(sK2,u1_struct_0(X0)) != u1_struct_0(X2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_586,c_20])).

cnf(c_623,plain,
    ( ~ v2_tex_2(u1_struct_0(X0),sK2)
    | m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | sK1(sK2,u1_struct_0(X0)) != u1_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_622])).

cnf(c_625,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | m1_pre_topc(X0,X1)
    | ~ v2_tex_2(u1_struct_0(X0),sK2)
    | sK1(sK2,u1_struct_0(X0)) != u1_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_623,c_18])).

cnf(c_626,plain,
    ( ~ v2_tex_2(u1_struct_0(X0),sK2)
    | m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK1(sK2,u1_struct_0(X0)) != u1_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_625])).

cnf(c_864,plain,
    ( ~ v2_tex_2(u1_struct_0(X0),sK2)
    | m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | sK1(sK2,u1_struct_0(X0)) != u1_struct_0(X1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_841,c_626])).

cnf(c_901,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | sK1(sK2,u1_struct_0(X0)) != u1_struct_0(X1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_871,c_864])).

cnf(c_996,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | sK1(sK2,u1_struct_0(X0)) != u1_struct_0(X1)
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(equality_resolution_simp,[status(thm)],[c_901])).

cnf(c_1043,plain,
    ( m1_pre_topc(X0_47,X1_47)
    | ~ m1_pre_topc(X0_47,sK2)
    | ~ m1_pre_topc(X1_47,sK2)
    | sK1(sK2,u1_struct_0(X0_47)) != u1_struct_0(X1_47)
    | u1_struct_0(X0_47) != u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_996])).

cnf(c_1211,plain,
    ( sK1(sK2,u1_struct_0(X0_47)) != u1_struct_0(X1_47)
    | u1_struct_0(X0_47) != u1_struct_0(sK3)
    | m1_pre_topc(X0_47,X1_47) = iProver_top
    | m1_pre_topc(X0_47,sK2) != iProver_top
    | m1_pre_topc(X1_47,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1043])).

cnf(c_1416,plain,
    ( sK1(sK2,u1_struct_0(X0_47)) != sK1(sK2,u1_struct_0(sK3))
    | u1_struct_0(X0_47) != u1_struct_0(sK3)
    | m1_pre_topc(X0_47,sK0(sK2,sK1(sK2,u1_struct_0(sK3)))) = iProver_top
    | m1_pre_topc(X0_47,sK2) != iProver_top
    | m1_pre_topc(sK0(sK2,sK1(sK2,u1_struct_0(sK3))),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1347,c_1211])).

cnf(c_28,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8,plain,
    ( ~ v3_tex_2(X0,X1)
    | m1_pre_topc(sK0(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_142,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_pre_topc(sK0(X1,X0),X1)
    | ~ v3_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_5])).

cnf(c_143,plain,
    ( ~ v3_tex_2(X0,X1)
    | m1_pre_topc(sK0(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_142])).

cnf(c_669,plain,
    ( ~ v3_tex_2(X0,X1)
    | m1_pre_topc(sK0(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_143,c_20])).

cnf(c_670,plain,
    ( ~ v3_tex_2(X0,sK2)
    | m1_pre_topc(sK0(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_669])).

cnf(c_674,plain,
    ( ~ v3_tex_2(X0,sK2)
    | m1_pre_topc(sK0(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_670,c_21,c_18])).

cnf(c_949,plain,
    ( m1_pre_topc(sK0(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK1(sK2,u1_struct_0(sK3)) != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_674,c_882])).

cnf(c_950,plain,
    ( m1_pre_topc(sK0(sK2,sK1(sK2,u1_struct_0(sK3))),sK2)
    | ~ m1_subset_1(sK1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_949])).

cnf(c_952,plain,
    ( m1_pre_topc(sK0(sK2,sK1(sK2,u1_struct_0(sK3))),sK2)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_950,c_892])).

cnf(c_954,plain,
    ( m1_pre_topc(sK0(sK2,sK1(sK2,u1_struct_0(sK3))),sK2) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_952])).

cnf(c_1261,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1260])).

cnf(c_1443,plain,
    ( m1_pre_topc(X0_47,sK2) != iProver_top
    | m1_pre_topc(X0_47,sK0(sK2,sK1(sK2,u1_struct_0(sK3)))) = iProver_top
    | u1_struct_0(X0_47) != u1_struct_0(sK3)
    | sK1(sK2,u1_struct_0(X0_47)) != sK1(sK2,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1416,c_28,c_954,c_1261])).

cnf(c_1444,plain,
    ( sK1(sK2,u1_struct_0(X0_47)) != sK1(sK2,u1_struct_0(sK3))
    | u1_struct_0(X0_47) != u1_struct_0(sK3)
    | m1_pre_topc(X0_47,sK0(sK2,sK1(sK2,u1_struct_0(sK3)))) = iProver_top
    | m1_pre_topc(X0_47,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_1443])).

cnf(c_1454,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | m1_pre_topc(sK3,sK0(sK2,sK1(sK2,u1_struct_0(sK3)))) = iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1444])).

cnf(c_1455,plain,
    ( m1_pre_topc(sK3,sK0(sK2,sK1(sK2,u1_struct_0(sK3)))) = iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1454])).

cnf(c_732,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_20])).

cnf(c_733,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_xboole_0(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_732])).

cnf(c_737,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_733,c_21,c_18])).

cnf(c_10,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK0(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_128,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK0(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_5])).

cnf(c_129,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK0(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_128])).

cnf(c_711,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK0(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_129,c_20])).

cnf(c_712,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_struct_0(sK0(sK2,X0))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_711])).

cnf(c_716,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_struct_0(sK0(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_712,c_21,c_18])).

cnf(c_9,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_pre_topc(sK0(X1,X0))
    | v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_135,plain,
    ( v1_pre_topc(sK0(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_5])).

cnf(c_136,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_pre_topc(sK0(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_135])).

cnf(c_690,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_pre_topc(sK0(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_136,c_20])).

cnf(c_691,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_pre_topc(sK0(sK2,X0))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_690])).

cnf(c_695,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_pre_topc(sK0(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_691,c_21,c_18])).

cnf(c_7,plain,
    ( v4_tex_2(sK0(X0,X1),X0)
    | ~ v3_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v1_xboole_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_14,negated_conjecture,
    ( ~ v4_tex_2(X0,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(sK3,X0)
    | ~ v1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_322,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_pre_topc(X2,sK2)
    | ~ m1_pre_topc(sK3,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_pre_topc(X2)
    | v1_xboole_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_14])).

cnf(c_323,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_pre_topc(sK0(sK2,X0),sK2)
    | ~ m1_pre_topc(sK3,sK0(sK2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_pre_topc(sK0(sK2,X0))
    | v1_xboole_0(X0)
    | v2_struct_0(sK0(sK2,X0))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_322])).

cnf(c_327,plain,
    ( v2_struct_0(sK0(sK2,X0))
    | v1_xboole_0(X0)
    | ~ v1_pre_topc(sK0(sK2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK3,sK0(sK2,X0))
    | ~ m1_pre_topc(sK0(sK2,X0),sK2)
    | ~ v3_tex_2(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_323,c_21,c_20,c_18])).

cnf(c_328,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_pre_topc(sK0(sK2,X0),sK2)
    | ~ m1_pre_topc(sK3,sK0(sK2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_pre_topc(sK0(sK2,X0))
    | v1_xboole_0(X0)
    | v2_struct_0(sK0(sK2,X0)) ),
    inference(renaming,[status(thm)],[c_327])).

cnf(c_766,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_pre_topc(sK3,sK0(sK2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_pre_topc(sK0(sK2,X0))
    | v1_xboole_0(X0)
    | v2_struct_0(sK0(sK2,X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_674,c_328])).

cnf(c_775,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_pre_topc(sK3,sK0(sK2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | v2_struct_0(sK0(sK2,X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_695,c_766])).

cnf(c_783,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_pre_topc(sK3,sK0(sK2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_716,c_775])).

cnf(c_791,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_pre_topc(sK3,sK0(sK2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_737,c_783])).

cnf(c_935,plain,
    ( ~ m1_pre_topc(sK3,sK0(sK2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK1(sK2,u1_struct_0(sK3)) != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_791,c_882])).

cnf(c_936,plain,
    ( ~ m1_pre_topc(sK3,sK0(sK2,sK1(sK2,u1_struct_0(sK3))))
    | ~ m1_subset_1(sK1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_935])).

cnf(c_938,plain,
    ( ~ m1_pre_topc(sK3,sK0(sK2,sK1(sK2,u1_struct_0(sK3))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_936,c_892])).

cnf(c_940,plain,
    ( m1_pre_topc(sK3,sK0(sK2,sK1(sK2,u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_938])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1455,c_1261,c_940,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:24:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 0.36/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.36/1.04  
% 0.36/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.36/1.04  
% 0.36/1.04  ------  iProver source info
% 0.36/1.04  
% 0.36/1.04  git: date: 2020-06-30 10:37:57 +0100
% 0.36/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.36/1.04  git: non_committed_changes: false
% 0.36/1.04  git: last_make_outside_of_git: false
% 0.36/1.04  
% 0.36/1.04  ------ 
% 0.36/1.04  
% 0.36/1.04  ------ Input Options
% 0.36/1.04  
% 0.36/1.04  --out_options                           all
% 0.36/1.04  --tptp_safe_out                         true
% 0.36/1.04  --problem_path                          ""
% 0.36/1.04  --include_path                          ""
% 0.36/1.04  --clausifier                            res/vclausify_rel
% 0.36/1.04  --clausifier_options                    --mode clausify
% 0.36/1.04  --stdin                                 false
% 0.36/1.04  --stats_out                             all
% 0.36/1.04  
% 0.36/1.04  ------ General Options
% 0.36/1.04  
% 0.36/1.04  --fof                                   false
% 0.36/1.04  --time_out_real                         305.
% 0.36/1.04  --time_out_virtual                      -1.
% 0.36/1.04  --symbol_type_check                     false
% 0.36/1.04  --clausify_out                          false
% 0.36/1.04  --sig_cnt_out                           false
% 0.36/1.04  --trig_cnt_out                          false
% 0.36/1.04  --trig_cnt_out_tolerance                1.
% 0.36/1.04  --trig_cnt_out_sk_spl                   false
% 0.36/1.04  --abstr_cl_out                          false
% 0.36/1.04  
% 0.36/1.04  ------ Global Options
% 0.36/1.04  
% 0.36/1.04  --schedule                              default
% 0.36/1.04  --add_important_lit                     false
% 0.36/1.04  --prop_solver_per_cl                    1000
% 0.36/1.04  --min_unsat_core                        false
% 0.36/1.04  --soft_assumptions                      false
% 0.36/1.04  --soft_lemma_size                       3
% 0.36/1.04  --prop_impl_unit_size                   0
% 0.36/1.04  --prop_impl_unit                        []
% 0.36/1.04  --share_sel_clauses                     true
% 0.36/1.04  --reset_solvers                         false
% 0.36/1.04  --bc_imp_inh                            [conj_cone]
% 0.36/1.04  --conj_cone_tolerance                   3.
% 0.36/1.04  --extra_neg_conj                        none
% 0.36/1.04  --large_theory_mode                     true
% 0.36/1.04  --prolific_symb_bound                   200
% 0.36/1.04  --lt_threshold                          2000
% 0.36/1.04  --clause_weak_htbl                      true
% 0.36/1.04  --gc_record_bc_elim                     false
% 0.36/1.04  
% 0.36/1.04  ------ Preprocessing Options
% 0.36/1.04  
% 0.36/1.04  --preprocessing_flag                    true
% 0.36/1.04  --time_out_prep_mult                    0.1
% 0.36/1.04  --splitting_mode                        input
% 0.36/1.04  --splitting_grd                         true
% 0.36/1.04  --splitting_cvd                         false
% 0.36/1.04  --splitting_cvd_svl                     false
% 0.36/1.04  --splitting_nvd                         32
% 0.36/1.04  --sub_typing                            true
% 0.36/1.04  --prep_gs_sim                           true
% 0.36/1.04  --prep_unflatten                        true
% 0.36/1.04  --prep_res_sim                          true
% 0.36/1.04  --prep_upred                            true
% 0.36/1.04  --prep_sem_filter                       exhaustive
% 0.36/1.04  --prep_sem_filter_out                   false
% 0.36/1.04  --pred_elim                             true
% 0.36/1.04  --res_sim_input                         true
% 0.36/1.04  --eq_ax_congr_red                       true
% 0.36/1.04  --pure_diseq_elim                       true
% 0.36/1.04  --brand_transform                       false
% 0.36/1.04  --non_eq_to_eq                          false
% 0.36/1.04  --prep_def_merge                        true
% 0.36/1.04  --prep_def_merge_prop_impl              false
% 0.36/1.04  --prep_def_merge_mbd                    true
% 0.36/1.04  --prep_def_merge_tr_red                 false
% 0.36/1.04  --prep_def_merge_tr_cl                  false
% 0.36/1.04  --smt_preprocessing                     true
% 0.36/1.04  --smt_ac_axioms                         fast
% 0.36/1.04  --preprocessed_out                      false
% 0.36/1.04  --preprocessed_stats                    false
% 0.36/1.04  
% 0.36/1.04  ------ Abstraction refinement Options
% 0.36/1.04  
% 0.36/1.04  --abstr_ref                             []
% 0.36/1.04  --abstr_ref_prep                        false
% 0.36/1.04  --abstr_ref_until_sat                   false
% 0.36/1.04  --abstr_ref_sig_restrict                funpre
% 0.36/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.36/1.04  --abstr_ref_under                       []
% 0.36/1.04  
% 0.36/1.04  ------ SAT Options
% 0.36/1.04  
% 0.36/1.04  --sat_mode                              false
% 0.36/1.04  --sat_fm_restart_options                ""
% 0.36/1.04  --sat_gr_def                            false
% 0.36/1.04  --sat_epr_types                         true
% 0.36/1.04  --sat_non_cyclic_types                  false
% 0.36/1.04  --sat_finite_models                     false
% 0.36/1.04  --sat_fm_lemmas                         false
% 0.36/1.04  --sat_fm_prep                           false
% 0.36/1.04  --sat_fm_uc_incr                        true
% 0.36/1.04  --sat_out_model                         small
% 0.36/1.04  --sat_out_clauses                       false
% 0.36/1.04  
% 0.36/1.04  ------ QBF Options
% 0.36/1.04  
% 0.36/1.04  --qbf_mode                              false
% 0.36/1.04  --qbf_elim_univ                         false
% 0.36/1.04  --qbf_dom_inst                          none
% 0.36/1.04  --qbf_dom_pre_inst                      false
% 0.36/1.04  --qbf_sk_in                             false
% 0.36/1.04  --qbf_pred_elim                         true
% 0.36/1.04  --qbf_split                             512
% 0.36/1.04  
% 0.36/1.04  ------ BMC1 Options
% 0.36/1.04  
% 0.36/1.04  --bmc1_incremental                      false
% 0.36/1.04  --bmc1_axioms                           reachable_all
% 0.36/1.04  --bmc1_min_bound                        0
% 0.36/1.04  --bmc1_max_bound                        -1
% 0.36/1.04  --bmc1_max_bound_default                -1
% 0.36/1.04  --bmc1_symbol_reachability              true
% 0.36/1.04  --bmc1_property_lemmas                  false
% 0.36/1.04  --bmc1_k_induction                      false
% 0.36/1.04  --bmc1_non_equiv_states                 false
% 0.36/1.04  --bmc1_deadlock                         false
% 0.36/1.04  --bmc1_ucm                              false
% 0.36/1.04  --bmc1_add_unsat_core                   none
% 0.36/1.04  --bmc1_unsat_core_children              false
% 0.36/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.36/1.04  --bmc1_out_stat                         full
% 0.36/1.04  --bmc1_ground_init                      false
% 0.36/1.04  --bmc1_pre_inst_next_state              false
% 0.36/1.04  --bmc1_pre_inst_state                   false
% 0.36/1.04  --bmc1_pre_inst_reach_state             false
% 0.36/1.04  --bmc1_out_unsat_core                   false
% 0.36/1.04  --bmc1_aig_witness_out                  false
% 0.36/1.04  --bmc1_verbose                          false
% 0.36/1.04  --bmc1_dump_clauses_tptp                false
% 0.36/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.36/1.04  --bmc1_dump_file                        -
% 0.36/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.36/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.36/1.04  --bmc1_ucm_extend_mode                  1
% 0.36/1.04  --bmc1_ucm_init_mode                    2
% 0.36/1.04  --bmc1_ucm_cone_mode                    none
% 0.36/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.36/1.04  --bmc1_ucm_relax_model                  4
% 0.36/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.36/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.36/1.04  --bmc1_ucm_layered_model                none
% 0.36/1.04  --bmc1_ucm_max_lemma_size               10
% 0.36/1.04  
% 0.36/1.04  ------ AIG Options
% 0.36/1.04  
% 0.36/1.04  --aig_mode                              false
% 0.36/1.04  
% 0.36/1.04  ------ Instantiation Options
% 0.36/1.04  
% 0.36/1.04  --instantiation_flag                    true
% 0.36/1.04  --inst_sos_flag                         false
% 0.36/1.04  --inst_sos_phase                        true
% 0.36/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.36/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.36/1.04  --inst_lit_sel_side                     num_symb
% 0.36/1.04  --inst_solver_per_active                1400
% 0.36/1.04  --inst_solver_calls_frac                1.
% 0.36/1.04  --inst_passive_queue_type               priority_queues
% 0.36/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.36/1.04  --inst_passive_queues_freq              [25;2]
% 0.36/1.04  --inst_dismatching                      true
% 0.36/1.04  --inst_eager_unprocessed_to_passive     true
% 0.36/1.04  --inst_prop_sim_given                   true
% 0.36/1.04  --inst_prop_sim_new                     false
% 0.36/1.04  --inst_subs_new                         false
% 0.36/1.04  --inst_eq_res_simp                      false
% 0.36/1.04  --inst_subs_given                       false
% 0.36/1.04  --inst_orphan_elimination               true
% 0.36/1.04  --inst_learning_loop_flag               true
% 0.36/1.04  --inst_learning_start                   3000
% 0.36/1.04  --inst_learning_factor                  2
% 0.36/1.04  --inst_start_prop_sim_after_learn       3
% 0.36/1.04  --inst_sel_renew                        solver
% 0.36/1.04  --inst_lit_activity_flag                true
% 0.36/1.04  --inst_restr_to_given                   false
% 0.36/1.04  --inst_activity_threshold               500
% 0.36/1.04  --inst_out_proof                        true
% 0.36/1.04  
% 0.36/1.04  ------ Resolution Options
% 0.36/1.04  
% 0.36/1.04  --resolution_flag                       true
% 0.36/1.04  --res_lit_sel                           adaptive
% 0.36/1.04  --res_lit_sel_side                      none
% 0.36/1.04  --res_ordering                          kbo
% 0.36/1.04  --res_to_prop_solver                    active
% 0.36/1.04  --res_prop_simpl_new                    false
% 0.36/1.04  --res_prop_simpl_given                  true
% 0.36/1.04  --res_passive_queue_type                priority_queues
% 0.36/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.36/1.04  --res_passive_queues_freq               [15;5]
% 0.36/1.04  --res_forward_subs                      full
% 0.36/1.04  --res_backward_subs                     full
% 0.36/1.04  --res_forward_subs_resolution           true
% 0.36/1.04  --res_backward_subs_resolution          true
% 0.36/1.04  --res_orphan_elimination                true
% 0.36/1.04  --res_time_limit                        2.
% 0.36/1.04  --res_out_proof                         true
% 0.36/1.04  
% 0.36/1.04  ------ Superposition Options
% 0.36/1.04  
% 0.36/1.04  --superposition_flag                    true
% 0.36/1.04  --sup_passive_queue_type                priority_queues
% 0.36/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.36/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.36/1.04  --demod_completeness_check              fast
% 0.36/1.04  --demod_use_ground                      true
% 0.36/1.04  --sup_to_prop_solver                    passive
% 0.36/1.04  --sup_prop_simpl_new                    true
% 0.36/1.04  --sup_prop_simpl_given                  true
% 0.36/1.04  --sup_fun_splitting                     false
% 0.36/1.04  --sup_smt_interval                      50000
% 0.36/1.04  
% 0.36/1.04  ------ Superposition Simplification Setup
% 0.36/1.04  
% 0.36/1.04  --sup_indices_passive                   []
% 0.36/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.36/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.04  --sup_full_bw                           [BwDemod]
% 0.36/1.04  --sup_immed_triv                        [TrivRules]
% 0.36/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.36/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.04  --sup_immed_bw_main                     []
% 0.36/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.36/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.36/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.36/1.04  
% 0.36/1.04  ------ Combination Options
% 0.36/1.04  
% 0.36/1.04  --comb_res_mult                         3
% 0.36/1.04  --comb_sup_mult                         2
% 0.36/1.04  --comb_inst_mult                        10
% 0.36/1.04  
% 0.36/1.04  ------ Debug Options
% 0.36/1.04  
% 0.36/1.04  --dbg_backtrace                         false
% 0.36/1.04  --dbg_dump_prop_clauses                 false
% 0.36/1.04  --dbg_dump_prop_clauses_file            -
% 0.36/1.04  --dbg_out_stat                          false
% 0.36/1.04  ------ Parsing...
% 0.36/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.36/1.04  
% 0.36/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 11 0s  sf_e  pe_s  pe_e 
% 0.36/1.04  
% 0.36/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.36/1.04  
% 0.36/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.36/1.04  ------ Proving...
% 0.36/1.04  ------ Problem Properties 
% 0.36/1.04  
% 0.36/1.04  
% 0.36/1.04  clauses                                 7
% 0.36/1.04  conjectures                             1
% 0.36/1.04  EPR                                     1
% 0.36/1.04  Horn                                    7
% 0.36/1.04  unary                                   1
% 0.36/1.04  binary                                  5
% 0.36/1.04  lits                                    16
% 0.36/1.04  lits eq                                 3
% 0.36/1.04  fd_pure                                 0
% 0.36/1.04  fd_pseudo                               0
% 0.36/1.04  fd_cond                                 0
% 0.36/1.04  fd_pseudo_cond                          0
% 0.36/1.04  AC symbols                              0
% 0.36/1.04  
% 0.36/1.04  ------ Schedule dynamic 5 is on 
% 0.36/1.04  
% 0.36/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.36/1.04  
% 0.36/1.04  
% 0.36/1.04  ------ 
% 0.36/1.04  Current options:
% 0.36/1.04  ------ 
% 0.36/1.04  
% 0.36/1.04  ------ Input Options
% 0.36/1.04  
% 0.36/1.04  --out_options                           all
% 0.36/1.04  --tptp_safe_out                         true
% 0.36/1.04  --problem_path                          ""
% 0.36/1.04  --include_path                          ""
% 0.36/1.04  --clausifier                            res/vclausify_rel
% 0.36/1.04  --clausifier_options                    --mode clausify
% 0.36/1.04  --stdin                                 false
% 0.36/1.04  --stats_out                             all
% 0.36/1.04  
% 0.36/1.04  ------ General Options
% 0.36/1.04  
% 0.36/1.04  --fof                                   false
% 0.36/1.04  --time_out_real                         305.
% 0.36/1.04  --time_out_virtual                      -1.
% 0.36/1.04  --symbol_type_check                     false
% 0.36/1.04  --clausify_out                          false
% 0.36/1.04  --sig_cnt_out                           false
% 0.36/1.04  --trig_cnt_out                          false
% 0.36/1.04  --trig_cnt_out_tolerance                1.
% 0.36/1.04  --trig_cnt_out_sk_spl                   false
% 0.36/1.04  --abstr_cl_out                          false
% 0.36/1.04  
% 0.36/1.04  ------ Global Options
% 0.36/1.04  
% 0.36/1.04  --schedule                              default
% 0.36/1.04  --add_important_lit                     false
% 0.36/1.04  --prop_solver_per_cl                    1000
% 0.36/1.04  --min_unsat_core                        false
% 0.36/1.04  --soft_assumptions                      false
% 0.36/1.04  --soft_lemma_size                       3
% 0.36/1.04  --prop_impl_unit_size                   0
% 0.36/1.04  --prop_impl_unit                        []
% 0.36/1.04  --share_sel_clauses                     true
% 0.36/1.04  --reset_solvers                         false
% 0.36/1.04  --bc_imp_inh                            [conj_cone]
% 0.36/1.04  --conj_cone_tolerance                   3.
% 0.36/1.04  --extra_neg_conj                        none
% 0.36/1.04  --large_theory_mode                     true
% 0.36/1.04  --prolific_symb_bound                   200
% 0.36/1.04  --lt_threshold                          2000
% 0.36/1.04  --clause_weak_htbl                      true
% 0.36/1.04  --gc_record_bc_elim                     false
% 0.36/1.04  
% 0.36/1.04  ------ Preprocessing Options
% 0.36/1.04  
% 0.36/1.04  --preprocessing_flag                    true
% 0.36/1.04  --time_out_prep_mult                    0.1
% 0.36/1.04  --splitting_mode                        input
% 0.36/1.04  --splitting_grd                         true
% 0.36/1.04  --splitting_cvd                         false
% 0.36/1.04  --splitting_cvd_svl                     false
% 0.36/1.04  --splitting_nvd                         32
% 0.36/1.04  --sub_typing                            true
% 0.36/1.04  --prep_gs_sim                           true
% 0.36/1.04  --prep_unflatten                        true
% 0.36/1.04  --prep_res_sim                          true
% 0.36/1.04  --prep_upred                            true
% 0.36/1.04  --prep_sem_filter                       exhaustive
% 0.36/1.04  --prep_sem_filter_out                   false
% 0.36/1.04  --pred_elim                             true
% 0.36/1.04  --res_sim_input                         true
% 0.36/1.04  --eq_ax_congr_red                       true
% 0.36/1.04  --pure_diseq_elim                       true
% 0.36/1.04  --brand_transform                       false
% 0.36/1.04  --non_eq_to_eq                          false
% 0.36/1.04  --prep_def_merge                        true
% 0.36/1.04  --prep_def_merge_prop_impl              false
% 0.36/1.04  --prep_def_merge_mbd                    true
% 0.36/1.04  --prep_def_merge_tr_red                 false
% 0.36/1.04  --prep_def_merge_tr_cl                  false
% 0.36/1.04  --smt_preprocessing                     true
% 0.36/1.04  --smt_ac_axioms                         fast
% 0.36/1.04  --preprocessed_out                      false
% 0.36/1.04  --preprocessed_stats                    false
% 0.36/1.04  
% 0.36/1.04  ------ Abstraction refinement Options
% 0.36/1.04  
% 0.36/1.04  --abstr_ref                             []
% 0.36/1.04  --abstr_ref_prep                        false
% 0.36/1.04  --abstr_ref_until_sat                   false
% 0.36/1.04  --abstr_ref_sig_restrict                funpre
% 0.36/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.36/1.04  --abstr_ref_under                       []
% 0.36/1.04  
% 0.36/1.04  ------ SAT Options
% 0.36/1.04  
% 0.36/1.04  --sat_mode                              false
% 0.36/1.04  --sat_fm_restart_options                ""
% 0.36/1.04  --sat_gr_def                            false
% 0.36/1.04  --sat_epr_types                         true
% 0.36/1.04  --sat_non_cyclic_types                  false
% 0.36/1.04  --sat_finite_models                     false
% 0.36/1.04  --sat_fm_lemmas                         false
% 0.36/1.04  --sat_fm_prep                           false
% 0.36/1.04  --sat_fm_uc_incr                        true
% 0.36/1.04  --sat_out_model                         small
% 0.36/1.04  --sat_out_clauses                       false
% 0.36/1.04  
% 0.36/1.04  ------ QBF Options
% 0.36/1.04  
% 0.36/1.04  --qbf_mode                              false
% 0.36/1.04  --qbf_elim_univ                         false
% 0.36/1.04  --qbf_dom_inst                          none
% 0.36/1.04  --qbf_dom_pre_inst                      false
% 0.36/1.04  --qbf_sk_in                             false
% 0.36/1.04  --qbf_pred_elim                         true
% 0.36/1.04  --qbf_split                             512
% 0.36/1.04  
% 0.36/1.04  ------ BMC1 Options
% 0.36/1.04  
% 0.36/1.04  --bmc1_incremental                      false
% 0.36/1.04  --bmc1_axioms                           reachable_all
% 0.36/1.04  --bmc1_min_bound                        0
% 0.36/1.04  --bmc1_max_bound                        -1
% 0.36/1.04  --bmc1_max_bound_default                -1
% 0.36/1.04  --bmc1_symbol_reachability              true
% 0.36/1.04  --bmc1_property_lemmas                  false
% 0.36/1.04  --bmc1_k_induction                      false
% 0.36/1.04  --bmc1_non_equiv_states                 false
% 0.36/1.04  --bmc1_deadlock                         false
% 0.36/1.04  --bmc1_ucm                              false
% 0.36/1.04  --bmc1_add_unsat_core                   none
% 0.36/1.04  --bmc1_unsat_core_children              false
% 0.36/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.36/1.04  --bmc1_out_stat                         full
% 0.36/1.04  --bmc1_ground_init                      false
% 0.36/1.04  --bmc1_pre_inst_next_state              false
% 0.36/1.04  --bmc1_pre_inst_state                   false
% 0.36/1.04  --bmc1_pre_inst_reach_state             false
% 0.36/1.04  --bmc1_out_unsat_core                   false
% 0.36/1.04  --bmc1_aig_witness_out                  false
% 0.36/1.04  --bmc1_verbose                          false
% 0.36/1.04  --bmc1_dump_clauses_tptp                false
% 0.36/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.36/1.04  --bmc1_dump_file                        -
% 0.36/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.36/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.36/1.04  --bmc1_ucm_extend_mode                  1
% 0.36/1.04  --bmc1_ucm_init_mode                    2
% 0.36/1.04  --bmc1_ucm_cone_mode                    none
% 0.36/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.36/1.04  --bmc1_ucm_relax_model                  4
% 0.36/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.36/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.36/1.04  --bmc1_ucm_layered_model                none
% 0.36/1.04  --bmc1_ucm_max_lemma_size               10
% 0.36/1.04  
% 0.36/1.04  ------ AIG Options
% 0.36/1.04  
% 0.36/1.04  --aig_mode                              false
% 0.36/1.04  
% 0.36/1.04  ------ Instantiation Options
% 0.36/1.04  
% 0.36/1.04  --instantiation_flag                    true
% 0.36/1.04  --inst_sos_flag                         false
% 0.36/1.04  --inst_sos_phase                        true
% 0.36/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.36/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.36/1.04  --inst_lit_sel_side                     none
% 0.36/1.04  --inst_solver_per_active                1400
% 0.36/1.04  --inst_solver_calls_frac                1.
% 0.36/1.04  --inst_passive_queue_type               priority_queues
% 0.36/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.36/1.04  --inst_passive_queues_freq              [25;2]
% 0.36/1.04  --inst_dismatching                      true
% 0.36/1.04  --inst_eager_unprocessed_to_passive     true
% 0.36/1.04  --inst_prop_sim_given                   true
% 0.36/1.04  --inst_prop_sim_new                     false
% 0.36/1.04  --inst_subs_new                         false
% 0.36/1.04  --inst_eq_res_simp                      false
% 0.36/1.04  --inst_subs_given                       false
% 0.36/1.04  --inst_orphan_elimination               true
% 0.36/1.04  --inst_learning_loop_flag               true
% 0.36/1.04  --inst_learning_start                   3000
% 0.36/1.04  --inst_learning_factor                  2
% 0.36/1.04  --inst_start_prop_sim_after_learn       3
% 0.36/1.04  --inst_sel_renew                        solver
% 0.36/1.04  --inst_lit_activity_flag                true
% 0.36/1.04  --inst_restr_to_given                   false
% 0.36/1.04  --inst_activity_threshold               500
% 0.36/1.04  --inst_out_proof                        true
% 0.36/1.04  
% 0.36/1.04  ------ Resolution Options
% 0.36/1.04  
% 0.36/1.04  --resolution_flag                       false
% 0.36/1.04  --res_lit_sel                           adaptive
% 0.36/1.04  --res_lit_sel_side                      none
% 0.36/1.04  --res_ordering                          kbo
% 0.36/1.04  --res_to_prop_solver                    active
% 0.36/1.04  --res_prop_simpl_new                    false
% 0.36/1.04  --res_prop_simpl_given                  true
% 0.36/1.04  --res_passive_queue_type                priority_queues
% 0.36/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.36/1.04  --res_passive_queues_freq               [15;5]
% 0.36/1.04  --res_forward_subs                      full
% 0.36/1.04  --res_backward_subs                     full
% 0.36/1.04  --res_forward_subs_resolution           true
% 0.36/1.04  --res_backward_subs_resolution          true
% 0.36/1.04  --res_orphan_elimination                true
% 0.36/1.04  --res_time_limit                        2.
% 0.36/1.04  --res_out_proof                         true
% 0.36/1.04  
% 0.36/1.04  ------ Superposition Options
% 0.36/1.04  
% 0.36/1.04  --superposition_flag                    true
% 0.36/1.04  --sup_passive_queue_type                priority_queues
% 0.36/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.36/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.36/1.04  --demod_completeness_check              fast
% 0.36/1.04  --demod_use_ground                      true
% 0.36/1.04  --sup_to_prop_solver                    passive
% 0.36/1.04  --sup_prop_simpl_new                    true
% 0.36/1.04  --sup_prop_simpl_given                  true
% 0.36/1.04  --sup_fun_splitting                     false
% 0.36/1.04  --sup_smt_interval                      50000
% 0.36/1.04  
% 0.36/1.04  ------ Superposition Simplification Setup
% 0.36/1.04  
% 0.36/1.04  --sup_indices_passive                   []
% 0.36/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.36/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.04  --sup_full_bw                           [BwDemod]
% 0.36/1.04  --sup_immed_triv                        [TrivRules]
% 0.36/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.36/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.04  --sup_immed_bw_main                     []
% 0.36/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.36/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.36/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.36/1.04  
% 0.36/1.04  ------ Combination Options
% 0.36/1.04  
% 0.36/1.04  --comb_res_mult                         3
% 0.36/1.04  --comb_sup_mult                         2
% 0.36/1.04  --comb_inst_mult                        10
% 0.36/1.04  
% 0.36/1.04  ------ Debug Options
% 0.36/1.04  
% 0.36/1.04  --dbg_backtrace                         false
% 0.36/1.04  --dbg_dump_prop_clauses                 false
% 0.36/1.04  --dbg_dump_prop_clauses_file            -
% 0.36/1.04  --dbg_out_stat                          false
% 0.36/1.04  
% 0.36/1.04  
% 0.36/1.04  
% 0.36/1.04  
% 0.36/1.04  ------ Proving...
% 0.36/1.04  
% 0.36/1.04  
% 0.36/1.04  % SZS status Theorem for theBenchmark.p
% 0.36/1.04  
% 0.36/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 0.36/1.04  
% 0.36/1.04  fof(f5,axiom,(
% 0.36/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => ~(u1_struct_0(X2) = X1 & v4_tex_2(X2,X0))) & v3_tex_2(X1,X0))))),
% 0.36/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.04  
% 0.36/1.04  fof(f16,plain,(
% 0.36/1.04    ! [X0] : (! [X1] : ((? [X2] : ((u1_struct_0(X2) = X1 & v4_tex_2(X2,X0)) & (m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))) | ~v3_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.36/1.04    inference(ennf_transformation,[],[f5])).
% 0.36/1.04  
% 0.36/1.04  fof(f17,plain,(
% 0.36/1.04    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & v4_tex_2(X2,X0) & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.36/1.04    inference(flattening,[],[f16])).
% 0.36/1.04  
% 0.36/1.04  fof(f24,plain,(
% 0.36/1.04    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & v4_tex_2(X2,X0) & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK0(X0,X1)) = X1 & v4_tex_2(sK0(X0,X1),X0) & m1_pre_topc(sK0(X0,X1),X0) & v1_pre_topc(sK0(X0,X1)) & ~v2_struct_0(sK0(X0,X1))))),
% 0.36/1.04    introduced(choice_axiom,[])).
% 0.36/1.04  
% 0.36/1.04  fof(f25,plain,(
% 0.36/1.04    ! [X0] : (! [X1] : ((u1_struct_0(sK0(X0,X1)) = X1 & v4_tex_2(sK0(X0,X1),X0) & m1_pre_topc(sK0(X0,X1),X0) & v1_pre_topc(sK0(X0,X1)) & ~v2_struct_0(sK0(X0,X1))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.36/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f24])).
% 0.36/1.04  
% 0.36/1.04  fof(f41,plain,(
% 0.36/1.04    ( ! [X0,X1] : (u1_struct_0(sK0(X0,X1)) = X1 | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.36/1.04    inference(cnf_transformation,[],[f25])).
% 0.36/1.04  
% 0.36/1.04  fof(f4,axiom,(
% 0.36/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 0.36/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.04  
% 0.36/1.04  fof(f14,plain,(
% 0.36/1.04    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.36/1.04    inference(ennf_transformation,[],[f4])).
% 0.36/1.04  
% 0.36/1.04  fof(f15,plain,(
% 0.36/1.04    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.36/1.04    inference(flattening,[],[f14])).
% 0.36/1.04  
% 0.36/1.04  fof(f36,plain,(
% 0.36/1.04    ( ! [X0,X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.36/1.04    inference(cnf_transformation,[],[f15])).
% 0.36/1.04  
% 0.36/1.04  fof(f7,conjecture,(
% 0.36/1.04    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) => ? [X2] : (v4_tex_2(X2,X0) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 0.36/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.04  
% 0.36/1.04  fof(f8,negated_conjecture,(
% 0.36/1.04    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) => ? [X2] : (v4_tex_2(X2,X0) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 0.36/1.04    inference(negated_conjecture,[],[f7])).
% 0.36/1.04  
% 0.36/1.04  fof(f20,plain,(
% 0.36/1.04    ? [X0] : (? [X1] : (! [X2] : (~v4_tex_2(X2,X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & (m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.36/1.04    inference(ennf_transformation,[],[f8])).
% 0.36/1.04  
% 0.36/1.04  fof(f21,plain,(
% 0.36/1.04    ? [X0] : (? [X1] : (! [X2] : (~v4_tex_2(X2,X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.36/1.04    inference(flattening,[],[f20])).
% 0.36/1.04  
% 0.36/1.04  fof(f29,plain,(
% 0.36/1.04    ( ! [X0] : (? [X1] : (! [X2] : (~v4_tex_2(X2,X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) => (! [X2] : (~v4_tex_2(X2,X0) | ~m1_pre_topc(sK3,X2) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & m1_pre_topc(sK3,X0) & v1_tdlat_3(sK3) & ~v2_struct_0(sK3))) )),
% 0.36/1.04    introduced(choice_axiom,[])).
% 0.36/1.04  
% 0.36/1.04  fof(f28,plain,(
% 0.36/1.04    ? [X0] : (? [X1] : (! [X2] : (~v4_tex_2(X2,X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (! [X2] : (~v4_tex_2(X2,sK2) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,sK2) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & m1_pre_topc(X1,sK2) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v3_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.36/1.04    introduced(choice_axiom,[])).
% 0.36/1.04  
% 0.36/1.04  fof(f30,plain,(
% 0.36/1.04    (! [X2] : (~v4_tex_2(X2,sK2) | ~m1_pre_topc(sK3,X2) | ~m1_pre_topc(X2,sK2) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & m1_pre_topc(sK3,sK2) & v1_tdlat_3(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v3_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.36/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f29,f28])).
% 0.36/1.04  
% 0.36/1.04  fof(f46,plain,(
% 0.36/1.04    v2_pre_topc(sK2)),
% 0.36/1.04    inference(cnf_transformation,[],[f30])).
% 0.36/1.04  
% 0.36/1.04  fof(f45,plain,(
% 0.36/1.04    ~v2_struct_0(sK2)),
% 0.36/1.04    inference(cnf_transformation,[],[f30])).
% 0.36/1.04  
% 0.36/1.04  fof(f48,plain,(
% 0.36/1.04    l1_pre_topc(sK2)),
% 0.36/1.04    inference(cnf_transformation,[],[f30])).
% 0.36/1.04  
% 0.36/1.04  fof(f3,axiom,(
% 0.36/1.04    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.36/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.04  
% 0.36/1.04  fof(f12,plain,(
% 0.36/1.04    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.36/1.04    inference(ennf_transformation,[],[f3])).
% 0.36/1.04  
% 0.36/1.04  fof(f13,plain,(
% 0.36/1.04    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.36/1.04    inference(flattening,[],[f12])).
% 0.36/1.04  
% 0.36/1.04  fof(f23,plain,(
% 0.36/1.04    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.36/1.04    inference(nnf_transformation,[],[f13])).
% 0.36/1.04  
% 0.36/1.04  fof(f35,plain,(
% 0.36/1.04    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.36/1.04    inference(cnf_transformation,[],[f23])).
% 0.36/1.04  
% 0.36/1.04  fof(f53,plain,(
% 0.36/1.04    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~v1_tdlat_3(X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.36/1.04    inference(equality_resolution,[],[f35])).
% 0.36/1.04  
% 0.36/1.04  fof(f1,axiom,(
% 0.36/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.36/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.04  
% 0.36/1.04  fof(f9,plain,(
% 0.36/1.04    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.36/1.04    inference(ennf_transformation,[],[f1])).
% 0.36/1.04  
% 0.36/1.04  fof(f31,plain,(
% 0.36/1.04    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.36/1.04    inference(cnf_transformation,[],[f9])).
% 0.36/1.04  
% 0.36/1.04  fof(f50,plain,(
% 0.36/1.04    v1_tdlat_3(sK3)),
% 0.36/1.04    inference(cnf_transformation,[],[f30])).
% 0.36/1.04  
% 0.36/1.04  fof(f49,plain,(
% 0.36/1.04    ~v2_struct_0(sK3)),
% 0.36/1.04    inference(cnf_transformation,[],[f30])).
% 0.36/1.04  
% 0.36/1.04  fof(f51,plain,(
% 0.36/1.04    m1_pre_topc(sK3,sK2)),
% 0.36/1.04    inference(cnf_transformation,[],[f30])).
% 0.36/1.04  
% 0.36/1.04  fof(f6,axiom,(
% 0.36/1.04    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(v3_tex_2(X2,X0) & r1_tarski(X1,X2))) & v2_tex_2(X1,X0))))),
% 0.36/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.04  
% 0.36/1.04  fof(f18,plain,(
% 0.36/1.04    ! [X0] : (! [X1] : ((? [X2] : ((v3_tex_2(X2,X0) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.36/1.04    inference(ennf_transformation,[],[f6])).
% 0.36/1.04  
% 0.36/1.04  fof(f19,plain,(
% 0.36/1.04    ! [X0] : (! [X1] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.36/1.04    inference(flattening,[],[f18])).
% 0.36/1.04  
% 0.36/1.04  fof(f26,plain,(
% 0.36/1.04    ! [X1,X0] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_tex_2(sK1(X0,X1),X0) & r1_tarski(X1,sK1(X0,X1)) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.36/1.04    introduced(choice_axiom,[])).
% 0.36/1.04  
% 0.36/1.04  fof(f27,plain,(
% 0.36/1.04    ! [X0] : (! [X1] : ((v3_tex_2(sK1(X0,X1),X0) & r1_tarski(X1,sK1(X0,X1)) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.36/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f26])).
% 0.36/1.04  
% 0.36/1.04  fof(f44,plain,(
% 0.36/1.04    ( ! [X0,X1] : (v3_tex_2(sK1(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.36/1.04    inference(cnf_transformation,[],[f27])).
% 0.36/1.04  
% 0.36/1.04  fof(f47,plain,(
% 0.36/1.04    v3_tdlat_3(sK2)),
% 0.36/1.04    inference(cnf_transformation,[],[f30])).
% 0.36/1.04  
% 0.36/1.04  fof(f42,plain,(
% 0.36/1.04    ( ! [X0,X1] : (m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.36/1.04    inference(cnf_transformation,[],[f27])).
% 0.36/1.04  
% 0.36/1.04  fof(f2,axiom,(
% 0.36/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.36/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.04  
% 0.36/1.04  fof(f10,plain,(
% 0.36/1.04    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.36/1.04    inference(ennf_transformation,[],[f2])).
% 0.36/1.04  
% 0.36/1.04  fof(f11,plain,(
% 0.36/1.04    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.36/1.04    inference(flattening,[],[f10])).
% 0.36/1.04  
% 0.36/1.04  fof(f22,plain,(
% 0.36/1.04    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.36/1.04    inference(nnf_transformation,[],[f11])).
% 0.36/1.04  
% 0.36/1.04  fof(f32,plain,(
% 0.36/1.04    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.36/1.04    inference(cnf_transformation,[],[f22])).
% 0.36/1.04  
% 0.36/1.04  fof(f43,plain,(
% 0.36/1.04    ( ! [X0,X1] : (r1_tarski(X1,sK1(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.36/1.04    inference(cnf_transformation,[],[f27])).
% 0.36/1.04  
% 0.36/1.04  fof(f39,plain,(
% 0.36/1.04    ( ! [X0,X1] : (m1_pre_topc(sK0(X0,X1),X0) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.36/1.04    inference(cnf_transformation,[],[f25])).
% 0.36/1.04  
% 0.36/1.04  fof(f37,plain,(
% 0.36/1.04    ( ! [X0,X1] : (~v2_struct_0(sK0(X0,X1)) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.36/1.04    inference(cnf_transformation,[],[f25])).
% 0.36/1.04  
% 0.36/1.04  fof(f38,plain,(
% 0.36/1.04    ( ! [X0,X1] : (v1_pre_topc(sK0(X0,X1)) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.36/1.04    inference(cnf_transformation,[],[f25])).
% 0.36/1.04  
% 0.36/1.04  fof(f40,plain,(
% 0.36/1.04    ( ! [X0,X1] : (v4_tex_2(sK0(X0,X1),X0) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.36/1.04    inference(cnf_transformation,[],[f25])).
% 0.36/1.04  
% 0.36/1.04  fof(f52,plain,(
% 0.36/1.04    ( ! [X2] : (~v4_tex_2(X2,sK2) | ~m1_pre_topc(sK3,X2) | ~m1_pre_topc(X2,sK2) | ~v1_pre_topc(X2) | v2_struct_0(X2)) )),
% 0.36/1.04    inference(cnf_transformation,[],[f30])).
% 0.36/1.04  
% 0.36/1.04  cnf(c_6,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,X1)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.36/1.04      | v1_xboole_0(X0)
% 0.36/1.04      | v2_struct_0(X1)
% 0.36/1.04      | ~ v2_pre_topc(X1)
% 0.36/1.04      | ~ l1_pre_topc(X1)
% 0.36/1.04      | u1_struct_0(sK0(X1,X0)) = X0 ),
% 0.36/1.04      inference(cnf_transformation,[],[f41]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_5,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,X1)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.36/1.04      | ~ v1_xboole_0(X0)
% 0.36/1.04      | v2_struct_0(X1)
% 0.36/1.04      | ~ v2_pre_topc(X1)
% 0.36/1.04      | ~ l1_pre_topc(X1) ),
% 0.36/1.04      inference(cnf_transformation,[],[f36]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_150,plain,
% 0.36/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.36/1.04      | ~ v3_tex_2(X0,X1)
% 0.36/1.04      | v2_struct_0(X1)
% 0.36/1.04      | ~ v2_pre_topc(X1)
% 0.36/1.04      | ~ l1_pre_topc(X1)
% 0.36/1.04      | u1_struct_0(sK0(X1,X0)) = X0 ),
% 0.36/1.04      inference(global_propositional_subsumption,[status(thm)],[c_6,c_5]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_151,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,X1)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.36/1.04      | v2_struct_0(X1)
% 0.36/1.04      | ~ v2_pre_topc(X1)
% 0.36/1.04      | ~ l1_pre_topc(X1)
% 0.36/1.04      | u1_struct_0(sK0(X1,X0)) = X0 ),
% 0.36/1.04      inference(renaming,[status(thm)],[c_150]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_20,negated_conjecture,
% 0.36/1.04      ( v2_pre_topc(sK2) ),
% 0.36/1.04      inference(cnf_transformation,[],[f46]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_648,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,X1)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.36/1.04      | v2_struct_0(X1)
% 0.36/1.04      | ~ l1_pre_topc(X1)
% 0.36/1.04      | u1_struct_0(sK0(X1,X0)) = X0
% 0.36/1.04      | sK2 != X1 ),
% 0.36/1.04      inference(resolution_lifted,[status(thm)],[c_151,c_20]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_649,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,sK2)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | v2_struct_0(sK2)
% 0.36/1.04      | ~ l1_pre_topc(sK2)
% 0.36/1.04      | u1_struct_0(sK0(sK2,X0)) = X0 ),
% 0.36/1.04      inference(unflattening,[status(thm)],[c_648]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_21,negated_conjecture,
% 0.36/1.04      ( ~ v2_struct_0(sK2) ),
% 0.36/1.04      inference(cnf_transformation,[],[f45]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_18,negated_conjecture,
% 0.36/1.04      ( l1_pre_topc(sK2) ),
% 0.36/1.04      inference(cnf_transformation,[],[f48]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_653,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,sK2)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | u1_struct_0(sK0(sK2,X0)) = X0 ),
% 0.36/1.04      inference(global_propositional_subsumption,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_649,c_21,c_18]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_3,plain,
% 0.36/1.04      ( v2_tex_2(u1_struct_0(X0),X1)
% 0.36/1.04      | ~ m1_pre_topc(X0,X1)
% 0.36/1.04      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 0.36/1.04      | v2_struct_0(X1)
% 0.36/1.04      | v2_struct_0(X0)
% 0.36/1.04      | ~ v1_tdlat_3(X0)
% 0.36/1.04      | ~ l1_pre_topc(X1) ),
% 0.36/1.04      inference(cnf_transformation,[],[f53]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_0,plain,
% 0.36/1.04      ( ~ m1_pre_topc(X0,X1)
% 0.36/1.04      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 0.36/1.04      | ~ l1_pre_topc(X1) ),
% 0.36/1.04      inference(cnf_transformation,[],[f31]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_165,plain,
% 0.36/1.04      ( ~ m1_pre_topc(X0,X1)
% 0.36/1.04      | v2_tex_2(u1_struct_0(X0),X1)
% 0.36/1.04      | v2_struct_0(X1)
% 0.36/1.04      | v2_struct_0(X0)
% 0.36/1.04      | ~ v1_tdlat_3(X0)
% 0.36/1.04      | ~ l1_pre_topc(X1) ),
% 0.36/1.04      inference(global_propositional_subsumption,[status(thm)],[c_3,c_0]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_166,plain,
% 0.36/1.04      ( v2_tex_2(u1_struct_0(X0),X1)
% 0.36/1.04      | ~ m1_pre_topc(X0,X1)
% 0.36/1.04      | v2_struct_0(X1)
% 0.36/1.04      | v2_struct_0(X0)
% 0.36/1.04      | ~ v1_tdlat_3(X0)
% 0.36/1.04      | ~ l1_pre_topc(X1) ),
% 0.36/1.04      inference(renaming,[status(thm)],[c_165]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_796,plain,
% 0.36/1.04      ( v2_tex_2(u1_struct_0(X0),X1)
% 0.36/1.04      | ~ m1_pre_topc(X0,X1)
% 0.36/1.04      | v2_struct_0(X1)
% 0.36/1.04      | v2_struct_0(X0)
% 0.36/1.04      | ~ v1_tdlat_3(X0)
% 0.36/1.04      | sK2 != X1 ),
% 0.36/1.04      inference(resolution_lifted,[status(thm)],[c_166,c_18]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_797,plain,
% 0.36/1.04      ( v2_tex_2(u1_struct_0(X0),sK2)
% 0.36/1.04      | ~ m1_pre_topc(X0,sK2)
% 0.36/1.04      | v2_struct_0(X0)
% 0.36/1.04      | v2_struct_0(sK2)
% 0.36/1.04      | ~ v1_tdlat_3(X0) ),
% 0.36/1.04      inference(unflattening,[status(thm)],[c_796]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_801,plain,
% 0.36/1.04      ( v2_struct_0(X0)
% 0.36/1.04      | ~ m1_pre_topc(X0,sK2)
% 0.36/1.04      | v2_tex_2(u1_struct_0(X0),sK2)
% 0.36/1.04      | ~ v1_tdlat_3(X0) ),
% 0.36/1.04      inference(global_propositional_subsumption,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_797,c_21]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_802,plain,
% 0.36/1.04      ( v2_tex_2(u1_struct_0(X0),sK2)
% 0.36/1.04      | ~ m1_pre_topc(X0,sK2)
% 0.36/1.04      | v2_struct_0(X0)
% 0.36/1.04      | ~ v1_tdlat_3(X0) ),
% 0.36/1.04      inference(renaming,[status(thm)],[c_801]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_16,negated_conjecture,
% 0.36/1.04      ( v1_tdlat_3(sK3) ),
% 0.36/1.04      inference(cnf_transformation,[],[f50]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_868,plain,
% 0.36/1.04      ( v2_tex_2(u1_struct_0(X0),sK2)
% 0.36/1.04      | ~ m1_pre_topc(X0,sK2)
% 0.36/1.04      | v2_struct_0(X0)
% 0.36/1.04      | sK3 != X0 ),
% 0.36/1.04      inference(resolution_lifted,[status(thm)],[c_802,c_16]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_869,plain,
% 0.36/1.04      ( v2_tex_2(u1_struct_0(sK3),sK2)
% 0.36/1.04      | ~ m1_pre_topc(sK3,sK2)
% 0.36/1.04      | v2_struct_0(sK3) ),
% 0.36/1.04      inference(unflattening,[status(thm)],[c_868]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_17,negated_conjecture,
% 0.36/1.04      ( ~ v2_struct_0(sK3) ),
% 0.36/1.04      inference(cnf_transformation,[],[f49]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_15,negated_conjecture,
% 0.36/1.04      ( m1_pre_topc(sK3,sK2) ),
% 0.36/1.04      inference(cnf_transformation,[],[f51]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_472,plain,
% 0.36/1.04      ( v2_tex_2(u1_struct_0(X0),X1)
% 0.36/1.04      | ~ m1_pre_topc(X0,X1)
% 0.36/1.04      | v2_struct_0(X1)
% 0.36/1.04      | v2_struct_0(X0)
% 0.36/1.04      | ~ l1_pre_topc(X1)
% 0.36/1.04      | sK3 != X0 ),
% 0.36/1.04      inference(resolution_lifted,[status(thm)],[c_166,c_16]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_473,plain,
% 0.36/1.04      ( v2_tex_2(u1_struct_0(sK3),X0)
% 0.36/1.04      | ~ m1_pre_topc(sK3,X0)
% 0.36/1.04      | v2_struct_0(X0)
% 0.36/1.04      | v2_struct_0(sK3)
% 0.36/1.04      | ~ l1_pre_topc(X0) ),
% 0.36/1.04      inference(unflattening,[status(thm)],[c_472]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_475,plain,
% 0.36/1.04      ( v2_tex_2(u1_struct_0(sK3),sK2)
% 0.36/1.04      | ~ m1_pre_topc(sK3,sK2)
% 0.36/1.04      | v2_struct_0(sK3)
% 0.36/1.04      | v2_struct_0(sK2)
% 0.36/1.04      | ~ l1_pre_topc(sK2) ),
% 0.36/1.04      inference(instantiation,[status(thm)],[c_473]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_871,plain,
% 0.36/1.04      ( v2_tex_2(u1_struct_0(sK3),sK2) ),
% 0.36/1.04      inference(global_propositional_subsumption,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_869,c_21,c_18,c_17,c_15,c_475]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_11,plain,
% 0.36/1.04      ( v3_tex_2(sK1(X0,X1),X0)
% 0.36/1.04      | ~ v2_tex_2(X1,X0)
% 0.36/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 0.36/1.04      | ~ v3_tdlat_3(X0)
% 0.36/1.04      | v2_struct_0(X0)
% 0.36/1.04      | ~ v2_pre_topc(X0)
% 0.36/1.04      | ~ l1_pre_topc(X0) ),
% 0.36/1.04      inference(cnf_transformation,[],[f44]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_19,negated_conjecture,
% 0.36/1.04      ( v3_tdlat_3(sK2) ),
% 0.36/1.04      inference(cnf_transformation,[],[f47]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_551,plain,
% 0.36/1.04      ( v3_tex_2(sK1(X0,X1),X0)
% 0.36/1.04      | ~ v2_tex_2(X1,X0)
% 0.36/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 0.36/1.04      | v2_struct_0(X0)
% 0.36/1.04      | ~ v2_pre_topc(X0)
% 0.36/1.04      | ~ l1_pre_topc(X0)
% 0.36/1.04      | sK2 != X0 ),
% 0.36/1.04      inference(resolution_lifted,[status(thm)],[c_11,c_19]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_552,plain,
% 0.36/1.04      ( v3_tex_2(sK1(sK2,X0),sK2)
% 0.36/1.04      | ~ v2_tex_2(X0,sK2)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | v2_struct_0(sK2)
% 0.36/1.04      | ~ v2_pre_topc(sK2)
% 0.36/1.04      | ~ l1_pre_topc(sK2) ),
% 0.36/1.04      inference(unflattening,[status(thm)],[c_551]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_556,plain,
% 0.36/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | ~ v2_tex_2(X0,sK2)
% 0.36/1.04      | v3_tex_2(sK1(sK2,X0),sK2) ),
% 0.36/1.04      inference(global_propositional_subsumption,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_552,c_21,c_20,c_18]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_557,plain,
% 0.36/1.04      ( v3_tex_2(sK1(sK2,X0),sK2)
% 0.36/1.04      | ~ v2_tex_2(X0,sK2)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 0.36/1.04      inference(renaming,[status(thm)],[c_556]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_881,plain,
% 0.36/1.04      ( v3_tex_2(sK1(sK2,X0),sK2)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | u1_struct_0(sK3) != X0
% 0.36/1.04      | sK2 != sK2 ),
% 0.36/1.04      inference(resolution_lifted,[status(thm)],[c_871,c_557]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_882,plain,
% 0.36/1.04      ( v3_tex_2(sK1(sK2,u1_struct_0(sK3)),sK2)
% 0.36/1.04      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 0.36/1.04      inference(unflattening,[status(thm)],[c_881]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_963,plain,
% 0.36/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | sK1(sK2,u1_struct_0(sK3)) != X0
% 0.36/1.04      | u1_struct_0(sK0(sK2,X0)) = X0
% 0.36/1.04      | sK2 != sK2 ),
% 0.36/1.04      inference(resolution_lifted,[status(thm)],[c_653,c_882]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_964,plain,
% 0.36/1.04      ( ~ m1_subset_1(sK1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | u1_struct_0(sK0(sK2,sK1(sK2,u1_struct_0(sK3)))) = sK1(sK2,u1_struct_0(sK3)) ),
% 0.36/1.04      inference(unflattening,[status(thm)],[c_963]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_13,plain,
% 0.36/1.04      ( ~ v2_tex_2(X0,X1)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.36/1.04      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 0.36/1.04      | ~ v3_tdlat_3(X1)
% 0.36/1.04      | v2_struct_0(X1)
% 0.36/1.04      | ~ v2_pre_topc(X1)
% 0.36/1.04      | ~ l1_pre_topc(X1) ),
% 0.36/1.04      inference(cnf_transformation,[],[f42]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_509,plain,
% 0.36/1.04      ( ~ v2_tex_2(X0,X1)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.36/1.04      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 0.36/1.04      | v2_struct_0(X1)
% 0.36/1.04      | ~ v2_pre_topc(X1)
% 0.36/1.04      | ~ l1_pre_topc(X1)
% 0.36/1.04      | sK2 != X1 ),
% 0.36/1.04      inference(resolution_lifted,[status(thm)],[c_13,c_19]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_510,plain,
% 0.36/1.04      ( ~ v2_tex_2(X0,sK2)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | v2_struct_0(sK2)
% 0.36/1.04      | ~ v2_pre_topc(sK2)
% 0.36/1.04      | ~ l1_pre_topc(sK2) ),
% 0.36/1.04      inference(unflattening,[status(thm)],[c_509]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_514,plain,
% 0.36/1.04      ( m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | ~ v2_tex_2(X0,sK2) ),
% 0.36/1.04      inference(global_propositional_subsumption,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_510,c_21,c_20,c_18]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_515,plain,
% 0.36/1.04      ( ~ v2_tex_2(X0,sK2)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 0.36/1.04      inference(renaming,[status(thm)],[c_514]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_891,plain,
% 0.36/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | u1_struct_0(sK3) != X0
% 0.36/1.04      | sK2 != sK2 ),
% 0.36/1.04      inference(resolution_lifted,[status(thm)],[c_871,c_515]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_892,plain,
% 0.36/1.04      ( m1_subset_1(sK1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 0.36/1.04      inference(unflattening,[status(thm)],[c_891]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_966,plain,
% 0.36/1.04      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | u1_struct_0(sK0(sK2,sK1(sK2,u1_struct_0(sK3)))) = sK1(sK2,u1_struct_0(sK3)) ),
% 0.36/1.04      inference(global_propositional_subsumption,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_964,c_892]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1044,plain,
% 0.36/1.04      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | u1_struct_0(sK0(sK2,sK1(sK2,u1_struct_0(sK3)))) = sK1(sK2,u1_struct_0(sK3)) ),
% 0.36/1.04      inference(subtyping,[status(esa)],[c_966]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1210,plain,
% 0.36/1.04      ( u1_struct_0(sK0(sK2,sK1(sK2,u1_struct_0(sK3)))) = sK1(sK2,u1_struct_0(sK3))
% 0.36/1.04      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 0.36/1.04      inference(predicate_to_equality,[status(thm)],[c_1044]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_840,plain,
% 0.36/1.04      ( ~ m1_pre_topc(X0,X1)
% 0.36/1.04      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 0.36/1.04      | sK2 != X1 ),
% 0.36/1.04      inference(resolution_lifted,[status(thm)],[c_0,c_18]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_841,plain,
% 0.36/1.04      ( ~ m1_pre_topc(X0,sK2)
% 0.36/1.04      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 0.36/1.04      inference(unflattening,[status(thm)],[c_840]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1048,plain,
% 0.36/1.04      ( ~ m1_pre_topc(X0_47,sK2)
% 0.36/1.04      | m1_subset_1(u1_struct_0(X0_47),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 0.36/1.04      inference(subtyping,[status(esa)],[c_841]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1260,plain,
% 0.36/1.04      ( ~ m1_pre_topc(sK3,sK2)
% 0.36/1.04      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 0.36/1.04      inference(instantiation,[status(thm)],[c_1048]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1347,plain,
% 0.36/1.04      ( u1_struct_0(sK0(sK2,sK1(sK2,u1_struct_0(sK3)))) = sK1(sK2,u1_struct_0(sK3)) ),
% 0.36/1.04      inference(global_propositional_subsumption,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_1210,c_15,c_1044,c_1260]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_2,plain,
% 0.36/1.04      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 0.36/1.04      | ~ m1_pre_topc(X0,X2)
% 0.36/1.04      | ~ m1_pre_topc(X1,X2)
% 0.36/1.04      | m1_pre_topc(X0,X1)
% 0.36/1.04      | ~ v2_pre_topc(X2)
% 0.36/1.04      | ~ l1_pre_topc(X2) ),
% 0.36/1.04      inference(cnf_transformation,[],[f32]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_12,plain,
% 0.36/1.04      ( ~ v2_tex_2(X0,X1)
% 0.36/1.04      | r1_tarski(X0,sK1(X1,X0))
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.36/1.04      | ~ v3_tdlat_3(X1)
% 0.36/1.04      | v2_struct_0(X1)
% 0.36/1.04      | ~ v2_pre_topc(X1)
% 0.36/1.04      | ~ l1_pre_topc(X1) ),
% 0.36/1.04      inference(cnf_transformation,[],[f43]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_530,plain,
% 0.36/1.04      ( ~ v2_tex_2(X0,X1)
% 0.36/1.04      | r1_tarski(X0,sK1(X1,X0))
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.36/1.04      | v2_struct_0(X1)
% 0.36/1.04      | ~ v2_pre_topc(X1)
% 0.36/1.04      | ~ l1_pre_topc(X1)
% 0.36/1.04      | sK2 != X1 ),
% 0.36/1.04      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_531,plain,
% 0.36/1.04      ( ~ v2_tex_2(X0,sK2)
% 0.36/1.04      | r1_tarski(X0,sK1(sK2,X0))
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | v2_struct_0(sK2)
% 0.36/1.04      | ~ v2_pre_topc(sK2)
% 0.36/1.04      | ~ l1_pre_topc(sK2) ),
% 0.36/1.04      inference(unflattening,[status(thm)],[c_530]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_535,plain,
% 0.36/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | r1_tarski(X0,sK1(sK2,X0))
% 0.36/1.04      | ~ v2_tex_2(X0,sK2) ),
% 0.36/1.04      inference(global_propositional_subsumption,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_531,c_21,c_20,c_18]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_536,plain,
% 0.36/1.04      ( ~ v2_tex_2(X0,sK2)
% 0.36/1.04      | r1_tarski(X0,sK1(sK2,X0))
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 0.36/1.04      inference(renaming,[status(thm)],[c_535]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_585,plain,
% 0.36/1.04      ( ~ v2_tex_2(X0,sK2)
% 0.36/1.04      | ~ m1_pre_topc(X1,X2)
% 0.36/1.04      | ~ m1_pre_topc(X3,X2)
% 0.36/1.04      | m1_pre_topc(X1,X3)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | ~ v2_pre_topc(X2)
% 0.36/1.04      | ~ l1_pre_topc(X2)
% 0.36/1.04      | sK1(sK2,X0) != u1_struct_0(X3)
% 0.36/1.04      | u1_struct_0(X1) != X0 ),
% 0.36/1.04      inference(resolution_lifted,[status(thm)],[c_2,c_536]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_586,plain,
% 0.36/1.04      ( ~ v2_tex_2(u1_struct_0(X0),sK2)
% 0.36/1.04      | ~ m1_pre_topc(X0,X1)
% 0.36/1.04      | ~ m1_pre_topc(X2,X1)
% 0.36/1.04      | m1_pre_topc(X0,X2)
% 0.36/1.04      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | ~ v2_pre_topc(X1)
% 0.36/1.04      | ~ l1_pre_topc(X1)
% 0.36/1.04      | sK1(sK2,u1_struct_0(X0)) != u1_struct_0(X2) ),
% 0.36/1.04      inference(unflattening,[status(thm)],[c_585]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_622,plain,
% 0.36/1.04      ( ~ v2_tex_2(u1_struct_0(X0),sK2)
% 0.36/1.04      | ~ m1_pre_topc(X0,X1)
% 0.36/1.04      | ~ m1_pre_topc(X2,X1)
% 0.36/1.04      | m1_pre_topc(X0,X2)
% 0.36/1.04      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | ~ l1_pre_topc(X1)
% 0.36/1.04      | sK1(sK2,u1_struct_0(X0)) != u1_struct_0(X2)
% 0.36/1.04      | sK2 != X1 ),
% 0.36/1.04      inference(resolution_lifted,[status(thm)],[c_586,c_20]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_623,plain,
% 0.36/1.04      ( ~ v2_tex_2(u1_struct_0(X0),sK2)
% 0.36/1.04      | m1_pre_topc(X0,X1)
% 0.36/1.04      | ~ m1_pre_topc(X1,sK2)
% 0.36/1.04      | ~ m1_pre_topc(X0,sK2)
% 0.36/1.04      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | ~ l1_pre_topc(sK2)
% 0.36/1.04      | sK1(sK2,u1_struct_0(X0)) != u1_struct_0(X1) ),
% 0.36/1.04      inference(unflattening,[status(thm)],[c_622]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_625,plain,
% 0.36/1.04      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | ~ m1_pre_topc(X0,sK2)
% 0.36/1.04      | ~ m1_pre_topc(X1,sK2)
% 0.36/1.04      | m1_pre_topc(X0,X1)
% 0.36/1.04      | ~ v2_tex_2(u1_struct_0(X0),sK2)
% 0.36/1.04      | sK1(sK2,u1_struct_0(X0)) != u1_struct_0(X1) ),
% 0.36/1.04      inference(global_propositional_subsumption,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_623,c_18]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_626,plain,
% 0.36/1.04      ( ~ v2_tex_2(u1_struct_0(X0),sK2)
% 0.36/1.04      | m1_pre_topc(X0,X1)
% 0.36/1.04      | ~ m1_pre_topc(X0,sK2)
% 0.36/1.04      | ~ m1_pre_topc(X1,sK2)
% 0.36/1.04      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | sK1(sK2,u1_struct_0(X0)) != u1_struct_0(X1) ),
% 0.36/1.04      inference(renaming,[status(thm)],[c_625]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_864,plain,
% 0.36/1.04      ( ~ v2_tex_2(u1_struct_0(X0),sK2)
% 0.36/1.04      | m1_pre_topc(X0,X1)
% 0.36/1.04      | ~ m1_pre_topc(X0,sK2)
% 0.36/1.04      | ~ m1_pre_topc(X1,sK2)
% 0.36/1.04      | sK1(sK2,u1_struct_0(X0)) != u1_struct_0(X1) ),
% 0.36/1.04      inference(backward_subsumption_resolution,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_841,c_626]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_901,plain,
% 0.36/1.04      ( m1_pre_topc(X0,X1)
% 0.36/1.04      | ~ m1_pre_topc(X0,sK2)
% 0.36/1.04      | ~ m1_pre_topc(X1,sK2)
% 0.36/1.04      | sK1(sK2,u1_struct_0(X0)) != u1_struct_0(X1)
% 0.36/1.04      | u1_struct_0(X0) != u1_struct_0(sK3)
% 0.36/1.04      | sK2 != sK2 ),
% 0.36/1.04      inference(resolution_lifted,[status(thm)],[c_871,c_864]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_996,plain,
% 0.36/1.04      ( m1_pre_topc(X0,X1)
% 0.36/1.04      | ~ m1_pre_topc(X0,sK2)
% 0.36/1.04      | ~ m1_pre_topc(X1,sK2)
% 0.36/1.04      | sK1(sK2,u1_struct_0(X0)) != u1_struct_0(X1)
% 0.36/1.04      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 0.36/1.04      inference(equality_resolution_simp,[status(thm)],[c_901]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1043,plain,
% 0.36/1.04      ( m1_pre_topc(X0_47,X1_47)
% 0.36/1.04      | ~ m1_pre_topc(X0_47,sK2)
% 0.36/1.04      | ~ m1_pre_topc(X1_47,sK2)
% 0.36/1.04      | sK1(sK2,u1_struct_0(X0_47)) != u1_struct_0(X1_47)
% 0.36/1.04      | u1_struct_0(X0_47) != u1_struct_0(sK3) ),
% 0.36/1.04      inference(subtyping,[status(esa)],[c_996]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1211,plain,
% 0.36/1.04      ( sK1(sK2,u1_struct_0(X0_47)) != u1_struct_0(X1_47)
% 0.36/1.04      | u1_struct_0(X0_47) != u1_struct_0(sK3)
% 0.36/1.04      | m1_pre_topc(X0_47,X1_47) = iProver_top
% 0.36/1.04      | m1_pre_topc(X0_47,sK2) != iProver_top
% 0.36/1.04      | m1_pre_topc(X1_47,sK2) != iProver_top ),
% 0.36/1.04      inference(predicate_to_equality,[status(thm)],[c_1043]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1416,plain,
% 0.36/1.04      ( sK1(sK2,u1_struct_0(X0_47)) != sK1(sK2,u1_struct_0(sK3))
% 0.36/1.04      | u1_struct_0(X0_47) != u1_struct_0(sK3)
% 0.36/1.04      | m1_pre_topc(X0_47,sK0(sK2,sK1(sK2,u1_struct_0(sK3)))) = iProver_top
% 0.36/1.04      | m1_pre_topc(X0_47,sK2) != iProver_top
% 0.36/1.04      | m1_pre_topc(sK0(sK2,sK1(sK2,u1_struct_0(sK3))),sK2) != iProver_top ),
% 0.36/1.04      inference(superposition,[status(thm)],[c_1347,c_1211]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_28,plain,
% 0.36/1.04      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 0.36/1.04      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_8,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,X1)
% 0.36/1.04      | m1_pre_topc(sK0(X1,X0),X1)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.36/1.04      | v1_xboole_0(X0)
% 0.36/1.04      | v2_struct_0(X1)
% 0.36/1.04      | ~ v2_pre_topc(X1)
% 0.36/1.04      | ~ l1_pre_topc(X1) ),
% 0.36/1.04      inference(cnf_transformation,[],[f39]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_142,plain,
% 0.36/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.36/1.04      | m1_pre_topc(sK0(X1,X0),X1)
% 0.36/1.04      | ~ v3_tex_2(X0,X1)
% 0.36/1.04      | v2_struct_0(X1)
% 0.36/1.04      | ~ v2_pre_topc(X1)
% 0.36/1.04      | ~ l1_pre_topc(X1) ),
% 0.36/1.04      inference(global_propositional_subsumption,[status(thm)],[c_8,c_5]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_143,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,X1)
% 0.36/1.04      | m1_pre_topc(sK0(X1,X0),X1)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.36/1.04      | v2_struct_0(X1)
% 0.36/1.04      | ~ v2_pre_topc(X1)
% 0.36/1.04      | ~ l1_pre_topc(X1) ),
% 0.36/1.04      inference(renaming,[status(thm)],[c_142]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_669,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,X1)
% 0.36/1.04      | m1_pre_topc(sK0(X1,X0),X1)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.36/1.04      | v2_struct_0(X1)
% 0.36/1.04      | ~ l1_pre_topc(X1)
% 0.36/1.04      | sK2 != X1 ),
% 0.36/1.04      inference(resolution_lifted,[status(thm)],[c_143,c_20]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_670,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,sK2)
% 0.36/1.04      | m1_pre_topc(sK0(sK2,X0),sK2)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | v2_struct_0(sK2)
% 0.36/1.04      | ~ l1_pre_topc(sK2) ),
% 0.36/1.04      inference(unflattening,[status(thm)],[c_669]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_674,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,sK2)
% 0.36/1.04      | m1_pre_topc(sK0(sK2,X0),sK2)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 0.36/1.04      inference(global_propositional_subsumption,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_670,c_21,c_18]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_949,plain,
% 0.36/1.04      ( m1_pre_topc(sK0(sK2,X0),sK2)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | sK1(sK2,u1_struct_0(sK3)) != X0
% 0.36/1.04      | sK2 != sK2 ),
% 0.36/1.04      inference(resolution_lifted,[status(thm)],[c_674,c_882]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_950,plain,
% 0.36/1.04      ( m1_pre_topc(sK0(sK2,sK1(sK2,u1_struct_0(sK3))),sK2)
% 0.36/1.04      | ~ m1_subset_1(sK1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 0.36/1.04      inference(unflattening,[status(thm)],[c_949]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_952,plain,
% 0.36/1.04      ( m1_pre_topc(sK0(sK2,sK1(sK2,u1_struct_0(sK3))),sK2)
% 0.36/1.04      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 0.36/1.04      inference(global_propositional_subsumption,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_950,c_892]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_954,plain,
% 0.36/1.04      ( m1_pre_topc(sK0(sK2,sK1(sK2,u1_struct_0(sK3))),sK2) = iProver_top
% 0.36/1.04      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 0.36/1.04      inference(predicate_to_equality,[status(thm)],[c_952]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1261,plain,
% 0.36/1.04      ( m1_pre_topc(sK3,sK2) != iProver_top
% 0.36/1.04      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 0.36/1.04      inference(predicate_to_equality,[status(thm)],[c_1260]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1443,plain,
% 0.36/1.04      ( m1_pre_topc(X0_47,sK2) != iProver_top
% 0.36/1.04      | m1_pre_topc(X0_47,sK0(sK2,sK1(sK2,u1_struct_0(sK3)))) = iProver_top
% 0.36/1.04      | u1_struct_0(X0_47) != u1_struct_0(sK3)
% 0.36/1.04      | sK1(sK2,u1_struct_0(X0_47)) != sK1(sK2,u1_struct_0(sK3)) ),
% 0.36/1.04      inference(global_propositional_subsumption,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_1416,c_28,c_954,c_1261]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1444,plain,
% 0.36/1.04      ( sK1(sK2,u1_struct_0(X0_47)) != sK1(sK2,u1_struct_0(sK3))
% 0.36/1.04      | u1_struct_0(X0_47) != u1_struct_0(sK3)
% 0.36/1.04      | m1_pre_topc(X0_47,sK0(sK2,sK1(sK2,u1_struct_0(sK3)))) = iProver_top
% 0.36/1.04      | m1_pre_topc(X0_47,sK2) != iProver_top ),
% 0.36/1.04      inference(renaming,[status(thm)],[c_1443]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1454,plain,
% 0.36/1.04      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 0.36/1.04      | m1_pre_topc(sK3,sK0(sK2,sK1(sK2,u1_struct_0(sK3)))) = iProver_top
% 0.36/1.04      | m1_pre_topc(sK3,sK2) != iProver_top ),
% 0.36/1.04      inference(equality_resolution,[status(thm)],[c_1444]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1455,plain,
% 0.36/1.04      ( m1_pre_topc(sK3,sK0(sK2,sK1(sK2,u1_struct_0(sK3)))) = iProver_top
% 0.36/1.04      | m1_pre_topc(sK3,sK2) != iProver_top ),
% 0.36/1.04      inference(equality_resolution_simp,[status(thm)],[c_1454]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_732,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,X1)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.36/1.04      | ~ v1_xboole_0(X0)
% 0.36/1.04      | v2_struct_0(X1)
% 0.36/1.04      | ~ l1_pre_topc(X1)
% 0.36/1.04      | sK2 != X1 ),
% 0.36/1.04      inference(resolution_lifted,[status(thm)],[c_5,c_20]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_733,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,sK2)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | ~ v1_xboole_0(X0)
% 0.36/1.04      | v2_struct_0(sK2)
% 0.36/1.04      | ~ l1_pre_topc(sK2) ),
% 0.36/1.04      inference(unflattening,[status(thm)],[c_732]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_737,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,sK2)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | ~ v1_xboole_0(X0) ),
% 0.36/1.04      inference(global_propositional_subsumption,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_733,c_21,c_18]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_10,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,X1)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.36/1.04      | v1_xboole_0(X0)
% 0.36/1.04      | v2_struct_0(X1)
% 0.36/1.04      | ~ v2_struct_0(sK0(X1,X0))
% 0.36/1.04      | ~ v2_pre_topc(X1)
% 0.36/1.04      | ~ l1_pre_topc(X1) ),
% 0.36/1.04      inference(cnf_transformation,[],[f37]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_128,plain,
% 0.36/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.36/1.04      | ~ v3_tex_2(X0,X1)
% 0.36/1.04      | v2_struct_0(X1)
% 0.36/1.04      | ~ v2_struct_0(sK0(X1,X0))
% 0.36/1.04      | ~ v2_pre_topc(X1)
% 0.36/1.04      | ~ l1_pre_topc(X1) ),
% 0.36/1.04      inference(global_propositional_subsumption,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_10,c_5]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_129,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,X1)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.36/1.04      | v2_struct_0(X1)
% 0.36/1.04      | ~ v2_struct_0(sK0(X1,X0))
% 0.36/1.04      | ~ v2_pre_topc(X1)
% 0.36/1.04      | ~ l1_pre_topc(X1) ),
% 0.36/1.04      inference(renaming,[status(thm)],[c_128]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_711,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,X1)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.36/1.04      | v2_struct_0(X1)
% 0.36/1.04      | ~ v2_struct_0(sK0(X1,X0))
% 0.36/1.04      | ~ l1_pre_topc(X1)
% 0.36/1.04      | sK2 != X1 ),
% 0.36/1.04      inference(resolution_lifted,[status(thm)],[c_129,c_20]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_712,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,sK2)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | ~ v2_struct_0(sK0(sK2,X0))
% 0.36/1.04      | v2_struct_0(sK2)
% 0.36/1.04      | ~ l1_pre_topc(sK2) ),
% 0.36/1.04      inference(unflattening,[status(thm)],[c_711]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_716,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,sK2)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | ~ v2_struct_0(sK0(sK2,X0)) ),
% 0.36/1.04      inference(global_propositional_subsumption,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_712,c_21,c_18]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_9,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,X1)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.36/1.04      | v1_pre_topc(sK0(X1,X0))
% 0.36/1.04      | v1_xboole_0(X0)
% 0.36/1.04      | v2_struct_0(X1)
% 0.36/1.04      | ~ v2_pre_topc(X1)
% 0.36/1.04      | ~ l1_pre_topc(X1) ),
% 0.36/1.04      inference(cnf_transformation,[],[f38]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_135,plain,
% 0.36/1.04      ( v1_pre_topc(sK0(X1,X0))
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.36/1.04      | ~ v3_tex_2(X0,X1)
% 0.36/1.04      | v2_struct_0(X1)
% 0.36/1.04      | ~ v2_pre_topc(X1)
% 0.36/1.04      | ~ l1_pre_topc(X1) ),
% 0.36/1.04      inference(global_propositional_subsumption,[status(thm)],[c_9,c_5]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_136,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,X1)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.36/1.04      | v1_pre_topc(sK0(X1,X0))
% 0.36/1.04      | v2_struct_0(X1)
% 0.36/1.04      | ~ v2_pre_topc(X1)
% 0.36/1.04      | ~ l1_pre_topc(X1) ),
% 0.36/1.04      inference(renaming,[status(thm)],[c_135]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_690,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,X1)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.36/1.04      | v1_pre_topc(sK0(X1,X0))
% 0.36/1.04      | v2_struct_0(X1)
% 0.36/1.04      | ~ l1_pre_topc(X1)
% 0.36/1.04      | sK2 != X1 ),
% 0.36/1.04      inference(resolution_lifted,[status(thm)],[c_136,c_20]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_691,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,sK2)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | v1_pre_topc(sK0(sK2,X0))
% 0.36/1.04      | v2_struct_0(sK2)
% 0.36/1.04      | ~ l1_pre_topc(sK2) ),
% 0.36/1.04      inference(unflattening,[status(thm)],[c_690]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_695,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,sK2)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | v1_pre_topc(sK0(sK2,X0)) ),
% 0.36/1.04      inference(global_propositional_subsumption,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_691,c_21,c_18]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_7,plain,
% 0.36/1.04      ( v4_tex_2(sK0(X0,X1),X0)
% 0.36/1.04      | ~ v3_tex_2(X1,X0)
% 0.36/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 0.36/1.04      | v1_xboole_0(X1)
% 0.36/1.04      | v2_struct_0(X0)
% 0.36/1.04      | ~ v2_pre_topc(X0)
% 0.36/1.04      | ~ l1_pre_topc(X0) ),
% 0.36/1.04      inference(cnf_transformation,[],[f40]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_14,negated_conjecture,
% 0.36/1.04      ( ~ v4_tex_2(X0,sK2)
% 0.36/1.04      | ~ m1_pre_topc(X0,sK2)
% 0.36/1.04      | ~ m1_pre_topc(sK3,X0)
% 0.36/1.04      | ~ v1_pre_topc(X0)
% 0.36/1.04      | v2_struct_0(X0) ),
% 0.36/1.04      inference(cnf_transformation,[],[f52]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_322,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,X1)
% 0.36/1.04      | ~ m1_pre_topc(X2,sK2)
% 0.36/1.04      | ~ m1_pre_topc(sK3,X2)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.36/1.04      | ~ v1_pre_topc(X2)
% 0.36/1.04      | v1_xboole_0(X0)
% 0.36/1.04      | v2_struct_0(X1)
% 0.36/1.04      | v2_struct_0(X2)
% 0.36/1.04      | ~ v2_pre_topc(X1)
% 0.36/1.04      | ~ l1_pre_topc(X1)
% 0.36/1.04      | sK0(X1,X0) != X2
% 0.36/1.04      | sK2 != X1 ),
% 0.36/1.04      inference(resolution_lifted,[status(thm)],[c_7,c_14]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_323,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,sK2)
% 0.36/1.04      | ~ m1_pre_topc(sK0(sK2,X0),sK2)
% 0.36/1.04      | ~ m1_pre_topc(sK3,sK0(sK2,X0))
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | ~ v1_pre_topc(sK0(sK2,X0))
% 0.36/1.04      | v1_xboole_0(X0)
% 0.36/1.04      | v2_struct_0(sK0(sK2,X0))
% 0.36/1.04      | v2_struct_0(sK2)
% 0.36/1.04      | ~ v2_pre_topc(sK2)
% 0.36/1.04      | ~ l1_pre_topc(sK2) ),
% 0.36/1.04      inference(unflattening,[status(thm)],[c_322]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_327,plain,
% 0.36/1.04      ( v2_struct_0(sK0(sK2,X0))
% 0.36/1.04      | v1_xboole_0(X0)
% 0.36/1.04      | ~ v1_pre_topc(sK0(sK2,X0))
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | ~ m1_pre_topc(sK3,sK0(sK2,X0))
% 0.36/1.04      | ~ m1_pre_topc(sK0(sK2,X0),sK2)
% 0.36/1.04      | ~ v3_tex_2(X0,sK2) ),
% 0.36/1.04      inference(global_propositional_subsumption,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_323,c_21,c_20,c_18]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_328,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,sK2)
% 0.36/1.04      | ~ m1_pre_topc(sK0(sK2,X0),sK2)
% 0.36/1.04      | ~ m1_pre_topc(sK3,sK0(sK2,X0))
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | ~ v1_pre_topc(sK0(sK2,X0))
% 0.36/1.04      | v1_xboole_0(X0)
% 0.36/1.04      | v2_struct_0(sK0(sK2,X0)) ),
% 0.36/1.04      inference(renaming,[status(thm)],[c_327]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_766,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,sK2)
% 0.36/1.04      | ~ m1_pre_topc(sK3,sK0(sK2,X0))
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | ~ v1_pre_topc(sK0(sK2,X0))
% 0.36/1.04      | v1_xboole_0(X0)
% 0.36/1.04      | v2_struct_0(sK0(sK2,X0)) ),
% 0.36/1.04      inference(backward_subsumption_resolution,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_674,c_328]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_775,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,sK2)
% 0.36/1.04      | ~ m1_pre_topc(sK3,sK0(sK2,X0))
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | v1_xboole_0(X0)
% 0.36/1.04      | v2_struct_0(sK0(sK2,X0)) ),
% 0.36/1.04      inference(backward_subsumption_resolution,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_695,c_766]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_783,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,sK2)
% 0.36/1.04      | ~ m1_pre_topc(sK3,sK0(sK2,X0))
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | v1_xboole_0(X0) ),
% 0.36/1.04      inference(backward_subsumption_resolution,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_716,c_775]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_791,plain,
% 0.36/1.04      ( ~ v3_tex_2(X0,sK2)
% 0.36/1.04      | ~ m1_pre_topc(sK3,sK0(sK2,X0))
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 0.36/1.04      inference(backward_subsumption_resolution,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_737,c_783]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_935,plain,
% 0.36/1.04      ( ~ m1_pre_topc(sK3,sK0(sK2,X0))
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | sK1(sK2,u1_struct_0(sK3)) != X0
% 0.36/1.04      | sK2 != sK2 ),
% 0.36/1.04      inference(resolution_lifted,[status(thm)],[c_791,c_882]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_936,plain,
% 0.36/1.04      ( ~ m1_pre_topc(sK3,sK0(sK2,sK1(sK2,u1_struct_0(sK3))))
% 0.36/1.04      | ~ m1_subset_1(sK1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.36/1.04      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 0.36/1.04      inference(unflattening,[status(thm)],[c_935]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_938,plain,
% 0.36/1.04      ( ~ m1_pre_topc(sK3,sK0(sK2,sK1(sK2,u1_struct_0(sK3))))
% 0.36/1.04      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 0.36/1.04      inference(global_propositional_subsumption,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_936,c_892]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_940,plain,
% 0.36/1.04      ( m1_pre_topc(sK3,sK0(sK2,sK1(sK2,u1_struct_0(sK3)))) != iProver_top
% 0.36/1.04      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 0.36/1.04      inference(predicate_to_equality,[status(thm)],[c_938]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(contradiction,plain,
% 0.36/1.04      ( $false ),
% 0.36/1.04      inference(minisat,[status(thm)],[c_1455,c_1261,c_940,c_28]) ).
% 0.36/1.04  
% 0.36/1.04  
% 0.36/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 0.36/1.04  
% 0.36/1.04  ------                               Statistics
% 0.36/1.04  
% 0.36/1.04  ------ General
% 0.36/1.04  
% 0.36/1.04  abstr_ref_over_cycles:                  0
% 0.36/1.04  abstr_ref_under_cycles:                 0
% 0.36/1.04  gc_basic_clause_elim:                   0
% 0.36/1.04  forced_gc_time:                         0
% 0.36/1.04  parsing_time:                           0.013
% 0.36/1.04  unif_index_cands_time:                  0.
% 0.36/1.04  unif_index_add_time:                    0.
% 0.36/1.04  orderings_time:                         0.
% 0.36/1.04  out_proof_time:                         0.017
% 0.36/1.04  total_time:                             0.092
% 0.36/1.04  num_of_symbols:                         50
% 0.36/1.04  num_of_terms:                           1099
% 0.36/1.04  
% 0.36/1.04  ------ Preprocessing
% 0.36/1.04  
% 0.36/1.04  num_of_splits:                          0
% 0.36/1.04  num_of_split_atoms:                     0
% 0.36/1.04  num_of_reused_defs:                     0
% 0.36/1.04  num_eq_ax_congr_red:                    7
% 0.36/1.04  num_of_sem_filtered_clauses:            1
% 0.36/1.04  num_of_subtypes:                        3
% 0.36/1.04  monotx_restored_types:                  0
% 0.36/1.04  sat_num_of_epr_types:                   0
% 0.36/1.04  sat_num_of_non_cyclic_types:            0
% 0.36/1.04  sat_guarded_non_collapsed_types:        0
% 0.36/1.04  num_pure_diseq_elim:                    0
% 0.36/1.04  simp_replaced_by:                       0
% 0.36/1.04  res_preprocessed:                       64
% 0.36/1.04  prep_upred:                             0
% 0.36/1.04  prep_unflattend:                        23
% 0.36/1.04  smt_new_axioms:                         0
% 0.36/1.04  pred_elim_cands:                        2
% 0.36/1.04  pred_elim:                              11
% 0.36/1.04  pred_elim_cl:                           15
% 0.36/1.04  pred_elim_cycles:                       17
% 0.36/1.04  merged_defs:                            0
% 0.36/1.04  merged_defs_ncl:                        0
% 0.36/1.04  bin_hyper_res:                          0
% 0.36/1.04  prep_cycles:                            4
% 0.36/1.04  pred_elim_time:                         0.016
% 0.36/1.04  splitting_time:                         0.
% 0.36/1.04  sem_filter_time:                        0.
% 0.36/1.04  monotx_time:                            0.
% 0.36/1.04  subtype_inf_time:                       0.
% 0.36/1.04  
% 0.36/1.04  ------ Problem properties
% 0.36/1.04  
% 0.36/1.04  clauses:                                7
% 0.36/1.04  conjectures:                            1
% 0.36/1.04  epr:                                    1
% 0.36/1.04  horn:                                   7
% 0.36/1.04  ground:                                 5
% 0.36/1.04  unary:                                  1
% 0.36/1.04  binary:                                 5
% 0.36/1.04  lits:                                   16
% 0.36/1.04  lits_eq:                                3
% 0.36/1.04  fd_pure:                                0
% 0.36/1.04  fd_pseudo:                              0
% 0.36/1.04  fd_cond:                                0
% 0.36/1.04  fd_pseudo_cond:                         0
% 0.36/1.04  ac_symbols:                             0
% 0.36/1.04  
% 0.36/1.04  ------ Propositional Solver
% 0.36/1.04  
% 0.36/1.04  prop_solver_calls:                      25
% 0.36/1.04  prop_fast_solver_calls:                 663
% 0.36/1.04  smt_solver_calls:                       0
% 0.36/1.04  smt_fast_solver_calls:                  0
% 0.36/1.04  prop_num_of_clauses:                    383
% 0.36/1.04  prop_preprocess_simplified:             1728
% 0.36/1.04  prop_fo_subsumed:                       42
% 0.36/1.04  prop_solver_time:                       0.
% 0.36/1.04  smt_solver_time:                        0.
% 0.36/1.04  smt_fast_solver_time:                   0.
% 0.36/1.04  prop_fast_solver_time:                  0.
% 0.36/1.04  prop_unsat_core_time:                   0.
% 0.36/1.04  
% 0.36/1.04  ------ QBF
% 0.36/1.04  
% 0.36/1.04  qbf_q_res:                              0
% 0.36/1.04  qbf_num_tautologies:                    0
% 0.36/1.04  qbf_prep_cycles:                        0
% 0.36/1.04  
% 0.36/1.04  ------ BMC1
% 0.36/1.04  
% 0.36/1.04  bmc1_current_bound:                     -1
% 0.36/1.04  bmc1_last_solved_bound:                 -1
% 0.36/1.04  bmc1_unsat_core_size:                   -1
% 0.36/1.04  bmc1_unsat_core_parents_size:           -1
% 0.36/1.04  bmc1_merge_next_fun:                    0
% 0.36/1.04  bmc1_unsat_core_clauses_time:           0.
% 0.36/1.04  
% 0.36/1.04  ------ Instantiation
% 0.36/1.04  
% 0.36/1.04  inst_num_of_clauses:                    50
% 0.36/1.04  inst_num_in_passive:                    2
% 0.36/1.04  inst_num_in_active:                     34
% 0.36/1.04  inst_num_in_unprocessed:                14
% 0.36/1.04  inst_num_of_loops:                      40
% 0.36/1.04  inst_num_of_learning_restarts:          0
% 0.36/1.04  inst_num_moves_active_passive:          4
% 0.36/1.04  inst_lit_activity:                      0
% 0.36/1.04  inst_lit_activity_moves:                0
% 0.36/1.04  inst_num_tautologies:                   0
% 0.36/1.04  inst_num_prop_implied:                  0
% 0.36/1.04  inst_num_existing_simplified:           0
% 0.36/1.04  inst_num_eq_res_simplified:             0
% 0.36/1.04  inst_num_child_elim:                    0
% 0.36/1.04  inst_num_of_dismatching_blockings:      0
% 0.36/1.04  inst_num_of_non_proper_insts:           19
% 0.36/1.04  inst_num_of_duplicates:                 0
% 0.36/1.04  inst_inst_num_from_inst_to_res:         0
% 0.36/1.04  inst_dismatching_checking_time:         0.
% 0.36/1.04  
% 0.36/1.04  ------ Resolution
% 0.36/1.04  
% 0.36/1.04  res_num_of_clauses:                     0
% 0.36/1.04  res_num_in_passive:                     0
% 0.36/1.04  res_num_in_active:                      0
% 0.36/1.04  res_num_of_loops:                       68
% 0.36/1.04  res_forward_subset_subsumed:            4
% 0.36/1.04  res_backward_subset_subsumed:           0
% 0.36/1.04  res_forward_subsumed:                   0
% 0.36/1.04  res_backward_subsumed:                  0
% 0.36/1.04  res_forward_subsumption_resolution:     1
% 0.36/1.04  res_backward_subsumption_resolution:    5
% 0.36/1.04  res_clause_to_clause_subsumption:       56
% 0.36/1.04  res_orphan_elimination:                 0
% 0.36/1.04  res_tautology_del:                      6
% 0.36/1.04  res_num_eq_res_simplified:              1
% 0.36/1.04  res_num_sel_changes:                    0
% 0.36/1.04  res_moves_from_active_to_pass:          0
% 0.36/1.04  
% 0.36/1.04  ------ Superposition
% 0.36/1.04  
% 0.36/1.04  sup_time_total:                         0.
% 0.36/1.04  sup_time_generating:                    0.
% 0.36/1.04  sup_time_sim_full:                      0.
% 0.36/1.04  sup_time_sim_immed:                     0.
% 0.36/1.04  
% 0.36/1.04  sup_num_of_clauses:                     10
% 0.36/1.04  sup_num_in_active:                      8
% 0.36/1.04  sup_num_in_passive:                     2
% 0.36/1.04  sup_num_of_loops:                       7
% 0.36/1.04  sup_fw_superposition:                   3
% 0.36/1.04  sup_bw_superposition:                   1
% 0.36/1.04  sup_immediate_simplified:               3
% 0.36/1.04  sup_given_eliminated:                   0
% 0.36/1.04  comparisons_done:                       0
% 0.36/1.04  comparisons_avoided:                    0
% 0.36/1.04  
% 0.36/1.04  ------ Simplifications
% 0.36/1.04  
% 0.36/1.04  
% 0.36/1.04  sim_fw_subset_subsumed:                 1
% 0.36/1.04  sim_bw_subset_subsumed:                 0
% 0.36/1.04  sim_fw_subsumed:                        0
% 0.36/1.04  sim_bw_subsumed:                        0
% 0.36/1.04  sim_fw_subsumption_res:                 0
% 0.36/1.04  sim_bw_subsumption_res:                 0
% 0.36/1.04  sim_tautology_del:                      0
% 0.36/1.04  sim_eq_tautology_del:                   0
% 0.36/1.04  sim_eq_res_simp:                        1
% 0.36/1.04  sim_fw_demodulated:                     0
% 0.36/1.04  sim_bw_demodulated:                     0
% 0.36/1.04  sim_light_normalised:                   2
% 0.36/1.04  sim_joinable_taut:                      0
% 0.36/1.04  sim_joinable_simp:                      0
% 0.36/1.04  sim_ac_normalised:                      0
% 0.36/1.04  sim_smt_subsumption:                    0
% 0.36/1.04  
%------------------------------------------------------------------------------
