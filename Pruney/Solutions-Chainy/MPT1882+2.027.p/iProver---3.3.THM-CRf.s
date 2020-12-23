%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:24 EST 2020

% Result     : Theorem 0.86s
% Output     : CNFRefutation 0.86s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 671 expanded)
%              Number of clauses        :   74 ( 147 expanded)
%              Number of leaves         :   12 ( 150 expanded)
%              Depth                    :   24
%              Number of atoms          :  637 (5355 expanded)
%              Number of equality atoms :   47 ( 134 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f27])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ~ v1_zfmisc_1(X1) )
            & ( v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v3_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v3_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ( ~ v1_zfmisc_1(sK3)
          | ~ v3_tex_2(sK3,X0) )
        & ( v1_zfmisc_1(sK3)
          | v3_tex_2(sK3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v3_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,sK2) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK2)
      & v2_tdlat_3(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ( ~ v1_zfmisc_1(sK3)
      | ~ v3_tex_2(sK3,sK2) )
    & ( v1_zfmisc_1(sK3)
      | v3_tex_2(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & ~ v1_xboole_0(sK3)
    & l1_pre_topc(sK2)
    & v2_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f36,f38,f37])).

fof(f56,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f57,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
    v2_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f63,plain,
    ( ~ v1_zfmisc_1(sK3)
    | ~ v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f13])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f14])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | r1_tarski(X1,sK1(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v1_zfmisc_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,
    ( v1_zfmisc_1(sK3)
    | v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | sK1(X0,X1) != X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | v2_tex_2(sK1(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_5,plain,
    ( v1_zfmisc_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_133,plain,
    ( v1_zfmisc_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_5])).

cnf(c_134,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(X0) ),
    inference(renaming,[status(thm)],[c_133])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_134,c_23])).

cnf(c_391,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_21,negated_conjecture,
    ( v2_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_395,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_zfmisc_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_391,c_22,c_21,c_20])).

cnf(c_396,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | v1_zfmisc_1(X0) ),
    inference(renaming,[status(thm)],[c_395])).

cnf(c_16,negated_conjecture,
    ( ~ v3_tex_2(sK3,sK2)
    | ~ v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_184,plain,
    ( ~ v1_zfmisc_1(sK3)
    | ~ v3_tex_2(sK3,sK2) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_185,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | ~ v1_zfmisc_1(sK3) ),
    inference(renaming,[status(thm)],[c_184])).

cnf(c_853,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | ~ v3_tex_2(sK3,sK2)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_396,c_185])).

cnf(c_854,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(sK3,sK2)
    | ~ v3_tex_2(sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_853])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_856,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ v3_tex_2(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_854,c_18])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | r1_tarski(X0,sK1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_633,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | r1_tarski(X0,sK1(X1,X0))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_634,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | r1_tarski(X0,sK1(sK2,X0)) ),
    inference(unflattening,[status(thm)],[c_633])).

cnf(c_732,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ r1_xboole_0(X1,X2)
    | v1_xboole_0(X1)
    | X0 != X1
    | sK1(sK2,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_634])).

cnf(c_733,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ r1_xboole_0(X0,sK1(sK2,X0))
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_732])).

cnf(c_958,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | ~ r1_xboole_0(X0,sK1(sK2,X0))
    | v1_xboole_0(X0)
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_856,c_733])).

cnf(c_959,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(sK3,sK2)
    | ~ r1_xboole_0(sK3,sK1(sK2,sK3))
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_958])).

cnf(c_19,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_411,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_412,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tex_2(X0,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_411])).

cnf(c_416,plain,
    ( v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_412,c_22,c_21,c_20])).

cnf(c_417,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tex_2(X0,sK2)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_416])).

cnf(c_17,negated_conjecture,
    ( v3_tex_2(sK3,sK2)
    | v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_186,plain,
    ( v1_zfmisc_1(sK3)
    | v3_tex_2(sK3,sK2) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_187,plain,
    ( v3_tex_2(sK3,sK2)
    | v1_zfmisc_1(sK3) ),
    inference(renaming,[status(thm)],[c_186])).

cnf(c_869,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tex_2(X0,sK2)
    | v3_tex_2(sK3,sK2)
    | v1_xboole_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_417,c_187])).

cnf(c_870,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tex_2(sK3,sK2)
    | v3_tex_2(sK3,sK2)
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_869])).

cnf(c_872,plain,
    ( v3_tex_2(sK3,sK2)
    | v2_tex_2(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_870,c_19,c_18])).

cnf(c_873,plain,
    ( v2_tex_2(sK3,sK2)
    | v3_tex_2(sK3,sK2) ),
    inference(renaming,[status(thm)],[c_872])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_558,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_559,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tex_2(X0,sK2)
    | ~ v3_tex_2(X0,sK2) ),
    inference(unflattening,[status(thm)],[c_558])).

cnf(c_936,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tex_2(X0,sK2)
    | v2_tex_2(sK3,sK2)
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_873,c_559])).

cnf(c_937,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tex_2(sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_936])).

cnf(c_961,plain,
    ( ~ r1_xboole_0(sK3,sK1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_959,c_19,c_18,c_937])).

cnf(c_1055,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | sK1(sK2,sK3) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_961])).

cnf(c_1056,plain,
    ( r2_hidden(sK0(sK3,sK1(sK2,sK3)),sK1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_1055])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_702,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X0 != X2
    | X1 = X2
    | sK1(sK2,X0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_634])).

cnf(c_703,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ v1_zfmisc_1(sK1(sK2,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1(sK2,X0))
    | sK1(sK2,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_702])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_651,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | sK1(X1,X0) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_20])).

cnf(c_652,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | sK1(sK2,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_651])).

cnf(c_707,plain,
    ( v1_xboole_0(sK1(sK2,X0))
    | v1_xboole_0(X0)
    | ~ v1_zfmisc_1(sK1(sK2,X0))
    | v3_tex_2(X0,sK2)
    | ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_703,c_652])).

cnf(c_708,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ v1_zfmisc_1(sK1(sK2,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1(sK2,X0)) ),
    inference(renaming,[status(thm)],[c_707])).

cnf(c_883,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | ~ v2_tex_2(X1,sK2)
    | v3_tex_2(X1,sK2)
    | v1_xboole_0(X1)
    | v1_xboole_0(sK1(sK2,X1))
    | sK1(sK2,X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_396,c_708])).

cnf(c_884,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | ~ v2_tex_2(sK1(sK2,X0),sK2)
    | v3_tex_2(X0,sK2)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1(sK2,X0)) ),
    inference(unflattening,[status(thm)],[c_883])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_597,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_598,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2) ),
    inference(unflattening,[status(thm)],[c_597])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK1(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_615,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK1(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_616,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | v2_tex_2(sK1(sK2,X0),sK2)
    | v3_tex_2(X0,sK2) ),
    inference(unflattening,[status(thm)],[c_615])).

cnf(c_888,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_tex_2(X0,sK2)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_884,c_598,c_616])).

cnf(c_889,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1(sK2,X0)) ),
    inference(renaming,[status(thm)],[c_888])).

cnf(c_947,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1(sK2,X0))
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_856,c_889])).

cnf(c_948,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(sK3,sK2)
    | v1_xboole_0(sK1(sK2,sK3))
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_947])).

cnf(c_950,plain,
    ( v1_xboole_0(sK1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_948,c_19,c_18,c_937])).

cnf(c_1010,plain,
    ( ~ r2_hidden(X0,X1)
    | sK1(sK2,sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_950])).

cnf(c_1011,plain,
    ( ~ r2_hidden(X0,sK1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_1010])).

cnf(c_1060,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1056,c_1011])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.36  % Computer   : n022.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 13:17:26 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running in FOF mode
% 0.86/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.86/1.02  
% 0.86/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.86/1.02  
% 0.86/1.02  ------  iProver source info
% 0.86/1.02  
% 0.86/1.02  git: date: 2020-06-30 10:37:57 +0100
% 0.86/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.86/1.02  git: non_committed_changes: false
% 0.86/1.02  git: last_make_outside_of_git: false
% 0.86/1.02  
% 0.86/1.02  ------ 
% 0.86/1.02  
% 0.86/1.02  ------ Input Options
% 0.86/1.02  
% 0.86/1.02  --out_options                           all
% 0.86/1.02  --tptp_safe_out                         true
% 0.86/1.02  --problem_path                          ""
% 0.86/1.02  --include_path                          ""
% 0.86/1.02  --clausifier                            res/vclausify_rel
% 0.86/1.02  --clausifier_options                    --mode clausify
% 0.86/1.02  --stdin                                 false
% 0.86/1.02  --stats_out                             all
% 0.86/1.02  
% 0.86/1.02  ------ General Options
% 0.86/1.02  
% 0.86/1.02  --fof                                   false
% 0.86/1.02  --time_out_real                         305.
% 0.86/1.02  --time_out_virtual                      -1.
% 0.86/1.02  --symbol_type_check                     false
% 0.86/1.02  --clausify_out                          false
% 0.86/1.02  --sig_cnt_out                           false
% 0.86/1.02  --trig_cnt_out                          false
% 0.86/1.02  --trig_cnt_out_tolerance                1.
% 0.86/1.02  --trig_cnt_out_sk_spl                   false
% 0.86/1.02  --abstr_cl_out                          false
% 0.86/1.02  
% 0.86/1.02  ------ Global Options
% 0.86/1.02  
% 0.86/1.02  --schedule                              default
% 0.86/1.02  --add_important_lit                     false
% 0.86/1.02  --prop_solver_per_cl                    1000
% 0.86/1.02  --min_unsat_core                        false
% 0.86/1.02  --soft_assumptions                      false
% 0.86/1.02  --soft_lemma_size                       3
% 0.86/1.02  --prop_impl_unit_size                   0
% 0.86/1.02  --prop_impl_unit                        []
% 0.86/1.02  --share_sel_clauses                     true
% 0.86/1.02  --reset_solvers                         false
% 0.86/1.02  --bc_imp_inh                            [conj_cone]
% 0.86/1.02  --conj_cone_tolerance                   3.
% 0.86/1.02  --extra_neg_conj                        none
% 0.86/1.02  --large_theory_mode                     true
% 0.86/1.02  --prolific_symb_bound                   200
% 0.86/1.02  --lt_threshold                          2000
% 0.86/1.02  --clause_weak_htbl                      true
% 0.86/1.02  --gc_record_bc_elim                     false
% 0.86/1.02  
% 0.86/1.02  ------ Preprocessing Options
% 0.86/1.02  
% 0.86/1.02  --preprocessing_flag                    true
% 0.86/1.02  --time_out_prep_mult                    0.1
% 0.86/1.02  --splitting_mode                        input
% 0.86/1.02  --splitting_grd                         true
% 0.86/1.02  --splitting_cvd                         false
% 0.86/1.02  --splitting_cvd_svl                     false
% 0.86/1.02  --splitting_nvd                         32
% 0.86/1.02  --sub_typing                            true
% 0.86/1.02  --prep_gs_sim                           true
% 0.86/1.02  --prep_unflatten                        true
% 0.86/1.02  --prep_res_sim                          true
% 0.86/1.02  --prep_upred                            true
% 0.86/1.02  --prep_sem_filter                       exhaustive
% 0.86/1.02  --prep_sem_filter_out                   false
% 0.86/1.02  --pred_elim                             true
% 0.86/1.02  --res_sim_input                         true
% 0.86/1.02  --eq_ax_congr_red                       true
% 0.86/1.02  --pure_diseq_elim                       true
% 0.86/1.02  --brand_transform                       false
% 0.86/1.02  --non_eq_to_eq                          false
% 0.86/1.02  --prep_def_merge                        true
% 0.86/1.02  --prep_def_merge_prop_impl              false
% 0.86/1.02  --prep_def_merge_mbd                    true
% 0.86/1.02  --prep_def_merge_tr_red                 false
% 0.86/1.02  --prep_def_merge_tr_cl                  false
% 0.86/1.02  --smt_preprocessing                     true
% 0.86/1.02  --smt_ac_axioms                         fast
% 0.86/1.02  --preprocessed_out                      false
% 0.86/1.02  --preprocessed_stats                    false
% 0.86/1.02  
% 0.86/1.02  ------ Abstraction refinement Options
% 0.86/1.02  
% 0.86/1.02  --abstr_ref                             []
% 0.86/1.02  --abstr_ref_prep                        false
% 0.86/1.02  --abstr_ref_until_sat                   false
% 0.86/1.02  --abstr_ref_sig_restrict                funpre
% 0.86/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 0.86/1.02  --abstr_ref_under                       []
% 0.86/1.02  
% 0.86/1.02  ------ SAT Options
% 0.86/1.02  
% 0.86/1.02  --sat_mode                              false
% 0.86/1.02  --sat_fm_restart_options                ""
% 0.86/1.02  --sat_gr_def                            false
% 0.86/1.02  --sat_epr_types                         true
% 0.86/1.02  --sat_non_cyclic_types                  false
% 0.86/1.02  --sat_finite_models                     false
% 0.86/1.02  --sat_fm_lemmas                         false
% 0.86/1.02  --sat_fm_prep                           false
% 0.86/1.02  --sat_fm_uc_incr                        true
% 0.86/1.02  --sat_out_model                         small
% 0.86/1.02  --sat_out_clauses                       false
% 0.86/1.02  
% 0.86/1.02  ------ QBF Options
% 0.86/1.02  
% 0.86/1.02  --qbf_mode                              false
% 0.86/1.02  --qbf_elim_univ                         false
% 0.86/1.02  --qbf_dom_inst                          none
% 0.86/1.02  --qbf_dom_pre_inst                      false
% 0.86/1.02  --qbf_sk_in                             false
% 0.86/1.02  --qbf_pred_elim                         true
% 0.86/1.02  --qbf_split                             512
% 0.86/1.02  
% 0.86/1.02  ------ BMC1 Options
% 0.86/1.02  
% 0.86/1.02  --bmc1_incremental                      false
% 0.86/1.02  --bmc1_axioms                           reachable_all
% 0.86/1.02  --bmc1_min_bound                        0
% 0.86/1.02  --bmc1_max_bound                        -1
% 0.86/1.02  --bmc1_max_bound_default                -1
% 0.86/1.02  --bmc1_symbol_reachability              true
% 0.86/1.02  --bmc1_property_lemmas                  false
% 0.86/1.02  --bmc1_k_induction                      false
% 0.86/1.02  --bmc1_non_equiv_states                 false
% 0.86/1.02  --bmc1_deadlock                         false
% 0.86/1.02  --bmc1_ucm                              false
% 0.86/1.02  --bmc1_add_unsat_core                   none
% 0.86/1.02  --bmc1_unsat_core_children              false
% 0.86/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 0.86/1.02  --bmc1_out_stat                         full
% 0.86/1.02  --bmc1_ground_init                      false
% 0.86/1.02  --bmc1_pre_inst_next_state              false
% 0.86/1.02  --bmc1_pre_inst_state                   false
% 0.86/1.02  --bmc1_pre_inst_reach_state             false
% 0.86/1.02  --bmc1_out_unsat_core                   false
% 0.86/1.02  --bmc1_aig_witness_out                  false
% 0.86/1.02  --bmc1_verbose                          false
% 0.86/1.02  --bmc1_dump_clauses_tptp                false
% 0.86/1.02  --bmc1_dump_unsat_core_tptp             false
% 0.86/1.02  --bmc1_dump_file                        -
% 0.86/1.02  --bmc1_ucm_expand_uc_limit              128
% 0.86/1.02  --bmc1_ucm_n_expand_iterations          6
% 0.86/1.02  --bmc1_ucm_extend_mode                  1
% 0.86/1.02  --bmc1_ucm_init_mode                    2
% 0.86/1.02  --bmc1_ucm_cone_mode                    none
% 0.86/1.02  --bmc1_ucm_reduced_relation_type        0
% 0.86/1.02  --bmc1_ucm_relax_model                  4
% 0.86/1.02  --bmc1_ucm_full_tr_after_sat            true
% 0.86/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 0.86/1.02  --bmc1_ucm_layered_model                none
% 0.86/1.02  --bmc1_ucm_max_lemma_size               10
% 0.86/1.02  
% 0.86/1.02  ------ AIG Options
% 0.86/1.02  
% 0.86/1.02  --aig_mode                              false
% 0.86/1.02  
% 0.86/1.02  ------ Instantiation Options
% 0.86/1.02  
% 0.86/1.02  --instantiation_flag                    true
% 0.86/1.02  --inst_sos_flag                         false
% 0.86/1.02  --inst_sos_phase                        true
% 0.86/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.86/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.86/1.02  --inst_lit_sel_side                     num_symb
% 0.86/1.02  --inst_solver_per_active                1400
% 0.86/1.02  --inst_solver_calls_frac                1.
% 0.86/1.02  --inst_passive_queue_type               priority_queues
% 0.86/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.86/1.02  --inst_passive_queues_freq              [25;2]
% 0.86/1.02  --inst_dismatching                      true
% 0.86/1.02  --inst_eager_unprocessed_to_passive     true
% 0.86/1.02  --inst_prop_sim_given                   true
% 0.86/1.02  --inst_prop_sim_new                     false
% 0.86/1.02  --inst_subs_new                         false
% 0.86/1.02  --inst_eq_res_simp                      false
% 0.86/1.02  --inst_subs_given                       false
% 0.86/1.02  --inst_orphan_elimination               true
% 0.86/1.02  --inst_learning_loop_flag               true
% 0.86/1.02  --inst_learning_start                   3000
% 0.86/1.02  --inst_learning_factor                  2
% 0.86/1.02  --inst_start_prop_sim_after_learn       3
% 0.86/1.02  --inst_sel_renew                        solver
% 0.86/1.02  --inst_lit_activity_flag                true
% 0.86/1.02  --inst_restr_to_given                   false
% 0.86/1.02  --inst_activity_threshold               500
% 0.86/1.02  --inst_out_proof                        true
% 0.86/1.02  
% 0.86/1.02  ------ Resolution Options
% 0.86/1.02  
% 0.86/1.02  --resolution_flag                       true
% 0.86/1.02  --res_lit_sel                           adaptive
% 0.86/1.02  --res_lit_sel_side                      none
% 0.86/1.02  --res_ordering                          kbo
% 0.86/1.02  --res_to_prop_solver                    active
% 0.86/1.02  --res_prop_simpl_new                    false
% 0.86/1.02  --res_prop_simpl_given                  true
% 0.86/1.02  --res_passive_queue_type                priority_queues
% 0.86/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.86/1.02  --res_passive_queues_freq               [15;5]
% 0.86/1.02  --res_forward_subs                      full
% 0.86/1.02  --res_backward_subs                     full
% 0.86/1.02  --res_forward_subs_resolution           true
% 0.86/1.02  --res_backward_subs_resolution          true
% 0.86/1.02  --res_orphan_elimination                true
% 0.86/1.02  --res_time_limit                        2.
% 0.86/1.02  --res_out_proof                         true
% 0.86/1.02  
% 0.86/1.02  ------ Superposition Options
% 0.86/1.02  
% 0.86/1.02  --superposition_flag                    true
% 0.86/1.02  --sup_passive_queue_type                priority_queues
% 0.86/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.86/1.02  --sup_passive_queues_freq               [8;1;4]
% 0.86/1.02  --demod_completeness_check              fast
% 0.86/1.02  --demod_use_ground                      true
% 0.86/1.02  --sup_to_prop_solver                    passive
% 0.86/1.02  --sup_prop_simpl_new                    true
% 0.86/1.02  --sup_prop_simpl_given                  true
% 0.86/1.02  --sup_fun_splitting                     false
% 0.86/1.02  --sup_smt_interval                      50000
% 0.86/1.02  
% 0.86/1.02  ------ Superposition Simplification Setup
% 0.86/1.02  
% 0.86/1.02  --sup_indices_passive                   []
% 0.86/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.86/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.86/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.86/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 0.86/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.86/1.02  --sup_full_bw                           [BwDemod]
% 0.86/1.02  --sup_immed_triv                        [TrivRules]
% 0.86/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.86/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.86/1.02  --sup_immed_bw_main                     []
% 0.86/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.86/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 0.86/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.86/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.86/1.02  
% 0.86/1.02  ------ Combination Options
% 0.86/1.02  
% 0.86/1.02  --comb_res_mult                         3
% 0.86/1.02  --comb_sup_mult                         2
% 0.86/1.02  --comb_inst_mult                        10
% 0.86/1.02  
% 0.86/1.02  ------ Debug Options
% 0.86/1.02  
% 0.86/1.02  --dbg_backtrace                         false
% 0.86/1.02  --dbg_dump_prop_clauses                 false
% 0.86/1.02  --dbg_dump_prop_clauses_file            -
% 0.86/1.02  --dbg_out_stat                          false
% 0.86/1.02  ------ Parsing...
% 0.86/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.86/1.02  
% 0.86/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s
% 0.86/1.02  
% 0.86/1.02  % SZS status Theorem for theBenchmark.p
% 0.86/1.02  
% 0.86/1.02   Resolution empty clause
% 0.86/1.02  
% 0.86/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 0.86/1.02  
% 0.86/1.02  fof(f1,axiom,(
% 0.86/1.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.86/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.86/1.02  
% 0.86/1.02  fof(f11,plain,(
% 0.86/1.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.86/1.02    inference(rectify,[],[f1])).
% 0.86/1.02  
% 0.86/1.02  fof(f12,plain,(
% 0.86/1.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.86/1.02    inference(ennf_transformation,[],[f11])).
% 0.86/1.02  
% 0.86/1.02  fof(f27,plain,(
% 0.86/1.02    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 0.86/1.02    introduced(choice_axiom,[])).
% 0.86/1.02  
% 0.86/1.02  fof(f28,plain,(
% 0.86/1.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.86/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f27])).
% 0.86/1.02  
% 0.86/1.02  fof(f41,plain,(
% 0.86/1.02    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.86/1.02    inference(cnf_transformation,[],[f28])).
% 0.86/1.02  
% 0.86/1.02  fof(f8,axiom,(
% 0.86/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.86/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.86/1.02  
% 0.86/1.02  fof(f23,plain,(
% 0.86/1.02    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.86/1.02    inference(ennf_transformation,[],[f8])).
% 0.86/1.02  
% 0.86/1.02  fof(f24,plain,(
% 0.86/1.02    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.86/1.02    inference(flattening,[],[f23])).
% 0.86/1.02  
% 0.86/1.02  fof(f34,plain,(
% 0.86/1.02    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1)) & (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.86/1.02    inference(nnf_transformation,[],[f24])).
% 0.86/1.02  
% 0.86/1.02  fof(f54,plain,(
% 0.86/1.02    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.86/1.02    inference(cnf_transformation,[],[f34])).
% 0.86/1.02  
% 0.86/1.02  fof(f4,axiom,(
% 0.86/1.02    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 0.86/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.86/1.02  
% 0.86/1.02  fof(f16,plain,(
% 0.86/1.02    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 0.86/1.02    inference(ennf_transformation,[],[f4])).
% 0.86/1.02  
% 0.86/1.02  fof(f45,plain,(
% 0.86/1.02    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 0.86/1.02    inference(cnf_transformation,[],[f16])).
% 0.86/1.02  
% 0.86/1.02  fof(f9,conjecture,(
% 0.86/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.86/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.86/1.02  
% 0.86/1.02  fof(f10,negated_conjecture,(
% 0.86/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.86/1.02    inference(negated_conjecture,[],[f9])).
% 0.86/1.02  
% 0.86/1.02  fof(f25,plain,(
% 0.86/1.02    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.86/1.02    inference(ennf_transformation,[],[f10])).
% 0.86/1.02  
% 0.86/1.02  fof(f26,plain,(
% 0.86/1.02    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.86/1.02    inference(flattening,[],[f25])).
% 0.86/1.02  
% 0.86/1.02  fof(f35,plain,(
% 0.86/1.02    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.86/1.02    inference(nnf_transformation,[],[f26])).
% 0.86/1.02  
% 0.86/1.02  fof(f36,plain,(
% 0.86/1.02    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.86/1.02    inference(flattening,[],[f35])).
% 0.86/1.02  
% 0.86/1.02  fof(f38,plain,(
% 0.86/1.02    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK3) | ~v3_tex_2(sK3,X0)) & (v1_zfmisc_1(sK3) | v3_tex_2(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK3))) )),
% 0.86/1.02    introduced(choice_axiom,[])).
% 0.86/1.02  
% 0.86/1.02  fof(f37,plain,(
% 0.86/1.02    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK2)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.86/1.02    introduced(choice_axiom,[])).
% 0.86/1.02  
% 0.86/1.02  fof(f39,plain,(
% 0.86/1.02    ((~v1_zfmisc_1(sK3) | ~v3_tex_2(sK3,sK2)) & (v1_zfmisc_1(sK3) | v3_tex_2(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.86/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f36,f38,f37])).
% 0.86/1.02  
% 0.86/1.02  fof(f56,plain,(
% 0.86/1.02    ~v2_struct_0(sK2)),
% 0.86/1.02    inference(cnf_transformation,[],[f39])).
% 0.86/1.02  
% 0.86/1.02  fof(f57,plain,(
% 0.86/1.02    v2_pre_topc(sK2)),
% 0.86/1.02    inference(cnf_transformation,[],[f39])).
% 0.86/1.02  
% 0.86/1.02  fof(f58,plain,(
% 0.86/1.02    v2_tdlat_3(sK2)),
% 0.86/1.02    inference(cnf_transformation,[],[f39])).
% 0.86/1.02  
% 0.86/1.02  fof(f59,plain,(
% 0.86/1.02    l1_pre_topc(sK2)),
% 0.86/1.02    inference(cnf_transformation,[],[f39])).
% 0.86/1.02  
% 0.86/1.02  fof(f63,plain,(
% 0.86/1.02    ~v1_zfmisc_1(sK3) | ~v3_tex_2(sK3,sK2)),
% 0.86/1.02    inference(cnf_transformation,[],[f39])).
% 0.86/1.02  
% 0.86/1.02  fof(f61,plain,(
% 0.86/1.02    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.86/1.02    inference(cnf_transformation,[],[f39])).
% 0.86/1.02  
% 0.86/1.02  fof(f2,axiom,(
% 0.86/1.02    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.86/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.86/1.02  
% 0.86/1.02  fof(f13,plain,(
% 0.86/1.02    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.86/1.02    inference(ennf_transformation,[],[f2])).
% 0.86/1.02  
% 0.86/1.02  fof(f14,plain,(
% 0.86/1.02    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.86/1.02    inference(flattening,[],[f13])).
% 0.86/1.02  
% 0.86/1.02  fof(f43,plain,(
% 0.86/1.02    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.86/1.02    inference(cnf_transformation,[],[f14])).
% 0.86/1.02  
% 0.86/1.02  fof(f6,axiom,(
% 0.86/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.86/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.86/1.02  
% 0.86/1.02  fof(f19,plain,(
% 0.86/1.02    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.86/1.02    inference(ennf_transformation,[],[f6])).
% 0.86/1.02  
% 0.86/1.02  fof(f20,plain,(
% 0.86/1.02    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.86/1.02    inference(flattening,[],[f19])).
% 0.86/1.02  
% 0.86/1.02  fof(f29,plain,(
% 0.86/1.02    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.86/1.02    inference(nnf_transformation,[],[f20])).
% 0.86/1.02  
% 0.86/1.02  fof(f30,plain,(
% 0.86/1.02    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.86/1.02    inference(flattening,[],[f29])).
% 0.86/1.02  
% 0.86/1.02  fof(f31,plain,(
% 0.86/1.02    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.86/1.02    inference(rectify,[],[f30])).
% 0.86/1.02  
% 0.86/1.02  fof(f32,plain,(
% 0.86/1.02    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK1(X0,X1) != X1 & r1_tarski(X1,sK1(X0,X1)) & v2_tex_2(sK1(X0,X1),X0) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.86/1.02    introduced(choice_axiom,[])).
% 0.86/1.02  
% 0.86/1.02  fof(f33,plain,(
% 0.86/1.02    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK1(X0,X1) != X1 & r1_tarski(X1,sK1(X0,X1)) & v2_tex_2(sK1(X0,X1),X0) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.86/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 0.86/1.02  
% 0.86/1.02  fof(f51,plain,(
% 0.86/1.02    ( ! [X0,X1] : (v3_tex_2(X1,X0) | r1_tarski(X1,sK1(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.86/1.02    inference(cnf_transformation,[],[f33])).
% 0.86/1.02  
% 0.86/1.02  fof(f60,plain,(
% 0.86/1.02    ~v1_xboole_0(sK3)),
% 0.86/1.02    inference(cnf_transformation,[],[f39])).
% 0.86/1.02  
% 0.86/1.02  fof(f55,plain,(
% 0.86/1.02    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.86/1.02    inference(cnf_transformation,[],[f34])).
% 0.86/1.02  
% 0.86/1.02  fof(f62,plain,(
% 0.86/1.02    v1_zfmisc_1(sK3) | v3_tex_2(sK3,sK2)),
% 0.86/1.02    inference(cnf_transformation,[],[f39])).
% 0.86/1.02  
% 0.86/1.02  fof(f47,plain,(
% 0.86/1.02    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.86/1.02    inference(cnf_transformation,[],[f33])).
% 0.86/1.02  
% 0.86/1.02  fof(f3,axiom,(
% 0.86/1.02    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 0.86/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.86/1.02  
% 0.86/1.02  fof(f15,plain,(
% 0.86/1.02    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.86/1.02    inference(ennf_transformation,[],[f3])).
% 0.86/1.02  
% 0.86/1.02  fof(f44,plain,(
% 0.86/1.02    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 0.86/1.02    inference(cnf_transformation,[],[f15])).
% 0.86/1.02  
% 0.86/1.02  fof(f7,axiom,(
% 0.86/1.02    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.86/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.86/1.02  
% 0.86/1.02  fof(f21,plain,(
% 0.86/1.02    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.86/1.02    inference(ennf_transformation,[],[f7])).
% 0.86/1.02  
% 0.86/1.02  fof(f22,plain,(
% 0.86/1.02    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.86/1.02    inference(flattening,[],[f21])).
% 0.86/1.02  
% 0.86/1.02  fof(f53,plain,(
% 0.86/1.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.86/1.02    inference(cnf_transformation,[],[f22])).
% 0.86/1.02  
% 0.86/1.02  fof(f52,plain,(
% 0.86/1.02    ( ! [X0,X1] : (v3_tex_2(X1,X0) | sK1(X0,X1) != X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.86/1.02    inference(cnf_transformation,[],[f33])).
% 0.86/1.02  
% 0.86/1.02  fof(f49,plain,(
% 0.86/1.02    ( ! [X0,X1] : (v3_tex_2(X1,X0) | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.86/1.02    inference(cnf_transformation,[],[f33])).
% 0.86/1.02  
% 0.86/1.02  fof(f50,plain,(
% 0.86/1.02    ( ! [X0,X1] : (v3_tex_2(X1,X0) | v2_tex_2(sK1(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.86/1.02    inference(cnf_transformation,[],[f33])).
% 0.86/1.02  
% 0.86/1.02  cnf(c_1,plain,
% 0.86/1.02      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 0.86/1.02      inference(cnf_transformation,[],[f41]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_15,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.86/1.02      | ~ v2_tex_2(X0,X1)
% 0.86/1.02      | v2_struct_0(X1)
% 0.86/1.02      | ~ l1_pre_topc(X1)
% 0.86/1.02      | ~ v2_tdlat_3(X1)
% 0.86/1.02      | ~ v2_pre_topc(X1)
% 0.86/1.02      | v1_zfmisc_1(X0)
% 0.86/1.02      | v1_xboole_0(X0) ),
% 0.86/1.02      inference(cnf_transformation,[],[f54]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_5,plain,
% 0.86/1.02      ( v1_zfmisc_1(X0) | ~ v1_xboole_0(X0) ),
% 0.86/1.02      inference(cnf_transformation,[],[f45]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_133,plain,
% 0.86/1.02      ( v1_zfmisc_1(X0)
% 0.86/1.02      | ~ v2_pre_topc(X1)
% 0.86/1.02      | ~ v2_tdlat_3(X1)
% 0.86/1.02      | ~ l1_pre_topc(X1)
% 0.86/1.02      | v2_struct_0(X1)
% 0.86/1.02      | ~ v2_tex_2(X0,X1)
% 0.86/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) ),
% 0.86/1.02      inference(global_propositional_subsumption,[status(thm)],[c_15,c_5]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_134,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.86/1.02      | ~ v2_tex_2(X0,X1)
% 0.86/1.02      | v2_struct_0(X1)
% 0.86/1.02      | ~ l1_pre_topc(X1)
% 0.86/1.02      | ~ v2_tdlat_3(X1)
% 0.86/1.02      | ~ v2_pre_topc(X1)
% 0.86/1.02      | v1_zfmisc_1(X0) ),
% 0.86/1.02      inference(renaming,[status(thm)],[c_133]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_23,negated_conjecture,
% 0.86/1.02      ( ~ v2_struct_0(sK2) ),
% 0.86/1.02      inference(cnf_transformation,[],[f56]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_390,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.86/1.02      | ~ v2_tex_2(X0,X1)
% 0.86/1.02      | ~ l1_pre_topc(X1)
% 0.86/1.02      | ~ v2_tdlat_3(X1)
% 0.86/1.02      | ~ v2_pre_topc(X1)
% 0.86/1.02      | v1_zfmisc_1(X0)
% 0.86/1.02      | sK2 != X1 ),
% 0.86/1.02      inference(resolution_lifted,[status(thm)],[c_134,c_23]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_391,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | ~ v2_tex_2(X0,sK2)
% 0.86/1.02      | ~ l1_pre_topc(sK2)
% 0.86/1.02      | ~ v2_tdlat_3(sK2)
% 0.86/1.02      | ~ v2_pre_topc(sK2)
% 0.86/1.02      | v1_zfmisc_1(X0) ),
% 0.86/1.02      inference(unflattening,[status(thm)],[c_390]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_22,negated_conjecture,
% 0.86/1.02      ( v2_pre_topc(sK2) ),
% 0.86/1.02      inference(cnf_transformation,[],[f57]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_21,negated_conjecture,
% 0.86/1.02      ( v2_tdlat_3(sK2) ),
% 0.86/1.02      inference(cnf_transformation,[],[f58]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_20,negated_conjecture,
% 0.86/1.02      ( l1_pre_topc(sK2) ),
% 0.86/1.02      inference(cnf_transformation,[],[f59]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_395,plain,
% 0.86/1.02      ( ~ v2_tex_2(X0,sK2)
% 0.86/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | v1_zfmisc_1(X0) ),
% 0.86/1.02      inference(global_propositional_subsumption,
% 0.86/1.02                [status(thm)],
% 0.86/1.02                [c_391,c_22,c_21,c_20]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_396,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | ~ v2_tex_2(X0,sK2)
% 0.86/1.02      | v1_zfmisc_1(X0) ),
% 0.86/1.02      inference(renaming,[status(thm)],[c_395]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_16,negated_conjecture,
% 0.86/1.02      ( ~ v3_tex_2(sK3,sK2) | ~ v1_zfmisc_1(sK3) ),
% 0.86/1.02      inference(cnf_transformation,[],[f63]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_184,plain,
% 0.86/1.02      ( ~ v1_zfmisc_1(sK3) | ~ v3_tex_2(sK3,sK2) ),
% 0.86/1.02      inference(prop_impl,[status(thm)],[c_16]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_185,plain,
% 0.86/1.02      ( ~ v3_tex_2(sK3,sK2) | ~ v1_zfmisc_1(sK3) ),
% 0.86/1.02      inference(renaming,[status(thm)],[c_184]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_853,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | ~ v2_tex_2(X0,sK2)
% 0.86/1.02      | ~ v3_tex_2(sK3,sK2)
% 0.86/1.02      | sK3 != X0 ),
% 0.86/1.02      inference(resolution_lifted,[status(thm)],[c_396,c_185]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_854,plain,
% 0.86/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | ~ v2_tex_2(sK3,sK2)
% 0.86/1.02      | ~ v3_tex_2(sK3,sK2) ),
% 0.86/1.02      inference(unflattening,[status(thm)],[c_853]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_18,negated_conjecture,
% 0.86/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 0.86/1.02      inference(cnf_transformation,[],[f61]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_856,plain,
% 0.86/1.02      ( ~ v2_tex_2(sK3,sK2) | ~ v3_tex_2(sK3,sK2) ),
% 0.86/1.02      inference(global_propositional_subsumption,[status(thm)],[c_854,c_18]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_3,plain,
% 0.86/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | v1_xboole_0(X0) ),
% 0.86/1.02      inference(cnf_transformation,[],[f43]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_8,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.86/1.02      | ~ v2_tex_2(X0,X1)
% 0.86/1.02      | v3_tex_2(X0,X1)
% 0.86/1.02      | r1_tarski(X0,sK1(X1,X0))
% 0.86/1.02      | ~ l1_pre_topc(X1) ),
% 0.86/1.02      inference(cnf_transformation,[],[f51]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_633,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.86/1.02      | ~ v2_tex_2(X0,X1)
% 0.86/1.02      | v3_tex_2(X0,X1)
% 0.86/1.02      | r1_tarski(X0,sK1(X1,X0))
% 0.86/1.02      | sK2 != X1 ),
% 0.86/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_20]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_634,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | ~ v2_tex_2(X0,sK2)
% 0.86/1.02      | v3_tex_2(X0,sK2)
% 0.86/1.02      | r1_tarski(X0,sK1(sK2,X0)) ),
% 0.86/1.02      inference(unflattening,[status(thm)],[c_633]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_732,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | ~ v2_tex_2(X0,sK2)
% 0.86/1.02      | v3_tex_2(X0,sK2)
% 0.86/1.02      | ~ r1_xboole_0(X1,X2)
% 0.86/1.02      | v1_xboole_0(X1)
% 0.86/1.02      | X0 != X1
% 0.86/1.02      | sK1(sK2,X0) != X2 ),
% 0.86/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_634]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_733,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | ~ v2_tex_2(X0,sK2)
% 0.86/1.02      | v3_tex_2(X0,sK2)
% 0.86/1.02      | ~ r1_xboole_0(X0,sK1(sK2,X0))
% 0.86/1.02      | v1_xboole_0(X0) ),
% 0.86/1.02      inference(unflattening,[status(thm)],[c_732]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_958,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | ~ v2_tex_2(X0,sK2)
% 0.86/1.02      | ~ v2_tex_2(sK3,sK2)
% 0.86/1.02      | ~ r1_xboole_0(X0,sK1(sK2,X0))
% 0.86/1.02      | v1_xboole_0(X0)
% 0.86/1.02      | sK2 != sK2
% 0.86/1.02      | sK3 != X0 ),
% 0.86/1.02      inference(resolution_lifted,[status(thm)],[c_856,c_733]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_959,plain,
% 0.86/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | ~ v2_tex_2(sK3,sK2)
% 0.86/1.02      | ~ r1_xboole_0(sK3,sK1(sK2,sK3))
% 0.86/1.02      | v1_xboole_0(sK3) ),
% 0.86/1.02      inference(unflattening,[status(thm)],[c_958]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_19,negated_conjecture,
% 0.86/1.02      ( ~ v1_xboole_0(sK3) ),
% 0.86/1.02      inference(cnf_transformation,[],[f60]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_14,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.86/1.02      | v2_tex_2(X0,X1)
% 0.86/1.02      | v2_struct_0(X1)
% 0.86/1.02      | ~ l1_pre_topc(X1)
% 0.86/1.02      | ~ v2_tdlat_3(X1)
% 0.86/1.02      | ~ v2_pre_topc(X1)
% 0.86/1.02      | ~ v1_zfmisc_1(X0)
% 0.86/1.02      | v1_xboole_0(X0) ),
% 0.86/1.02      inference(cnf_transformation,[],[f55]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_411,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.86/1.02      | v2_tex_2(X0,X1)
% 0.86/1.02      | ~ l1_pre_topc(X1)
% 0.86/1.02      | ~ v2_tdlat_3(X1)
% 0.86/1.02      | ~ v2_pre_topc(X1)
% 0.86/1.02      | ~ v1_zfmisc_1(X0)
% 0.86/1.02      | v1_xboole_0(X0)
% 0.86/1.02      | sK2 != X1 ),
% 0.86/1.02      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_412,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | v2_tex_2(X0,sK2)
% 0.86/1.02      | ~ l1_pre_topc(sK2)
% 0.86/1.02      | ~ v2_tdlat_3(sK2)
% 0.86/1.02      | ~ v2_pre_topc(sK2)
% 0.86/1.02      | ~ v1_zfmisc_1(X0)
% 0.86/1.02      | v1_xboole_0(X0) ),
% 0.86/1.02      inference(unflattening,[status(thm)],[c_411]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_416,plain,
% 0.86/1.02      ( v2_tex_2(X0,sK2)
% 0.86/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | ~ v1_zfmisc_1(X0)
% 0.86/1.02      | v1_xboole_0(X0) ),
% 0.86/1.02      inference(global_propositional_subsumption,
% 0.86/1.02                [status(thm)],
% 0.86/1.02                [c_412,c_22,c_21,c_20]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_417,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | v2_tex_2(X0,sK2)
% 0.86/1.02      | ~ v1_zfmisc_1(X0)
% 0.86/1.02      | v1_xboole_0(X0) ),
% 0.86/1.02      inference(renaming,[status(thm)],[c_416]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_17,negated_conjecture,
% 0.86/1.02      ( v3_tex_2(sK3,sK2) | v1_zfmisc_1(sK3) ),
% 0.86/1.02      inference(cnf_transformation,[],[f62]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_186,plain,
% 0.86/1.02      ( v1_zfmisc_1(sK3) | v3_tex_2(sK3,sK2) ),
% 0.86/1.02      inference(prop_impl,[status(thm)],[c_17]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_187,plain,
% 0.86/1.02      ( v3_tex_2(sK3,sK2) | v1_zfmisc_1(sK3) ),
% 0.86/1.02      inference(renaming,[status(thm)],[c_186]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_869,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | v2_tex_2(X0,sK2)
% 0.86/1.02      | v3_tex_2(sK3,sK2)
% 0.86/1.02      | v1_xboole_0(X0)
% 0.86/1.02      | sK3 != X0 ),
% 0.86/1.02      inference(resolution_lifted,[status(thm)],[c_417,c_187]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_870,plain,
% 0.86/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | v2_tex_2(sK3,sK2)
% 0.86/1.02      | v3_tex_2(sK3,sK2)
% 0.86/1.02      | v1_xboole_0(sK3) ),
% 0.86/1.02      inference(unflattening,[status(thm)],[c_869]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_872,plain,
% 0.86/1.02      ( v3_tex_2(sK3,sK2) | v2_tex_2(sK3,sK2) ),
% 0.86/1.02      inference(global_propositional_subsumption,
% 0.86/1.02                [status(thm)],
% 0.86/1.02                [c_870,c_19,c_18]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_873,plain,
% 0.86/1.02      ( v2_tex_2(sK3,sK2) | v3_tex_2(sK3,sK2) ),
% 0.86/1.02      inference(renaming,[status(thm)],[c_872]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_12,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.86/1.02      | v2_tex_2(X0,X1)
% 0.86/1.02      | ~ v3_tex_2(X0,X1)
% 0.86/1.02      | ~ l1_pre_topc(X1) ),
% 0.86/1.02      inference(cnf_transformation,[],[f47]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_558,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.86/1.02      | v2_tex_2(X0,X1)
% 0.86/1.02      | ~ v3_tex_2(X0,X1)
% 0.86/1.02      | sK2 != X1 ),
% 0.86/1.02      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_559,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | v2_tex_2(X0,sK2)
% 0.86/1.02      | ~ v3_tex_2(X0,sK2) ),
% 0.86/1.02      inference(unflattening,[status(thm)],[c_558]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_936,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | v2_tex_2(X0,sK2)
% 0.86/1.02      | v2_tex_2(sK3,sK2)
% 0.86/1.02      | sK2 != sK2
% 0.86/1.02      | sK3 != X0 ),
% 0.86/1.02      inference(resolution_lifted,[status(thm)],[c_873,c_559]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_937,plain,
% 0.86/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | v2_tex_2(sK3,sK2) ),
% 0.86/1.02      inference(unflattening,[status(thm)],[c_936]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_961,plain,
% 0.86/1.02      ( ~ r1_xboole_0(sK3,sK1(sK2,sK3)) ),
% 0.86/1.02      inference(global_propositional_subsumption,
% 0.86/1.02                [status(thm)],
% 0.86/1.02                [c_959,c_19,c_18,c_937]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_1055,plain,
% 0.86/1.02      ( r2_hidden(sK0(X0,X1),X1) | sK1(sK2,sK3) != X1 | sK3 != X0 ),
% 0.86/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_961]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_1056,plain,
% 0.86/1.02      ( r2_hidden(sK0(sK3,sK1(sK2,sK3)),sK1(sK2,sK3)) ),
% 0.86/1.02      inference(unflattening,[status(thm)],[c_1055]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_4,plain,
% 0.86/1.02      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 0.86/1.02      inference(cnf_transformation,[],[f44]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_13,plain,
% 0.86/1.02      ( ~ r1_tarski(X0,X1)
% 0.86/1.02      | ~ v1_zfmisc_1(X1)
% 0.86/1.02      | v1_xboole_0(X1)
% 0.86/1.02      | v1_xboole_0(X0)
% 0.86/1.02      | X1 = X0 ),
% 0.86/1.02      inference(cnf_transformation,[],[f53]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_702,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | ~ v2_tex_2(X0,sK2)
% 0.86/1.02      | v3_tex_2(X0,sK2)
% 0.86/1.02      | ~ v1_zfmisc_1(X1)
% 0.86/1.02      | v1_xboole_0(X1)
% 0.86/1.02      | v1_xboole_0(X2)
% 0.86/1.02      | X0 != X2
% 0.86/1.02      | X1 = X2
% 0.86/1.02      | sK1(sK2,X0) != X1 ),
% 0.86/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_634]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_703,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | ~ v2_tex_2(X0,sK2)
% 0.86/1.02      | v3_tex_2(X0,sK2)
% 0.86/1.02      | ~ v1_zfmisc_1(sK1(sK2,X0))
% 0.86/1.02      | v1_xboole_0(X0)
% 0.86/1.02      | v1_xboole_0(sK1(sK2,X0))
% 0.86/1.02      | sK1(sK2,X0) = X0 ),
% 0.86/1.02      inference(unflattening,[status(thm)],[c_702]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_7,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.86/1.02      | ~ v2_tex_2(X0,X1)
% 0.86/1.02      | v3_tex_2(X0,X1)
% 0.86/1.02      | ~ l1_pre_topc(X1)
% 0.86/1.02      | sK1(X1,X0) != X0 ),
% 0.86/1.02      inference(cnf_transformation,[],[f52]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_651,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.86/1.02      | ~ v2_tex_2(X0,X1)
% 0.86/1.02      | v3_tex_2(X0,X1)
% 0.86/1.02      | sK1(X1,X0) != X0
% 0.86/1.02      | sK2 != X1 ),
% 0.86/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_20]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_652,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | ~ v2_tex_2(X0,sK2)
% 0.86/1.02      | v3_tex_2(X0,sK2)
% 0.86/1.02      | sK1(sK2,X0) != X0 ),
% 0.86/1.02      inference(unflattening,[status(thm)],[c_651]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_707,plain,
% 0.86/1.02      ( v1_xboole_0(sK1(sK2,X0))
% 0.86/1.02      | v1_xboole_0(X0)
% 0.86/1.02      | ~ v1_zfmisc_1(sK1(sK2,X0))
% 0.86/1.02      | v3_tex_2(X0,sK2)
% 0.86/1.02      | ~ v2_tex_2(X0,sK2)
% 0.86/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 0.86/1.02      inference(global_propositional_subsumption,[status(thm)],[c_703,c_652]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_708,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | ~ v2_tex_2(X0,sK2)
% 0.86/1.02      | v3_tex_2(X0,sK2)
% 0.86/1.02      | ~ v1_zfmisc_1(sK1(sK2,X0))
% 0.86/1.02      | v1_xboole_0(X0)
% 0.86/1.02      | v1_xboole_0(sK1(sK2,X0)) ),
% 0.86/1.02      inference(renaming,[status(thm)],[c_707]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_883,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | ~ v2_tex_2(X0,sK2)
% 0.86/1.02      | ~ v2_tex_2(X1,sK2)
% 0.86/1.02      | v3_tex_2(X1,sK2)
% 0.86/1.02      | v1_xboole_0(X1)
% 0.86/1.02      | v1_xboole_0(sK1(sK2,X1))
% 0.86/1.02      | sK1(sK2,X1) != X0 ),
% 0.86/1.02      inference(resolution_lifted,[status(thm)],[c_396,c_708]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_884,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | ~ m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | ~ v2_tex_2(X0,sK2)
% 0.86/1.02      | ~ v2_tex_2(sK1(sK2,X0),sK2)
% 0.86/1.02      | v3_tex_2(X0,sK2)
% 0.86/1.02      | v1_xboole_0(X0)
% 0.86/1.02      | v1_xboole_0(sK1(sK2,X0)) ),
% 0.86/1.02      inference(unflattening,[status(thm)],[c_883]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_10,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.86/1.02      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 0.86/1.02      | ~ v2_tex_2(X0,X1)
% 0.86/1.02      | v3_tex_2(X0,X1)
% 0.86/1.02      | ~ l1_pre_topc(X1) ),
% 0.86/1.02      inference(cnf_transformation,[],[f49]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_597,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.86/1.02      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 0.86/1.02      | ~ v2_tex_2(X0,X1)
% 0.86/1.02      | v3_tex_2(X0,X1)
% 0.86/1.02      | sK2 != X1 ),
% 0.86/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_598,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | ~ v2_tex_2(X0,sK2)
% 0.86/1.02      | v3_tex_2(X0,sK2) ),
% 0.86/1.02      inference(unflattening,[status(thm)],[c_597]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_9,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.86/1.02      | ~ v2_tex_2(X0,X1)
% 0.86/1.02      | v2_tex_2(sK1(X1,X0),X1)
% 0.86/1.02      | v3_tex_2(X0,X1)
% 0.86/1.02      | ~ l1_pre_topc(X1) ),
% 0.86/1.02      inference(cnf_transformation,[],[f50]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_615,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.86/1.02      | ~ v2_tex_2(X0,X1)
% 0.86/1.02      | v2_tex_2(sK1(X1,X0),X1)
% 0.86/1.02      | v3_tex_2(X0,X1)
% 0.86/1.02      | sK2 != X1 ),
% 0.86/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_20]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_616,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | ~ v2_tex_2(X0,sK2)
% 0.86/1.02      | v2_tex_2(sK1(sK2,X0),sK2)
% 0.86/1.02      | v3_tex_2(X0,sK2) ),
% 0.86/1.02      inference(unflattening,[status(thm)],[c_615]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_888,plain,
% 0.86/1.02      ( ~ v2_tex_2(X0,sK2)
% 0.86/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | v3_tex_2(X0,sK2)
% 0.86/1.02      | v1_xboole_0(X0)
% 0.86/1.02      | v1_xboole_0(sK1(sK2,X0)) ),
% 0.86/1.02      inference(global_propositional_subsumption,
% 0.86/1.02                [status(thm)],
% 0.86/1.02                [c_884,c_598,c_616]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_889,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | ~ v2_tex_2(X0,sK2)
% 0.86/1.02      | v3_tex_2(X0,sK2)
% 0.86/1.02      | v1_xboole_0(X0)
% 0.86/1.02      | v1_xboole_0(sK1(sK2,X0)) ),
% 0.86/1.02      inference(renaming,[status(thm)],[c_888]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_947,plain,
% 0.86/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | ~ v2_tex_2(X0,sK2)
% 0.86/1.02      | ~ v2_tex_2(sK3,sK2)
% 0.86/1.02      | v1_xboole_0(X0)
% 0.86/1.02      | v1_xboole_0(sK1(sK2,X0))
% 0.86/1.02      | sK2 != sK2
% 0.86/1.02      | sK3 != X0 ),
% 0.86/1.02      inference(resolution_lifted,[status(thm)],[c_856,c_889]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_948,plain,
% 0.86/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.86/1.02      | ~ v2_tex_2(sK3,sK2)
% 0.86/1.02      | v1_xboole_0(sK1(sK2,sK3))
% 0.86/1.02      | v1_xboole_0(sK3) ),
% 0.86/1.02      inference(unflattening,[status(thm)],[c_947]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_950,plain,
% 0.86/1.02      ( v1_xboole_0(sK1(sK2,sK3)) ),
% 0.86/1.02      inference(global_propositional_subsumption,
% 0.86/1.02                [status(thm)],
% 0.86/1.02                [c_948,c_19,c_18,c_937]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_1010,plain,
% 0.86/1.02      ( ~ r2_hidden(X0,X1) | sK1(sK2,sK3) != X1 ),
% 0.86/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_950]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_1011,plain,
% 0.86/1.02      ( ~ r2_hidden(X0,sK1(sK2,sK3)) ),
% 0.86/1.02      inference(unflattening,[status(thm)],[c_1010]) ).
% 0.86/1.02  
% 0.86/1.02  cnf(c_1060,plain,
% 0.86/1.02      ( $false ),
% 0.86/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_1056,c_1011]) ).
% 0.86/1.02  
% 0.86/1.02  
% 0.86/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 0.86/1.02  
% 0.86/1.02  ------                               Statistics
% 0.86/1.02  
% 0.86/1.02  ------ General
% 0.86/1.02  
% 0.86/1.02  abstr_ref_over_cycles:                  0
% 0.86/1.02  abstr_ref_under_cycles:                 0
% 0.86/1.02  gc_basic_clause_elim:                   0
% 0.86/1.02  forced_gc_time:                         0
% 0.86/1.02  parsing_time:                           0.012
% 0.86/1.02  unif_index_cands_time:                  0.
% 0.86/1.02  unif_index_add_time:                    0.
% 0.86/1.02  orderings_time:                         0.
% 0.86/1.02  out_proof_time:                         0.014
% 0.86/1.02  total_time:                             0.062
% 0.86/1.02  num_of_symbols:                         46
% 0.86/1.02  num_of_terms:                           642
% 0.86/1.02  
% 0.86/1.02  ------ Preprocessing
% 0.86/1.02  
% 0.86/1.02  num_of_splits:                          0
% 0.86/1.02  num_of_split_atoms:                     0
% 0.86/1.02  num_of_reused_defs:                     0
% 0.86/1.02  num_eq_ax_congr_red:                    9
% 0.86/1.02  num_of_sem_filtered_clauses:            0
% 0.86/1.02  num_of_subtypes:                        0
% 0.86/1.02  monotx_restored_types:                  0
% 0.86/1.02  sat_num_of_epr_types:                   0
% 0.86/1.02  sat_num_of_non_cyclic_types:            0
% 0.86/1.02  sat_guarded_non_collapsed_types:        0
% 0.86/1.02  num_pure_diseq_elim:                    0
% 0.86/1.02  simp_replaced_by:                       0
% 0.86/1.02  res_preprocessed:                       24
% 0.86/1.02  prep_upred:                             0
% 0.86/1.02  prep_unflattend:                        52
% 0.86/1.02  smt_new_axioms:                         0
% 0.86/1.02  pred_elim_cands:                        12
% 0.86/1.02  pred_elim:                              10
% 0.86/1.02  pred_elim_cl:                           0
% 0.86/1.02  pred_elim_cycles:                       13
% 0.86/1.02  merged_defs:                            2
% 0.86/1.02  merged_defs_ncl:                        0
% 0.86/1.02  bin_hyper_res:                          2
% 0.86/1.02  prep_cycles:                            1
% 0.86/1.02  pred_elim_time:                         0.
% 0.86/1.02  splitting_time:                         0.
% 0.86/1.02  sem_filter_time:                        0.
% 0.86/1.02  monotx_time:                            0.
% 0.86/1.02  subtype_inf_time:                       0.
% 0.86/1.02  
% 0.86/1.02  ------ Problem properties
% 0.86/1.02  
% 0.86/1.02  clauses:                                0
% 0.86/1.02  conjectures:                            0
% 0.86/1.02  epr:                                    0
% 0.86/1.02  horn:                                   0
% 0.86/1.02  ground:                                 0
% 0.86/1.02  unary:                                  0
% 0.86/1.02  binary:                                 0
% 0.86/1.02  lits:                                   0
% 0.86/1.02  lits_eq:                                0
% 0.86/1.02  fd_pure:                                0
% 0.86/1.02  fd_pseudo:                              0
% 0.86/1.02  fd_cond:                                0
% 0.86/1.02  fd_pseudo_cond:                         0
% 0.86/1.02  ac_symbols:                             undef
% 0.86/1.02  
% 0.86/1.02  ------ Propositional Solver
% 0.86/1.02  
% 0.86/1.02  prop_solver_calls:                      6
% 0.86/1.02  prop_fast_solver_calls:                 364
% 0.86/1.02  smt_solver_calls:                       0
% 0.86/1.02  smt_fast_solver_calls:                  0
% 0.86/1.02  prop_num_of_clauses:                    216
% 0.86/1.02  prop_preprocess_simplified:             842
% 0.86/1.02  prop_fo_subsumed:                       30
% 0.86/1.02  prop_solver_time:                       0.
% 0.86/1.02  smt_solver_time:                        0.
% 0.86/1.02  smt_fast_solver_time:                   0.
% 0.86/1.02  prop_fast_solver_time:                  0.
% 0.86/1.02  prop_unsat_core_time:                   0.
% 0.86/1.02  
% 0.86/1.02  ------ QBF
% 0.86/1.02  
% 0.86/1.02  qbf_q_res:                              0
% 0.86/1.02  qbf_num_tautologies:                    0
% 0.86/1.02  qbf_prep_cycles:                        0
% 0.86/1.02  
% 0.86/1.02  ------ BMC1
% 0.86/1.02  
% 0.86/1.02  bmc1_current_bound:                     -1
% 0.86/1.02  bmc1_last_solved_bound:                 -1
% 0.86/1.02  bmc1_unsat_core_size:                   -1
% 0.86/1.02  bmc1_unsat_core_parents_size:           -1
% 0.86/1.02  bmc1_merge_next_fun:                    0
% 0.86/1.02  bmc1_unsat_core_clauses_time:           0.
% 0.86/1.02  
% 0.86/1.02  ------ Instantiation
% 0.86/1.02  
% 0.86/1.02  inst_num_of_clauses:                    undef
% 0.86/1.02  inst_num_in_passive:                    undef
% 0.86/1.02  inst_num_in_active:                     0
% 0.86/1.02  inst_num_in_unprocessed:                0
% 0.86/1.02  inst_num_of_loops:                      0
% 0.86/1.02  inst_num_of_learning_restarts:          0
% 0.86/1.02  inst_num_moves_active_passive:          0
% 0.86/1.02  inst_lit_activity:                      0
% 0.86/1.02  inst_lit_activity_moves:                0
% 0.86/1.02  inst_num_tautologies:                   0
% 0.86/1.02  inst_num_prop_implied:                  0
% 0.86/1.02  inst_num_existing_simplified:           0
% 0.86/1.02  inst_num_eq_res_simplified:             0
% 0.86/1.02  inst_num_child_elim:                    0
% 0.86/1.02  inst_num_of_dismatching_blockings:      0
% 0.86/1.02  inst_num_of_non_proper_insts:           0
% 0.86/1.02  inst_num_of_duplicates:                 0
% 0.86/1.02  inst_inst_num_from_inst_to_res:         0
% 0.86/1.02  inst_dismatching_checking_time:         0.
% 0.86/1.02  
% 0.86/1.02  ------ Resolution
% 0.86/1.02  
% 0.86/1.02  res_num_of_clauses:                     24
% 0.86/1.02  res_num_in_passive:                     0
% 0.86/1.02  res_num_in_active:                      0
% 0.86/1.02  res_num_of_loops:                       25
% 0.86/1.02  res_forward_subset_subsumed:            2
% 0.86/1.02  res_backward_subset_subsumed:           0
% 0.86/1.02  res_forward_subsumed:                   1
% 0.86/1.02  res_backward_subsumed:                  0
% 0.86/1.02  res_forward_subsumption_resolution:     1
% 0.86/1.02  res_backward_subsumption_resolution:    0
% 0.86/1.02  res_clause_to_clause_subsumption:       19
% 0.86/1.02  res_orphan_elimination:                 0
% 0.86/1.02  res_tautology_del:                      15
% 0.86/1.02  res_num_eq_res_simplified:              0
% 0.86/1.02  res_num_sel_changes:                    0
% 0.86/1.02  res_moves_from_active_to_pass:          0
% 0.86/1.02  
% 0.86/1.02  ------ Superposition
% 0.86/1.02  
% 0.86/1.02  sup_time_total:                         0.
% 0.86/1.02  sup_time_generating:                    0.
% 0.86/1.02  sup_time_sim_full:                      0.
% 0.86/1.02  sup_time_sim_immed:                     0.
% 0.86/1.02  
% 0.86/1.02  sup_num_of_clauses:                     undef
% 0.86/1.02  sup_num_in_active:                      undef
% 0.86/1.02  sup_num_in_passive:                     undef
% 0.86/1.02  sup_num_of_loops:                       0
% 0.86/1.02  sup_fw_superposition:                   0
% 0.86/1.02  sup_bw_superposition:                   0
% 0.86/1.02  sup_immediate_simplified:               0
% 0.86/1.02  sup_given_eliminated:                   0
% 0.86/1.02  comparisons_done:                       0
% 0.86/1.02  comparisons_avoided:                    0
% 0.86/1.02  
% 0.86/1.02  ------ Simplifications
% 0.86/1.02  
% 0.86/1.02  
% 0.86/1.02  sim_fw_subset_subsumed:                 0
% 0.86/1.02  sim_bw_subset_subsumed:                 0
% 0.86/1.02  sim_fw_subsumed:                        0
% 0.86/1.02  sim_bw_subsumed:                        0
% 0.86/1.02  sim_fw_subsumption_res:                 0
% 0.86/1.02  sim_bw_subsumption_res:                 0
% 0.86/1.02  sim_tautology_del:                      0
% 0.86/1.02  sim_eq_tautology_del:                   0
% 0.86/1.02  sim_eq_res_simp:                        0
% 0.86/1.02  sim_fw_demodulated:                     0
% 0.86/1.02  sim_bw_demodulated:                     0
% 0.86/1.02  sim_light_normalised:                   0
% 0.86/1.02  sim_joinable_taut:                      0
% 0.86/1.02  sim_joinable_simp:                      0
% 0.86/1.02  sim_ac_normalised:                      0
% 0.86/1.02  sim_smt_subsumption:                    0
% 0.86/1.02  
%------------------------------------------------------------------------------
