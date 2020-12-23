%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:24 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :  142 (2522 expanded)
%              Number of clauses        :   87 ( 570 expanded)
%              Number of leaves         :   12 ( 562 expanded)
%              Depth                    :   23
%              Number of atoms          :  636 (19997 expanded)
%              Number of equality atoms :  120 ( 569 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ( ~ v1_zfmisc_1(sK2)
          | ~ v3_tex_2(sK2,X0) )
        & ( v1_zfmisc_1(sK2)
          | v3_tex_2(sK2,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
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
            | ~ v3_tex_2(X1,sK1) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK1)
      & v2_tdlat_3(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( ~ v1_zfmisc_1(sK2)
      | ~ v3_tex_2(sK2,sK1) )
    & ( v1_zfmisc_1(sK2)
      | v3_tex_2(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & ~ v1_xboole_0(sK2)
    & l1_pre_topc(sK1)
    & v2_tdlat_3(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f42,f44,f43])).

fof(f74,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f45])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f23])).

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
    inference(flattening,[],[f35])).

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
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | r1_tarski(X1,sK0(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f72,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f76,plain,
    ( ~ v1_zfmisc_1(sK2)
    | ~ v3_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v1_zfmisc_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    v2_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,
    ( v1_zfmisc_1(sK2)
    | v3_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f65,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | sK0(X0,X1) != X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | v2_tex_2(sK0(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2210,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_14,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,sK0(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_553,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,sK0(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_27])).

cnf(c_554,plain,
    ( ~ v2_tex_2(X0,sK1)
    | v3_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,sK0(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_553])).

cnf(c_2201,plain,
    ( v2_tex_2(X0,sK1) != iProver_top
    | v3_tex_2(X0,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,sK0(sK1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_554])).

cnf(c_2923,plain,
    ( v2_tex_2(sK2,sK1) != iProver_top
    | v3_tex_2(sK2,sK1) = iProver_top
    | r1_tarski(sK2,sK0(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2210,c_2201])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_23,negated_conjecture,
    ( ~ v3_tex_2(sK2,sK1)
    | ~ v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_38,plain,
    ( v3_tex_2(sK2,sK1) != iProver_top
    | v1_zfmisc_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_20,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_178,plain,
    ( ~ v1_zfmisc_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_tdlat_3(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_20])).

cnf(c_179,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_zfmisc_1(X0) ),
    inference(renaming,[status(thm)],[c_178])).

cnf(c_28,negated_conjecture,
    ( v2_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_405,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_zfmisc_1(X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_179,c_28])).

cnf(c_406,plain,
    ( v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_410,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(X0,sK1)
    | ~ v1_zfmisc_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_406,c_30,c_29,c_27])).

cnf(c_411,plain,
    ( v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_zfmisc_1(X0) ),
    inference(renaming,[status(thm)],[c_410])).

cnf(c_24,negated_conjecture,
    ( v3_tex_2(sK2,sK1)
    | v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_247,plain,
    ( v1_zfmisc_1(sK2)
    | v3_tex_2(sK2,sK1) ),
    inference(prop_impl,[status(thm)],[c_24])).

cnf(c_248,plain,
    ( v3_tex_2(sK2,sK1)
    | v1_zfmisc_1(sK2) ),
    inference(renaming,[status(thm)],[c_247])).

cnf(c_663,plain,
    ( v2_tex_2(X0,sK1)
    | v3_tex_2(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_411,c_248])).

cnf(c_664,plain,
    ( v2_tex_2(sK2,sK1)
    | v3_tex_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_663])).

cnf(c_665,plain,
    ( v2_tex_2(sK2,sK1) = iProver_top
    | v3_tex_2(sK2,sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_664])).

cnf(c_18,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_480,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_481,plain,
    ( v2_tex_2(X0,sK1)
    | ~ v3_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_480])).

cnf(c_720,plain,
    ( v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_zfmisc_1(sK2)
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_248,c_481])).

cnf(c_721,plain,
    ( v2_tex_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_zfmisc_1(sK2) ),
    inference(unflattening,[status(thm)],[c_720])).

cnf(c_22,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_8,plain,
    ( v1_zfmisc_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_171,plain,
    ( v1_zfmisc_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_tdlat_3(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22,c_8])).

cnf(c_172,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_zfmisc_1(X0) ),
    inference(renaming,[status(thm)],[c_171])).

cnf(c_426,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_zfmisc_1(X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_172,c_28])).

cnf(c_427,plain,
    ( ~ v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_431,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | v1_zfmisc_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_427,c_30,c_29,c_27])).

cnf(c_432,plain,
    ( ~ v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_zfmisc_1(X0) ),
    inference(renaming,[status(thm)],[c_431])).

cnf(c_245,plain,
    ( ~ v1_zfmisc_1(sK2)
    | ~ v3_tex_2(sK2,sK1) ),
    inference(prop_impl,[status(thm)],[c_23])).

cnf(c_246,plain,
    ( ~ v3_tex_2(sK2,sK1)
    | ~ v1_zfmisc_1(sK2) ),
    inference(renaming,[status(thm)],[c_245])).

cnf(c_647,plain,
    ( ~ v2_tex_2(X0,sK1)
    | ~ v3_tex_2(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_432,c_246])).

cnf(c_648,plain,
    ( ~ v2_tex_2(sK2,sK1)
    | ~ v3_tex_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_647])).

cnf(c_723,plain,
    ( v1_zfmisc_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_721,c_25,c_24,c_648])).

cnf(c_725,plain,
    ( v1_zfmisc_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_723])).

cnf(c_739,plain,
    ( ~ v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,sK0(sK1,X0))
    | ~ v1_zfmisc_1(sK2)
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_246,c_554])).

cnf(c_740,plain,
    ( ~ v2_tex_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK2,sK0(sK1,sK2))
    | ~ v1_zfmisc_1(sK2) ),
    inference(unflattening,[status(thm)],[c_739])).

cnf(c_741,plain,
    ( v2_tex_2(sK2,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK2,sK0(sK1,sK2)) = iProver_top
    | v1_zfmisc_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_740])).

cnf(c_2926,plain,
    ( r1_tarski(sK2,sK0(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2923,c_36,c_38,c_665,c_725,c_741])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2211,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3217,plain,
    ( sK0(sK1,sK2) = sK2
    | v1_zfmisc_1(sK0(sK1,sK2)) != iProver_top
    | v1_xboole_0(sK0(sK1,sK2)) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2926,c_2211])).

cnf(c_26,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_35,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_13,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_571,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK0(X1,X0) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_27])).

cnf(c_572,plain,
    ( ~ v2_tex_2(X0,sK1)
    | v3_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK0(sK1,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_731,plain,
    ( ~ v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_zfmisc_1(sK2)
    | sK0(sK1,X0) != X0
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_246,c_572])).

cnf(c_732,plain,
    ( ~ v2_tex_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_zfmisc_1(sK2)
    | sK0(sK1,sK2) != sK2 ),
    inference(unflattening,[status(thm)],[c_731])).

cnf(c_16,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_517,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_518,plain,
    ( ~ v2_tex_2(X0,sK1)
    | v3_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_517])).

cnf(c_2203,plain,
    ( v2_tex_2(X0,sK1) != iProver_top
    | v3_tex_2(X0,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_518])).

cnf(c_2207,plain,
    ( v2_tex_2(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_zfmisc_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_432])).

cnf(c_3057,plain,
    ( v2_tex_2(X0,sK1) != iProver_top
    | v2_tex_2(sK0(sK1,X0),sK1) != iProver_top
    | v3_tex_2(X0,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_zfmisc_1(sK0(sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2203,c_2207])).

cnf(c_15,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK0(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_535,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK0(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_27])).

cnf(c_536,plain,
    ( ~ v2_tex_2(X0,sK1)
    | v2_tex_2(sK0(sK1,X0),sK1)
    | v3_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_537,plain,
    ( v2_tex_2(X0,sK1) != iProver_top
    | v2_tex_2(sK0(sK1,X0),sK1) = iProver_top
    | v3_tex_2(X0,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_536])).

cnf(c_3176,plain,
    ( v2_tex_2(X0,sK1) != iProver_top
    | v3_tex_2(X0,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_zfmisc_1(sK0(sK1,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3057,c_537])).

cnf(c_3186,plain,
    ( v2_tex_2(sK2,sK1) != iProver_top
    | v3_tex_2(sK2,sK1) = iProver_top
    | v1_zfmisc_1(sK0(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2210,c_3176])).

cnf(c_3887,plain,
    ( v1_xboole_0(sK0(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3217,c_35,c_25,c_36,c_24,c_23,c_38,c_648,c_664,c_665,c_721,c_725,c_732,c_3186])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2222,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2217,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4233,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2222,c_2217])).

cnf(c_4972,plain,
    ( sK0(sK1,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3887,c_4233])).

cnf(c_7038,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4972,c_2926])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2218,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7315,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7038,c_2218])).

cnf(c_2200,plain,
    ( sK0(sK1,X0) != X0
    | v2_tex_2(X0,sK1) != iProver_top
    | v3_tex_2(X0,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_572])).

cnf(c_7112,plain,
    ( sK2 != k1_xboole_0
    | v2_tex_2(sK2,sK1) != iProver_top
    | v3_tex_2(sK2,sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4972,c_2200])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7315,c_7112,c_725,c_665,c_38,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:25:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.33/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/0.99  
% 2.33/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.33/0.99  
% 2.33/0.99  ------  iProver source info
% 2.33/0.99  
% 2.33/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.33/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.33/0.99  git: non_committed_changes: false
% 2.33/0.99  git: last_make_outside_of_git: false
% 2.33/0.99  
% 2.33/0.99  ------ 
% 2.33/0.99  
% 2.33/0.99  ------ Input Options
% 2.33/0.99  
% 2.33/0.99  --out_options                           all
% 2.33/0.99  --tptp_safe_out                         true
% 2.33/0.99  --problem_path                          ""
% 2.33/0.99  --include_path                          ""
% 2.33/0.99  --clausifier                            res/vclausify_rel
% 2.33/0.99  --clausifier_options                    --mode clausify
% 2.33/0.99  --stdin                                 false
% 2.33/0.99  --stats_out                             all
% 2.33/0.99  
% 2.33/0.99  ------ General Options
% 2.33/0.99  
% 2.33/0.99  --fof                                   false
% 2.33/0.99  --time_out_real                         305.
% 2.33/0.99  --time_out_virtual                      -1.
% 2.33/0.99  --symbol_type_check                     false
% 2.33/0.99  --clausify_out                          false
% 2.33/0.99  --sig_cnt_out                           false
% 2.33/0.99  --trig_cnt_out                          false
% 2.33/0.99  --trig_cnt_out_tolerance                1.
% 2.33/0.99  --trig_cnt_out_sk_spl                   false
% 2.33/0.99  --abstr_cl_out                          false
% 2.33/0.99  
% 2.33/0.99  ------ Global Options
% 2.33/0.99  
% 2.33/0.99  --schedule                              default
% 2.33/0.99  --add_important_lit                     false
% 2.33/0.99  --prop_solver_per_cl                    1000
% 2.33/0.99  --min_unsat_core                        false
% 2.33/0.99  --soft_assumptions                      false
% 2.33/0.99  --soft_lemma_size                       3
% 2.33/0.99  --prop_impl_unit_size                   0
% 2.33/0.99  --prop_impl_unit                        []
% 2.33/0.99  --share_sel_clauses                     true
% 2.33/0.99  --reset_solvers                         false
% 2.33/0.99  --bc_imp_inh                            [conj_cone]
% 2.33/0.99  --conj_cone_tolerance                   3.
% 2.33/0.99  --extra_neg_conj                        none
% 2.33/0.99  --large_theory_mode                     true
% 2.33/0.99  --prolific_symb_bound                   200
% 2.33/0.99  --lt_threshold                          2000
% 2.33/0.99  --clause_weak_htbl                      true
% 2.33/0.99  --gc_record_bc_elim                     false
% 2.33/0.99  
% 2.33/0.99  ------ Preprocessing Options
% 2.33/0.99  
% 2.33/0.99  --preprocessing_flag                    true
% 2.33/0.99  --time_out_prep_mult                    0.1
% 2.33/0.99  --splitting_mode                        input
% 2.33/0.99  --splitting_grd                         true
% 2.33/0.99  --splitting_cvd                         false
% 2.33/0.99  --splitting_cvd_svl                     false
% 2.33/0.99  --splitting_nvd                         32
% 2.33/0.99  --sub_typing                            true
% 2.33/0.99  --prep_gs_sim                           true
% 2.33/0.99  --prep_unflatten                        true
% 2.33/0.99  --prep_res_sim                          true
% 2.33/0.99  --prep_upred                            true
% 2.33/0.99  --prep_sem_filter                       exhaustive
% 2.33/0.99  --prep_sem_filter_out                   false
% 2.33/0.99  --pred_elim                             true
% 2.33/0.99  --res_sim_input                         true
% 2.33/0.99  --eq_ax_congr_red                       true
% 2.33/0.99  --pure_diseq_elim                       true
% 2.33/0.99  --brand_transform                       false
% 2.33/0.99  --non_eq_to_eq                          false
% 2.33/0.99  --prep_def_merge                        true
% 2.33/0.99  --prep_def_merge_prop_impl              false
% 2.33/0.99  --prep_def_merge_mbd                    true
% 2.33/0.99  --prep_def_merge_tr_red                 false
% 2.33/0.99  --prep_def_merge_tr_cl                  false
% 2.33/0.99  --smt_preprocessing                     true
% 2.33/0.99  --smt_ac_axioms                         fast
% 2.33/0.99  --preprocessed_out                      false
% 2.33/0.99  --preprocessed_stats                    false
% 2.33/0.99  
% 2.33/0.99  ------ Abstraction refinement Options
% 2.33/0.99  
% 2.33/0.99  --abstr_ref                             []
% 2.33/0.99  --abstr_ref_prep                        false
% 2.33/0.99  --abstr_ref_until_sat                   false
% 2.33/0.99  --abstr_ref_sig_restrict                funpre
% 2.33/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/0.99  --abstr_ref_under                       []
% 2.33/0.99  
% 2.33/0.99  ------ SAT Options
% 2.33/0.99  
% 2.33/0.99  --sat_mode                              false
% 2.33/0.99  --sat_fm_restart_options                ""
% 2.33/0.99  --sat_gr_def                            false
% 2.33/0.99  --sat_epr_types                         true
% 2.33/0.99  --sat_non_cyclic_types                  false
% 2.33/0.99  --sat_finite_models                     false
% 2.33/0.99  --sat_fm_lemmas                         false
% 2.33/0.99  --sat_fm_prep                           false
% 2.33/0.99  --sat_fm_uc_incr                        true
% 2.33/0.99  --sat_out_model                         small
% 2.33/0.99  --sat_out_clauses                       false
% 2.33/0.99  
% 2.33/0.99  ------ QBF Options
% 2.33/0.99  
% 2.33/0.99  --qbf_mode                              false
% 2.33/0.99  --qbf_elim_univ                         false
% 2.33/0.99  --qbf_dom_inst                          none
% 2.33/0.99  --qbf_dom_pre_inst                      false
% 2.33/0.99  --qbf_sk_in                             false
% 2.33/0.99  --qbf_pred_elim                         true
% 2.33/0.99  --qbf_split                             512
% 2.33/0.99  
% 2.33/0.99  ------ BMC1 Options
% 2.33/0.99  
% 2.33/0.99  --bmc1_incremental                      false
% 2.33/0.99  --bmc1_axioms                           reachable_all
% 2.33/0.99  --bmc1_min_bound                        0
% 2.33/0.99  --bmc1_max_bound                        -1
% 2.33/0.99  --bmc1_max_bound_default                -1
% 2.33/0.99  --bmc1_symbol_reachability              true
% 2.33/0.99  --bmc1_property_lemmas                  false
% 2.33/0.99  --bmc1_k_induction                      false
% 2.33/0.99  --bmc1_non_equiv_states                 false
% 2.33/0.99  --bmc1_deadlock                         false
% 2.33/0.99  --bmc1_ucm                              false
% 2.33/0.99  --bmc1_add_unsat_core                   none
% 2.33/0.99  --bmc1_unsat_core_children              false
% 2.33/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/0.99  --bmc1_out_stat                         full
% 2.33/0.99  --bmc1_ground_init                      false
% 2.33/0.99  --bmc1_pre_inst_next_state              false
% 2.33/0.99  --bmc1_pre_inst_state                   false
% 2.33/0.99  --bmc1_pre_inst_reach_state             false
% 2.33/0.99  --bmc1_out_unsat_core                   false
% 2.33/0.99  --bmc1_aig_witness_out                  false
% 2.33/0.99  --bmc1_verbose                          false
% 2.33/0.99  --bmc1_dump_clauses_tptp                false
% 2.33/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.33/0.99  --bmc1_dump_file                        -
% 2.33/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.33/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.33/0.99  --bmc1_ucm_extend_mode                  1
% 2.33/0.99  --bmc1_ucm_init_mode                    2
% 2.33/0.99  --bmc1_ucm_cone_mode                    none
% 2.33/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.33/0.99  --bmc1_ucm_relax_model                  4
% 2.33/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.33/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/0.99  --bmc1_ucm_layered_model                none
% 2.33/0.99  --bmc1_ucm_max_lemma_size               10
% 2.33/0.99  
% 2.33/0.99  ------ AIG Options
% 2.33/0.99  
% 2.33/0.99  --aig_mode                              false
% 2.33/0.99  
% 2.33/0.99  ------ Instantiation Options
% 2.33/0.99  
% 2.33/0.99  --instantiation_flag                    true
% 2.33/0.99  --inst_sos_flag                         false
% 2.33/0.99  --inst_sos_phase                        true
% 2.33/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/0.99  --inst_lit_sel_side                     num_symb
% 2.33/0.99  --inst_solver_per_active                1400
% 2.33/0.99  --inst_solver_calls_frac                1.
% 2.33/0.99  --inst_passive_queue_type               priority_queues
% 2.33/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/0.99  --inst_passive_queues_freq              [25;2]
% 2.33/0.99  --inst_dismatching                      true
% 2.33/0.99  --inst_eager_unprocessed_to_passive     true
% 2.33/0.99  --inst_prop_sim_given                   true
% 2.33/0.99  --inst_prop_sim_new                     false
% 2.33/0.99  --inst_subs_new                         false
% 2.33/0.99  --inst_eq_res_simp                      false
% 2.33/0.99  --inst_subs_given                       false
% 2.33/0.99  --inst_orphan_elimination               true
% 2.33/0.99  --inst_learning_loop_flag               true
% 2.33/0.99  --inst_learning_start                   3000
% 2.33/0.99  --inst_learning_factor                  2
% 2.33/0.99  --inst_start_prop_sim_after_learn       3
% 2.33/0.99  --inst_sel_renew                        solver
% 2.33/0.99  --inst_lit_activity_flag                true
% 2.33/0.99  --inst_restr_to_given                   false
% 2.33/0.99  --inst_activity_threshold               500
% 2.33/0.99  --inst_out_proof                        true
% 2.33/0.99  
% 2.33/0.99  ------ Resolution Options
% 2.33/0.99  
% 2.33/0.99  --resolution_flag                       true
% 2.33/0.99  --res_lit_sel                           adaptive
% 2.33/0.99  --res_lit_sel_side                      none
% 2.33/0.99  --res_ordering                          kbo
% 2.33/0.99  --res_to_prop_solver                    active
% 2.33/0.99  --res_prop_simpl_new                    false
% 2.33/0.99  --res_prop_simpl_given                  true
% 2.33/0.99  --res_passive_queue_type                priority_queues
% 2.33/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/0.99  --res_passive_queues_freq               [15;5]
% 2.33/0.99  --res_forward_subs                      full
% 2.33/0.99  --res_backward_subs                     full
% 2.33/0.99  --res_forward_subs_resolution           true
% 2.33/0.99  --res_backward_subs_resolution          true
% 2.33/0.99  --res_orphan_elimination                true
% 2.33/0.99  --res_time_limit                        2.
% 2.33/0.99  --res_out_proof                         true
% 2.33/0.99  
% 2.33/0.99  ------ Superposition Options
% 2.33/0.99  
% 2.33/0.99  --superposition_flag                    true
% 2.33/0.99  --sup_passive_queue_type                priority_queues
% 2.33/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.33/0.99  --demod_completeness_check              fast
% 2.33/0.99  --demod_use_ground                      true
% 2.33/0.99  --sup_to_prop_solver                    passive
% 2.33/0.99  --sup_prop_simpl_new                    true
% 2.33/0.99  --sup_prop_simpl_given                  true
% 2.33/0.99  --sup_fun_splitting                     false
% 2.33/0.99  --sup_smt_interval                      50000
% 2.33/0.99  
% 2.33/0.99  ------ Superposition Simplification Setup
% 2.33/0.99  
% 2.33/0.99  --sup_indices_passive                   []
% 2.33/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.99  --sup_full_bw                           [BwDemod]
% 2.33/0.99  --sup_immed_triv                        [TrivRules]
% 2.33/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.99  --sup_immed_bw_main                     []
% 2.33/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.99  
% 2.33/0.99  ------ Combination Options
% 2.33/0.99  
% 2.33/0.99  --comb_res_mult                         3
% 2.33/0.99  --comb_sup_mult                         2
% 2.33/0.99  --comb_inst_mult                        10
% 2.33/0.99  
% 2.33/0.99  ------ Debug Options
% 2.33/0.99  
% 2.33/0.99  --dbg_backtrace                         false
% 2.33/0.99  --dbg_dump_prop_clauses                 false
% 2.33/0.99  --dbg_dump_prop_clauses_file            -
% 2.33/0.99  --dbg_out_stat                          false
% 2.33/0.99  ------ Parsing...
% 2.33/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.33/0.99  
% 2.33/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.33/0.99  
% 2.33/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.33/0.99  
% 2.33/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.33/0.99  ------ Proving...
% 2.33/0.99  ------ Problem Properties 
% 2.33/0.99  
% 2.33/0.99  
% 2.33/0.99  clauses                                 26
% 2.33/0.99  conjectures                             2
% 2.33/0.99  EPR                                     10
% 2.33/0.99  Horn                                    21
% 2.33/0.99  unary                                   8
% 2.33/0.99  binary                                  6
% 2.33/0.99  lits                                    65
% 2.33/0.99  lits eq                                 7
% 2.33/0.99  fd_pure                                 0
% 2.33/0.99  fd_pseudo                               0
% 2.33/0.99  fd_cond                                 1
% 2.33/0.99  fd_pseudo_cond                          4
% 2.33/0.99  AC symbols                              0
% 2.33/0.99  
% 2.33/0.99  ------ Schedule dynamic 5 is on 
% 2.33/0.99  
% 2.33/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.33/0.99  
% 2.33/0.99  
% 2.33/0.99  ------ 
% 2.33/0.99  Current options:
% 2.33/0.99  ------ 
% 2.33/0.99  
% 2.33/0.99  ------ Input Options
% 2.33/0.99  
% 2.33/0.99  --out_options                           all
% 2.33/0.99  --tptp_safe_out                         true
% 2.33/0.99  --problem_path                          ""
% 2.33/0.99  --include_path                          ""
% 2.33/0.99  --clausifier                            res/vclausify_rel
% 2.33/0.99  --clausifier_options                    --mode clausify
% 2.33/0.99  --stdin                                 false
% 2.33/0.99  --stats_out                             all
% 2.33/1.00  
% 2.33/1.00  ------ General Options
% 2.33/1.00  
% 2.33/1.00  --fof                                   false
% 2.33/1.00  --time_out_real                         305.
% 2.33/1.00  --time_out_virtual                      -1.
% 2.33/1.00  --symbol_type_check                     false
% 2.33/1.00  --clausify_out                          false
% 2.33/1.00  --sig_cnt_out                           false
% 2.33/1.00  --trig_cnt_out                          false
% 2.33/1.00  --trig_cnt_out_tolerance                1.
% 2.33/1.00  --trig_cnt_out_sk_spl                   false
% 2.33/1.00  --abstr_cl_out                          false
% 2.33/1.00  
% 2.33/1.00  ------ Global Options
% 2.33/1.00  
% 2.33/1.00  --schedule                              default
% 2.33/1.00  --add_important_lit                     false
% 2.33/1.00  --prop_solver_per_cl                    1000
% 2.33/1.00  --min_unsat_core                        false
% 2.33/1.00  --soft_assumptions                      false
% 2.33/1.00  --soft_lemma_size                       3
% 2.33/1.00  --prop_impl_unit_size                   0
% 2.33/1.00  --prop_impl_unit                        []
% 2.33/1.00  --share_sel_clauses                     true
% 2.33/1.00  --reset_solvers                         false
% 2.33/1.00  --bc_imp_inh                            [conj_cone]
% 2.33/1.00  --conj_cone_tolerance                   3.
% 2.33/1.00  --extra_neg_conj                        none
% 2.33/1.00  --large_theory_mode                     true
% 2.33/1.00  --prolific_symb_bound                   200
% 2.33/1.00  --lt_threshold                          2000
% 2.33/1.00  --clause_weak_htbl                      true
% 2.33/1.00  --gc_record_bc_elim                     false
% 2.33/1.00  
% 2.33/1.00  ------ Preprocessing Options
% 2.33/1.00  
% 2.33/1.00  --preprocessing_flag                    true
% 2.33/1.00  --time_out_prep_mult                    0.1
% 2.33/1.00  --splitting_mode                        input
% 2.33/1.00  --splitting_grd                         true
% 2.33/1.00  --splitting_cvd                         false
% 2.33/1.00  --splitting_cvd_svl                     false
% 2.33/1.00  --splitting_nvd                         32
% 2.33/1.00  --sub_typing                            true
% 2.33/1.00  --prep_gs_sim                           true
% 2.33/1.00  --prep_unflatten                        true
% 2.33/1.00  --prep_res_sim                          true
% 2.33/1.00  --prep_upred                            true
% 2.33/1.00  --prep_sem_filter                       exhaustive
% 2.33/1.00  --prep_sem_filter_out                   false
% 2.33/1.00  --pred_elim                             true
% 2.33/1.00  --res_sim_input                         true
% 2.33/1.00  --eq_ax_congr_red                       true
% 2.33/1.00  --pure_diseq_elim                       true
% 2.33/1.00  --brand_transform                       false
% 2.33/1.00  --non_eq_to_eq                          false
% 2.33/1.00  --prep_def_merge                        true
% 2.33/1.00  --prep_def_merge_prop_impl              false
% 2.33/1.00  --prep_def_merge_mbd                    true
% 2.33/1.00  --prep_def_merge_tr_red                 false
% 2.33/1.00  --prep_def_merge_tr_cl                  false
% 2.33/1.00  --smt_preprocessing                     true
% 2.33/1.00  --smt_ac_axioms                         fast
% 2.33/1.00  --preprocessed_out                      false
% 2.33/1.00  --preprocessed_stats                    false
% 2.33/1.00  
% 2.33/1.00  ------ Abstraction refinement Options
% 2.33/1.00  
% 2.33/1.00  --abstr_ref                             []
% 2.33/1.00  --abstr_ref_prep                        false
% 2.33/1.00  --abstr_ref_until_sat                   false
% 2.33/1.00  --abstr_ref_sig_restrict                funpre
% 2.33/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/1.00  --abstr_ref_under                       []
% 2.33/1.00  
% 2.33/1.00  ------ SAT Options
% 2.33/1.00  
% 2.33/1.00  --sat_mode                              false
% 2.33/1.00  --sat_fm_restart_options                ""
% 2.33/1.00  --sat_gr_def                            false
% 2.33/1.00  --sat_epr_types                         true
% 2.33/1.00  --sat_non_cyclic_types                  false
% 2.33/1.00  --sat_finite_models                     false
% 2.33/1.00  --sat_fm_lemmas                         false
% 2.33/1.00  --sat_fm_prep                           false
% 2.33/1.00  --sat_fm_uc_incr                        true
% 2.33/1.00  --sat_out_model                         small
% 2.33/1.00  --sat_out_clauses                       false
% 2.33/1.00  
% 2.33/1.00  ------ QBF Options
% 2.33/1.00  
% 2.33/1.00  --qbf_mode                              false
% 2.33/1.00  --qbf_elim_univ                         false
% 2.33/1.00  --qbf_dom_inst                          none
% 2.33/1.00  --qbf_dom_pre_inst                      false
% 2.33/1.00  --qbf_sk_in                             false
% 2.33/1.00  --qbf_pred_elim                         true
% 2.33/1.00  --qbf_split                             512
% 2.33/1.00  
% 2.33/1.00  ------ BMC1 Options
% 2.33/1.00  
% 2.33/1.00  --bmc1_incremental                      false
% 2.33/1.00  --bmc1_axioms                           reachable_all
% 2.33/1.00  --bmc1_min_bound                        0
% 2.33/1.00  --bmc1_max_bound                        -1
% 2.33/1.00  --bmc1_max_bound_default                -1
% 2.33/1.00  --bmc1_symbol_reachability              true
% 2.33/1.00  --bmc1_property_lemmas                  false
% 2.33/1.00  --bmc1_k_induction                      false
% 2.33/1.00  --bmc1_non_equiv_states                 false
% 2.33/1.00  --bmc1_deadlock                         false
% 2.33/1.00  --bmc1_ucm                              false
% 2.33/1.00  --bmc1_add_unsat_core                   none
% 2.33/1.00  --bmc1_unsat_core_children              false
% 2.33/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/1.00  --bmc1_out_stat                         full
% 2.33/1.00  --bmc1_ground_init                      false
% 2.33/1.00  --bmc1_pre_inst_next_state              false
% 2.33/1.00  --bmc1_pre_inst_state                   false
% 2.33/1.00  --bmc1_pre_inst_reach_state             false
% 2.33/1.00  --bmc1_out_unsat_core                   false
% 2.33/1.00  --bmc1_aig_witness_out                  false
% 2.33/1.00  --bmc1_verbose                          false
% 2.33/1.00  --bmc1_dump_clauses_tptp                false
% 2.33/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.33/1.00  --bmc1_dump_file                        -
% 2.33/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.33/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.33/1.00  --bmc1_ucm_extend_mode                  1
% 2.33/1.00  --bmc1_ucm_init_mode                    2
% 2.33/1.00  --bmc1_ucm_cone_mode                    none
% 2.33/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.33/1.00  --bmc1_ucm_relax_model                  4
% 2.33/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.33/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/1.00  --bmc1_ucm_layered_model                none
% 2.33/1.00  --bmc1_ucm_max_lemma_size               10
% 2.33/1.00  
% 2.33/1.00  ------ AIG Options
% 2.33/1.00  
% 2.33/1.00  --aig_mode                              false
% 2.33/1.00  
% 2.33/1.00  ------ Instantiation Options
% 2.33/1.00  
% 2.33/1.00  --instantiation_flag                    true
% 2.33/1.00  --inst_sos_flag                         false
% 2.33/1.00  --inst_sos_phase                        true
% 2.33/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/1.00  --inst_lit_sel_side                     none
% 2.33/1.00  --inst_solver_per_active                1400
% 2.33/1.00  --inst_solver_calls_frac                1.
% 2.33/1.00  --inst_passive_queue_type               priority_queues
% 2.33/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/1.00  --inst_passive_queues_freq              [25;2]
% 2.33/1.00  --inst_dismatching                      true
% 2.33/1.00  --inst_eager_unprocessed_to_passive     true
% 2.33/1.00  --inst_prop_sim_given                   true
% 2.33/1.00  --inst_prop_sim_new                     false
% 2.33/1.00  --inst_subs_new                         false
% 2.33/1.00  --inst_eq_res_simp                      false
% 2.33/1.00  --inst_subs_given                       false
% 2.33/1.00  --inst_orphan_elimination               true
% 2.33/1.00  --inst_learning_loop_flag               true
% 2.33/1.00  --inst_learning_start                   3000
% 2.33/1.00  --inst_learning_factor                  2
% 2.33/1.00  --inst_start_prop_sim_after_learn       3
% 2.33/1.00  --inst_sel_renew                        solver
% 2.33/1.00  --inst_lit_activity_flag                true
% 2.33/1.00  --inst_restr_to_given                   false
% 2.33/1.00  --inst_activity_threshold               500
% 2.33/1.00  --inst_out_proof                        true
% 2.33/1.00  
% 2.33/1.00  ------ Resolution Options
% 2.33/1.00  
% 2.33/1.00  --resolution_flag                       false
% 2.33/1.00  --res_lit_sel                           adaptive
% 2.33/1.00  --res_lit_sel_side                      none
% 2.33/1.00  --res_ordering                          kbo
% 2.33/1.00  --res_to_prop_solver                    active
% 2.33/1.00  --res_prop_simpl_new                    false
% 2.33/1.00  --res_prop_simpl_given                  true
% 2.33/1.00  --res_passive_queue_type                priority_queues
% 2.33/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/1.00  --res_passive_queues_freq               [15;5]
% 2.33/1.00  --res_forward_subs                      full
% 2.33/1.00  --res_backward_subs                     full
% 2.33/1.00  --res_forward_subs_resolution           true
% 2.33/1.00  --res_backward_subs_resolution          true
% 2.33/1.00  --res_orphan_elimination                true
% 2.33/1.00  --res_time_limit                        2.
% 2.33/1.00  --res_out_proof                         true
% 2.33/1.00  
% 2.33/1.00  ------ Superposition Options
% 2.33/1.00  
% 2.33/1.00  --superposition_flag                    true
% 2.33/1.00  --sup_passive_queue_type                priority_queues
% 2.33/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.33/1.00  --demod_completeness_check              fast
% 2.33/1.00  --demod_use_ground                      true
% 2.33/1.00  --sup_to_prop_solver                    passive
% 2.33/1.00  --sup_prop_simpl_new                    true
% 2.33/1.00  --sup_prop_simpl_given                  true
% 2.33/1.00  --sup_fun_splitting                     false
% 2.33/1.00  --sup_smt_interval                      50000
% 2.33/1.00  
% 2.33/1.00  ------ Superposition Simplification Setup
% 2.33/1.00  
% 2.33/1.00  --sup_indices_passive                   []
% 2.33/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.00  --sup_full_bw                           [BwDemod]
% 2.33/1.00  --sup_immed_triv                        [TrivRules]
% 2.33/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.00  --sup_immed_bw_main                     []
% 2.33/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/1.00  
% 2.33/1.00  ------ Combination Options
% 2.33/1.00  
% 2.33/1.00  --comb_res_mult                         3
% 2.33/1.00  --comb_sup_mult                         2
% 2.33/1.00  --comb_inst_mult                        10
% 2.33/1.00  
% 2.33/1.00  ------ Debug Options
% 2.33/1.00  
% 2.33/1.00  --dbg_backtrace                         false
% 2.33/1.00  --dbg_dump_prop_clauses                 false
% 2.33/1.00  --dbg_dump_prop_clauses_file            -
% 2.33/1.00  --dbg_out_stat                          false
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  ------ Proving...
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  % SZS status Theorem for theBenchmark.p
% 2.33/1.00  
% 2.33/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.33/1.00  
% 2.33/1.00  fof(f15,conjecture,(
% 2.33/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f16,negated_conjecture,(
% 2.33/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 2.33/1.00    inference(negated_conjecture,[],[f15])).
% 2.33/1.00  
% 2.33/1.00  fof(f30,plain,(
% 2.33/1.00    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.33/1.00    inference(ennf_transformation,[],[f16])).
% 2.33/1.00  
% 2.33/1.00  fof(f31,plain,(
% 2.33/1.00    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.33/1.00    inference(flattening,[],[f30])).
% 2.33/1.00  
% 2.33/1.00  fof(f41,plain,(
% 2.33/1.00    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.33/1.00    inference(nnf_transformation,[],[f31])).
% 2.33/1.00  
% 2.33/1.00  fof(f42,plain,(
% 2.33/1.00    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.33/1.00    inference(flattening,[],[f41])).
% 2.33/1.00  
% 2.33/1.00  fof(f44,plain,(
% 2.33/1.00    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK2) | ~v3_tex_2(sK2,X0)) & (v1_zfmisc_1(sK2) | v3_tex_2(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK2))) )),
% 2.33/1.00    introduced(choice_axiom,[])).
% 2.33/1.00  
% 2.33/1.00  fof(f43,plain,(
% 2.33/1.00    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK1)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK1) & v2_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.33/1.00    introduced(choice_axiom,[])).
% 2.33/1.00  
% 2.33/1.00  fof(f45,plain,(
% 2.33/1.00    ((~v1_zfmisc_1(sK2) | ~v3_tex_2(sK2,sK1)) & (v1_zfmisc_1(sK2) | v3_tex_2(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) & ~v1_xboole_0(sK2)) & l1_pre_topc(sK1) & v2_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.33/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f42,f44,f43])).
% 2.33/1.00  
% 2.33/1.00  fof(f74,plain,(
% 2.33/1.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.33/1.00    inference(cnf_transformation,[],[f45])).
% 2.33/1.00  
% 2.33/1.00  fof(f11,axiom,(
% 2.33/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f22,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.33/1.00    inference(ennf_transformation,[],[f11])).
% 2.33/1.00  
% 2.33/1.00  fof(f23,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.33/1.00    inference(flattening,[],[f22])).
% 2.33/1.00  
% 2.33/1.00  fof(f35,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.33/1.00    inference(nnf_transformation,[],[f23])).
% 2.33/1.00  
% 2.33/1.00  fof(f36,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.33/1.00    inference(flattening,[],[f35])).
% 2.33/1.00  
% 2.33/1.00  fof(f37,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.33/1.00    inference(rectify,[],[f36])).
% 2.33/1.00  
% 2.33/1.00  fof(f38,plain,(
% 2.33/1.00    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK0(X0,X1) != X1 & r1_tarski(X1,sK0(X0,X1)) & v2_tex_2(sK0(X0,X1),X0) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.33/1.00    introduced(choice_axiom,[])).
% 2.33/1.00  
% 2.33/1.00  fof(f39,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK0(X0,X1) != X1 & r1_tarski(X1,sK0(X0,X1)) & v2_tex_2(sK0(X0,X1),X0) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.33/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 2.33/1.00  
% 2.33/1.00  fof(f63,plain,(
% 2.33/1.00    ( ! [X0,X1] : (v3_tex_2(X1,X0) | r1_tarski(X1,sK0(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f39])).
% 2.33/1.00  
% 2.33/1.00  fof(f72,plain,(
% 2.33/1.00    l1_pre_topc(sK1)),
% 2.33/1.00    inference(cnf_transformation,[],[f45])).
% 2.33/1.00  
% 2.33/1.00  fof(f76,plain,(
% 2.33/1.00    ~v1_zfmisc_1(sK2) | ~v3_tex_2(sK2,sK1)),
% 2.33/1.00    inference(cnf_transformation,[],[f45])).
% 2.33/1.00  
% 2.33/1.00  fof(f14,axiom,(
% 2.33/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f28,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.33/1.00    inference(ennf_transformation,[],[f14])).
% 2.33/1.00  
% 2.33/1.00  fof(f29,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/1.00    inference(flattening,[],[f28])).
% 2.33/1.00  
% 2.33/1.00  fof(f40,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1)) & (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/1.00    inference(nnf_transformation,[],[f29])).
% 2.33/1.00  
% 2.33/1.00  fof(f68,plain,(
% 2.33/1.00    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f40])).
% 2.33/1.00  
% 2.33/1.00  fof(f13,axiom,(
% 2.33/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f26,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.33/1.00    inference(ennf_transformation,[],[f13])).
% 2.33/1.00  
% 2.33/1.00  fof(f27,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/1.00    inference(flattening,[],[f26])).
% 2.33/1.00  
% 2.33/1.00  fof(f66,plain,(
% 2.33/1.00    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f27])).
% 2.33/1.00  
% 2.33/1.00  fof(f71,plain,(
% 2.33/1.00    v2_tdlat_3(sK1)),
% 2.33/1.00    inference(cnf_transformation,[],[f45])).
% 2.33/1.00  
% 2.33/1.00  fof(f69,plain,(
% 2.33/1.00    ~v2_struct_0(sK1)),
% 2.33/1.00    inference(cnf_transformation,[],[f45])).
% 2.33/1.00  
% 2.33/1.00  fof(f70,plain,(
% 2.33/1.00    v2_pre_topc(sK1)),
% 2.33/1.00    inference(cnf_transformation,[],[f45])).
% 2.33/1.00  
% 2.33/1.00  fof(f75,plain,(
% 2.33/1.00    v1_zfmisc_1(sK2) | v3_tex_2(sK2,sK1)),
% 2.33/1.00    inference(cnf_transformation,[],[f45])).
% 2.33/1.00  
% 2.33/1.00  fof(f59,plain,(
% 2.33/1.00    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f39])).
% 2.33/1.00  
% 2.33/1.00  fof(f67,plain,(
% 2.33/1.00    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f40])).
% 2.33/1.00  
% 2.33/1.00  fof(f7,axiom,(
% 2.33/1.00    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f20,plain,(
% 2.33/1.00    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 2.33/1.00    inference(ennf_transformation,[],[f7])).
% 2.33/1.00  
% 2.33/1.00  fof(f54,plain,(
% 2.33/1.00    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f20])).
% 2.33/1.00  
% 2.33/1.00  fof(f12,axiom,(
% 2.33/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f24,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 2.33/1.00    inference(ennf_transformation,[],[f12])).
% 2.33/1.00  
% 2.33/1.00  fof(f25,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.33/1.00    inference(flattening,[],[f24])).
% 2.33/1.00  
% 2.33/1.00  fof(f65,plain,(
% 2.33/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f25])).
% 2.33/1.00  
% 2.33/1.00  fof(f73,plain,(
% 2.33/1.00    ~v1_xboole_0(sK2)),
% 2.33/1.00    inference(cnf_transformation,[],[f45])).
% 2.33/1.00  
% 2.33/1.00  fof(f64,plain,(
% 2.33/1.00    ( ! [X0,X1] : (v3_tex_2(X1,X0) | sK0(X0,X1) != X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f39])).
% 2.33/1.00  
% 2.33/1.00  fof(f61,plain,(
% 2.33/1.00    ( ! [X0,X1] : (v3_tex_2(X1,X0) | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f39])).
% 2.33/1.00  
% 2.33/1.00  fof(f62,plain,(
% 2.33/1.00    ( ! [X0,X1] : (v3_tex_2(X1,X0) | v2_tex_2(sK0(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f39])).
% 2.33/1.00  
% 2.33/1.00  fof(f1,axiom,(
% 2.33/1.00    v1_xboole_0(k1_xboole_0)),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f46,plain,(
% 2.33/1.00    v1_xboole_0(k1_xboole_0)),
% 2.33/1.00    inference(cnf_transformation,[],[f1])).
% 2.33/1.00  
% 2.33/1.00  fof(f6,axiom,(
% 2.33/1.00    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f19,plain,(
% 2.33/1.00    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.33/1.00    inference(ennf_transformation,[],[f6])).
% 2.33/1.00  
% 2.33/1.00  fof(f53,plain,(
% 2.33/1.00    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f19])).
% 2.33/1.00  
% 2.33/1.00  fof(f5,axiom,(
% 2.33/1.00    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f18,plain,(
% 2.33/1.00    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.33/1.00    inference(ennf_transformation,[],[f5])).
% 2.33/1.00  
% 2.33/1.00  fof(f52,plain,(
% 2.33/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f18])).
% 2.33/1.00  
% 2.33/1.00  cnf(c_25,negated_conjecture,
% 2.33/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.33/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2210,plain,
% 2.33/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_14,plain,
% 2.33/1.00      ( ~ v2_tex_2(X0,X1)
% 2.33/1.00      | v3_tex_2(X0,X1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | r1_tarski(X0,sK0(X1,X0))
% 2.33/1.00      | ~ l1_pre_topc(X1) ),
% 2.33/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_27,negated_conjecture,
% 2.33/1.00      ( l1_pre_topc(sK1) ),
% 2.33/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_553,plain,
% 2.33/1.00      ( ~ v2_tex_2(X0,X1)
% 2.33/1.00      | v3_tex_2(X0,X1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | r1_tarski(X0,sK0(X1,X0))
% 2.33/1.00      | sK1 != X1 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_27]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_554,plain,
% 2.33/1.00      ( ~ v2_tex_2(X0,sK1)
% 2.33/1.00      | v3_tex_2(X0,sK1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.33/1.00      | r1_tarski(X0,sK0(sK1,X0)) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_553]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2201,plain,
% 2.33/1.00      ( v2_tex_2(X0,sK1) != iProver_top
% 2.33/1.00      | v3_tex_2(X0,sK1) = iProver_top
% 2.33/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.33/1.00      | r1_tarski(X0,sK0(sK1,X0)) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_554]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2923,plain,
% 2.33/1.00      ( v2_tex_2(sK2,sK1) != iProver_top
% 2.33/1.00      | v3_tex_2(sK2,sK1) = iProver_top
% 2.33/1.00      | r1_tarski(sK2,sK0(sK1,sK2)) = iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_2210,c_2201]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_36,plain,
% 2.33/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_23,negated_conjecture,
% 2.33/1.00      ( ~ v3_tex_2(sK2,sK1) | ~ v1_zfmisc_1(sK2) ),
% 2.33/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_38,plain,
% 2.33/1.00      ( v3_tex_2(sK2,sK1) != iProver_top
% 2.33/1.00      | v1_zfmisc_1(sK2) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_21,plain,
% 2.33/1.00      ( v2_tex_2(X0,X1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | ~ v2_tdlat_3(X1)
% 2.33/1.00      | v2_struct_0(X1)
% 2.33/1.00      | ~ v2_pre_topc(X1)
% 2.33/1.00      | ~ l1_pre_topc(X1)
% 2.33/1.00      | ~ v1_zfmisc_1(X0)
% 2.33/1.00      | v1_xboole_0(X0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_20,plain,
% 2.33/1.00      ( v2_tex_2(X0,X1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | v2_struct_0(X1)
% 2.33/1.00      | ~ v2_pre_topc(X1)
% 2.33/1.00      | ~ l1_pre_topc(X1)
% 2.33/1.00      | ~ v1_xboole_0(X0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_178,plain,
% 2.33/1.00      ( ~ v1_zfmisc_1(X0)
% 2.33/1.00      | ~ l1_pre_topc(X1)
% 2.33/1.00      | ~ v2_pre_topc(X1)
% 2.33/1.00      | v2_struct_0(X1)
% 2.33/1.00      | ~ v2_tdlat_3(X1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | v2_tex_2(X0,X1) ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_21,c_20]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_179,plain,
% 2.33/1.00      ( v2_tex_2(X0,X1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | ~ v2_tdlat_3(X1)
% 2.33/1.00      | v2_struct_0(X1)
% 2.33/1.00      | ~ v2_pre_topc(X1)
% 2.33/1.00      | ~ l1_pre_topc(X1)
% 2.33/1.00      | ~ v1_zfmisc_1(X0) ),
% 2.33/1.00      inference(renaming,[status(thm)],[c_178]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_28,negated_conjecture,
% 2.33/1.00      ( v2_tdlat_3(sK1) ),
% 2.33/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_405,plain,
% 2.33/1.00      ( v2_tex_2(X0,X1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | v2_struct_0(X1)
% 2.33/1.00      | ~ v2_pre_topc(X1)
% 2.33/1.00      | ~ l1_pre_topc(X1)
% 2.33/1.00      | ~ v1_zfmisc_1(X0)
% 2.33/1.00      | sK1 != X1 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_179,c_28]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_406,plain,
% 2.33/1.00      ( v2_tex_2(X0,sK1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.33/1.00      | v2_struct_0(sK1)
% 2.33/1.00      | ~ v2_pre_topc(sK1)
% 2.33/1.00      | ~ l1_pre_topc(sK1)
% 2.33/1.00      | ~ v1_zfmisc_1(X0) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_405]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_30,negated_conjecture,
% 2.33/1.00      ( ~ v2_struct_0(sK1) ),
% 2.33/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_29,negated_conjecture,
% 2.33/1.00      ( v2_pre_topc(sK1) ),
% 2.33/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_410,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.33/1.00      | v2_tex_2(X0,sK1)
% 2.33/1.00      | ~ v1_zfmisc_1(X0) ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_406,c_30,c_29,c_27]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_411,plain,
% 2.33/1.00      ( v2_tex_2(X0,sK1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.33/1.00      | ~ v1_zfmisc_1(X0) ),
% 2.33/1.00      inference(renaming,[status(thm)],[c_410]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_24,negated_conjecture,
% 2.33/1.00      ( v3_tex_2(sK2,sK1) | v1_zfmisc_1(sK2) ),
% 2.33/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_247,plain,
% 2.33/1.00      ( v1_zfmisc_1(sK2) | v3_tex_2(sK2,sK1) ),
% 2.33/1.00      inference(prop_impl,[status(thm)],[c_24]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_248,plain,
% 2.33/1.00      ( v3_tex_2(sK2,sK1) | v1_zfmisc_1(sK2) ),
% 2.33/1.00      inference(renaming,[status(thm)],[c_247]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_663,plain,
% 2.33/1.00      ( v2_tex_2(X0,sK1)
% 2.33/1.00      | v3_tex_2(sK2,sK1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.33/1.00      | sK2 != X0 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_411,c_248]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_664,plain,
% 2.33/1.00      ( v2_tex_2(sK2,sK1)
% 2.33/1.00      | v3_tex_2(sK2,sK1)
% 2.33/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_663]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_665,plain,
% 2.33/1.00      ( v2_tex_2(sK2,sK1) = iProver_top
% 2.33/1.00      | v3_tex_2(sK2,sK1) = iProver_top
% 2.33/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_664]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_18,plain,
% 2.33/1.00      ( v2_tex_2(X0,X1)
% 2.33/1.00      | ~ v3_tex_2(X0,X1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | ~ l1_pre_topc(X1) ),
% 2.33/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_480,plain,
% 2.33/1.00      ( v2_tex_2(X0,X1)
% 2.33/1.00      | ~ v3_tex_2(X0,X1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | sK1 != X1 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_481,plain,
% 2.33/1.00      ( v2_tex_2(X0,sK1)
% 2.33/1.00      | ~ v3_tex_2(X0,sK1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_480]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_720,plain,
% 2.33/1.00      ( v2_tex_2(X0,sK1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.33/1.00      | v1_zfmisc_1(sK2)
% 2.33/1.00      | sK1 != sK1
% 2.33/1.00      | sK2 != X0 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_248,c_481]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_721,plain,
% 2.33/1.00      ( v2_tex_2(sK2,sK1)
% 2.33/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.33/1.00      | v1_zfmisc_1(sK2) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_720]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_22,plain,
% 2.33/1.00      ( ~ v2_tex_2(X0,X1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | ~ v2_tdlat_3(X1)
% 2.33/1.00      | v2_struct_0(X1)
% 2.33/1.00      | ~ v2_pre_topc(X1)
% 2.33/1.00      | ~ l1_pre_topc(X1)
% 2.33/1.00      | v1_zfmisc_1(X0)
% 2.33/1.00      | v1_xboole_0(X0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_8,plain,
% 2.33/1.00      ( v1_zfmisc_1(X0) | ~ v1_xboole_0(X0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_171,plain,
% 2.33/1.00      ( v1_zfmisc_1(X0)
% 2.33/1.00      | ~ l1_pre_topc(X1)
% 2.33/1.00      | ~ v2_pre_topc(X1)
% 2.33/1.00      | v2_struct_0(X1)
% 2.33/1.00      | ~ v2_tdlat_3(X1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | ~ v2_tex_2(X0,X1) ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_22,c_8]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_172,plain,
% 2.33/1.00      ( ~ v2_tex_2(X0,X1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | ~ v2_tdlat_3(X1)
% 2.33/1.00      | v2_struct_0(X1)
% 2.33/1.00      | ~ v2_pre_topc(X1)
% 2.33/1.00      | ~ l1_pre_topc(X1)
% 2.33/1.00      | v1_zfmisc_1(X0) ),
% 2.33/1.00      inference(renaming,[status(thm)],[c_171]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_426,plain,
% 2.33/1.00      ( ~ v2_tex_2(X0,X1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | v2_struct_0(X1)
% 2.33/1.00      | ~ v2_pre_topc(X1)
% 2.33/1.00      | ~ l1_pre_topc(X1)
% 2.33/1.00      | v1_zfmisc_1(X0)
% 2.33/1.00      | sK1 != X1 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_172,c_28]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_427,plain,
% 2.33/1.00      ( ~ v2_tex_2(X0,sK1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.33/1.00      | v2_struct_0(sK1)
% 2.33/1.00      | ~ v2_pre_topc(sK1)
% 2.33/1.00      | ~ l1_pre_topc(sK1)
% 2.33/1.00      | v1_zfmisc_1(X0) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_426]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_431,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.33/1.00      | ~ v2_tex_2(X0,sK1)
% 2.33/1.00      | v1_zfmisc_1(X0) ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_427,c_30,c_29,c_27]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_432,plain,
% 2.33/1.00      ( ~ v2_tex_2(X0,sK1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.33/1.00      | v1_zfmisc_1(X0) ),
% 2.33/1.00      inference(renaming,[status(thm)],[c_431]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_245,plain,
% 2.33/1.00      ( ~ v1_zfmisc_1(sK2) | ~ v3_tex_2(sK2,sK1) ),
% 2.33/1.00      inference(prop_impl,[status(thm)],[c_23]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_246,plain,
% 2.33/1.00      ( ~ v3_tex_2(sK2,sK1) | ~ v1_zfmisc_1(sK2) ),
% 2.33/1.00      inference(renaming,[status(thm)],[c_245]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_647,plain,
% 2.33/1.00      ( ~ v2_tex_2(X0,sK1)
% 2.33/1.00      | ~ v3_tex_2(sK2,sK1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.33/1.00      | sK2 != X0 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_432,c_246]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_648,plain,
% 2.33/1.00      ( ~ v2_tex_2(sK2,sK1)
% 2.33/1.00      | ~ v3_tex_2(sK2,sK1)
% 2.33/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_647]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_723,plain,
% 2.33/1.00      ( v1_zfmisc_1(sK2) ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_721,c_25,c_24,c_648]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_725,plain,
% 2.33/1.00      ( v1_zfmisc_1(sK2) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_723]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_739,plain,
% 2.33/1.00      ( ~ v2_tex_2(X0,sK1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.33/1.00      | r1_tarski(X0,sK0(sK1,X0))
% 2.33/1.00      | ~ v1_zfmisc_1(sK2)
% 2.33/1.00      | sK1 != sK1
% 2.33/1.00      | sK2 != X0 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_246,c_554]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_740,plain,
% 2.33/1.00      ( ~ v2_tex_2(sK2,sK1)
% 2.33/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.33/1.00      | r1_tarski(sK2,sK0(sK1,sK2))
% 2.33/1.00      | ~ v1_zfmisc_1(sK2) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_739]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_741,plain,
% 2.33/1.00      ( v2_tex_2(sK2,sK1) != iProver_top
% 2.33/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.33/1.00      | r1_tarski(sK2,sK0(sK1,sK2)) = iProver_top
% 2.33/1.00      | v1_zfmisc_1(sK2) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_740]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2926,plain,
% 2.33/1.00      ( r1_tarski(sK2,sK0(sK1,sK2)) = iProver_top ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_2923,c_36,c_38,c_665,c_725,c_741]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_19,plain,
% 2.33/1.00      ( ~ r1_tarski(X0,X1)
% 2.33/1.00      | ~ v1_zfmisc_1(X1)
% 2.33/1.00      | v1_xboole_0(X1)
% 2.33/1.00      | v1_xboole_0(X0)
% 2.33/1.00      | X1 = X0 ),
% 2.33/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2211,plain,
% 2.33/1.00      ( X0 = X1
% 2.33/1.00      | r1_tarski(X1,X0) != iProver_top
% 2.33/1.00      | v1_zfmisc_1(X0) != iProver_top
% 2.33/1.00      | v1_xboole_0(X1) = iProver_top
% 2.33/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3217,plain,
% 2.33/1.00      ( sK0(sK1,sK2) = sK2
% 2.33/1.00      | v1_zfmisc_1(sK0(sK1,sK2)) != iProver_top
% 2.33/1.00      | v1_xboole_0(sK0(sK1,sK2)) = iProver_top
% 2.33/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_2926,c_2211]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_26,negated_conjecture,
% 2.33/1.00      ( ~ v1_xboole_0(sK2) ),
% 2.33/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_35,plain,
% 2.33/1.00      ( v1_xboole_0(sK2) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_13,plain,
% 2.33/1.00      ( ~ v2_tex_2(X0,X1)
% 2.33/1.00      | v3_tex_2(X0,X1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | ~ l1_pre_topc(X1)
% 2.33/1.00      | sK0(X1,X0) != X0 ),
% 2.33/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_571,plain,
% 2.33/1.00      ( ~ v2_tex_2(X0,X1)
% 2.33/1.00      | v3_tex_2(X0,X1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | sK0(X1,X0) != X0
% 2.33/1.00      | sK1 != X1 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_27]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_572,plain,
% 2.33/1.00      ( ~ v2_tex_2(X0,sK1)
% 2.33/1.00      | v3_tex_2(X0,sK1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.33/1.00      | sK0(sK1,X0) != X0 ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_571]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_731,plain,
% 2.33/1.00      ( ~ v2_tex_2(X0,sK1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.33/1.00      | ~ v1_zfmisc_1(sK2)
% 2.33/1.00      | sK0(sK1,X0) != X0
% 2.33/1.00      | sK1 != sK1
% 2.33/1.00      | sK2 != X0 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_246,c_572]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_732,plain,
% 2.33/1.00      ( ~ v2_tex_2(sK2,sK1)
% 2.33/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.33/1.00      | ~ v1_zfmisc_1(sK2)
% 2.33/1.00      | sK0(sK1,sK2) != sK2 ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_731]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_16,plain,
% 2.33/1.00      ( ~ v2_tex_2(X0,X1)
% 2.33/1.00      | v3_tex_2(X0,X1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | ~ l1_pre_topc(X1) ),
% 2.33/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_517,plain,
% 2.33/1.00      ( ~ v2_tex_2(X0,X1)
% 2.33/1.00      | v3_tex_2(X0,X1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | sK1 != X1 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_518,plain,
% 2.33/1.00      ( ~ v2_tex_2(X0,sK1)
% 2.33/1.00      | v3_tex_2(X0,sK1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.33/1.00      | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_517]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2203,plain,
% 2.33/1.00      ( v2_tex_2(X0,sK1) != iProver_top
% 2.33/1.00      | v3_tex_2(X0,sK1) = iProver_top
% 2.33/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.33/1.00      | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_518]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2207,plain,
% 2.33/1.00      ( v2_tex_2(X0,sK1) != iProver_top
% 2.33/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.33/1.00      | v1_zfmisc_1(X0) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_432]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3057,plain,
% 2.33/1.00      ( v2_tex_2(X0,sK1) != iProver_top
% 2.33/1.00      | v2_tex_2(sK0(sK1,X0),sK1) != iProver_top
% 2.33/1.00      | v3_tex_2(X0,sK1) = iProver_top
% 2.33/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.33/1.00      | v1_zfmisc_1(sK0(sK1,X0)) = iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_2203,c_2207]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_15,plain,
% 2.33/1.00      ( ~ v2_tex_2(X0,X1)
% 2.33/1.00      | v2_tex_2(sK0(X1,X0),X1)
% 2.33/1.00      | v3_tex_2(X0,X1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | ~ l1_pre_topc(X1) ),
% 2.33/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_535,plain,
% 2.33/1.00      ( ~ v2_tex_2(X0,X1)
% 2.33/1.00      | v2_tex_2(sK0(X1,X0),X1)
% 2.33/1.00      | v3_tex_2(X0,X1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | sK1 != X1 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_27]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_536,plain,
% 2.33/1.00      ( ~ v2_tex_2(X0,sK1)
% 2.33/1.00      | v2_tex_2(sK0(sK1,X0),sK1)
% 2.33/1.00      | v3_tex_2(X0,sK1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_535]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_537,plain,
% 2.33/1.00      ( v2_tex_2(X0,sK1) != iProver_top
% 2.33/1.00      | v2_tex_2(sK0(sK1,X0),sK1) = iProver_top
% 2.33/1.00      | v3_tex_2(X0,sK1) = iProver_top
% 2.33/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_536]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3176,plain,
% 2.33/1.00      ( v2_tex_2(X0,sK1) != iProver_top
% 2.33/1.00      | v3_tex_2(X0,sK1) = iProver_top
% 2.33/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.33/1.00      | v1_zfmisc_1(sK0(sK1,X0)) = iProver_top ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_3057,c_537]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3186,plain,
% 2.33/1.00      ( v2_tex_2(sK2,sK1) != iProver_top
% 2.33/1.00      | v3_tex_2(sK2,sK1) = iProver_top
% 2.33/1.00      | v1_zfmisc_1(sK0(sK1,sK2)) = iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_2210,c_3176]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3887,plain,
% 2.33/1.00      ( v1_xboole_0(sK0(sK1,sK2)) = iProver_top ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_3217,c_35,c_25,c_36,c_24,c_23,c_38,c_648,c_664,c_665,
% 2.33/1.00                 c_721,c_725,c_732,c_3186]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_0,plain,
% 2.33/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2222,plain,
% 2.33/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_7,plain,
% 2.33/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 2.33/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2217,plain,
% 2.33/1.00      ( X0 = X1
% 2.33/1.00      | v1_xboole_0(X0) != iProver_top
% 2.33/1.00      | v1_xboole_0(X1) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_4233,plain,
% 2.33/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_2222,c_2217]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_4972,plain,
% 2.33/1.00      ( sK0(sK1,sK2) = k1_xboole_0 ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_3887,c_4233]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_7038,plain,
% 2.33/1.00      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 2.33/1.00      inference(demodulation,[status(thm)],[c_4972,c_2926]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_6,plain,
% 2.33/1.00      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 2.33/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2218,plain,
% 2.33/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_7315,plain,
% 2.33/1.00      ( sK2 = k1_xboole_0 ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_7038,c_2218]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2200,plain,
% 2.33/1.00      ( sK0(sK1,X0) != X0
% 2.33/1.00      | v2_tex_2(X0,sK1) != iProver_top
% 2.33/1.00      | v3_tex_2(X0,sK1) = iProver_top
% 2.33/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_572]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_7112,plain,
% 2.33/1.00      ( sK2 != k1_xboole_0
% 2.33/1.00      | v2_tex_2(sK2,sK1) != iProver_top
% 2.33/1.00      | v3_tex_2(sK2,sK1) = iProver_top
% 2.33/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_4972,c_2200]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(contradiction,plain,
% 2.33/1.00      ( $false ),
% 2.33/1.00      inference(minisat,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_7315,c_7112,c_725,c_665,c_38,c_36]) ).
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.33/1.00  
% 2.33/1.00  ------                               Statistics
% 2.33/1.00  
% 2.33/1.00  ------ General
% 2.33/1.00  
% 2.33/1.00  abstr_ref_over_cycles:                  0
% 2.33/1.00  abstr_ref_under_cycles:                 0
% 2.33/1.00  gc_basic_clause_elim:                   0
% 2.33/1.00  forced_gc_time:                         0
% 2.33/1.00  parsing_time:                           0.009
% 2.33/1.00  unif_index_cands_time:                  0.
% 2.33/1.00  unif_index_add_time:                    0.
% 2.33/1.00  orderings_time:                         0.
% 2.33/1.00  out_proof_time:                         0.007
% 2.33/1.00  total_time:                             0.204
% 2.33/1.00  num_of_symbols:                         49
% 2.33/1.00  num_of_terms:                           4042
% 2.33/1.00  
% 2.33/1.00  ------ Preprocessing
% 2.33/1.00  
% 2.33/1.00  num_of_splits:                          0
% 2.33/1.00  num_of_split_atoms:                     0
% 2.33/1.00  num_of_reused_defs:                     0
% 2.33/1.00  num_eq_ax_congr_red:                    14
% 2.33/1.00  num_of_sem_filtered_clauses:            1
% 2.33/1.00  num_of_subtypes:                        0
% 2.33/1.00  monotx_restored_types:                  0
% 2.33/1.00  sat_num_of_epr_types:                   0
% 2.33/1.00  sat_num_of_non_cyclic_types:            0
% 2.33/1.00  sat_guarded_non_collapsed_types:        0
% 2.33/1.00  num_pure_diseq_elim:                    0
% 2.33/1.00  simp_replaced_by:                       0
% 2.33/1.00  res_preprocessed:                       133
% 2.33/1.00  prep_upred:                             0
% 2.33/1.00  prep_unflattend:                        49
% 2.33/1.00  smt_new_axioms:                         0
% 2.33/1.00  pred_elim_cands:                        6
% 2.33/1.00  pred_elim:                              4
% 2.33/1.00  pred_elim_cl:                           4
% 2.33/1.00  pred_elim_cycles:                       10
% 2.33/1.00  merged_defs:                            10
% 2.33/1.00  merged_defs_ncl:                        0
% 2.33/1.00  bin_hyper_res:                          10
% 2.33/1.00  prep_cycles:                            4
% 2.33/1.00  pred_elim_time:                         0.017
% 2.33/1.00  splitting_time:                         0.
% 2.33/1.00  sem_filter_time:                        0.
% 2.33/1.00  monotx_time:                            0.001
% 2.33/1.00  subtype_inf_time:                       0.
% 2.33/1.00  
% 2.33/1.00  ------ Problem properties
% 2.33/1.00  
% 2.33/1.00  clauses:                                26
% 2.33/1.00  conjectures:                            2
% 2.33/1.00  epr:                                    10
% 2.33/1.00  horn:                                   21
% 2.33/1.00  ground:                                 5
% 2.33/1.00  unary:                                  8
% 2.33/1.00  binary:                                 6
% 2.33/1.00  lits:                                   65
% 2.33/1.00  lits_eq:                                7
% 2.33/1.00  fd_pure:                                0
% 2.33/1.00  fd_pseudo:                              0
% 2.33/1.00  fd_cond:                                1
% 2.33/1.00  fd_pseudo_cond:                         4
% 2.33/1.00  ac_symbols:                             0
% 2.33/1.00  
% 2.33/1.00  ------ Propositional Solver
% 2.33/1.00  
% 2.33/1.00  prop_solver_calls:                      29
% 2.33/1.00  prop_fast_solver_calls:                 1334
% 2.33/1.00  smt_solver_calls:                       0
% 2.33/1.00  smt_fast_solver_calls:                  0
% 2.33/1.00  prop_num_of_clauses:                    2222
% 2.33/1.00  prop_preprocess_simplified:             6589
% 2.33/1.00  prop_fo_subsumed:                       85
% 2.33/1.00  prop_solver_time:                       0.
% 2.33/1.00  smt_solver_time:                        0.
% 2.33/1.00  smt_fast_solver_time:                   0.
% 2.33/1.00  prop_fast_solver_time:                  0.
% 2.33/1.00  prop_unsat_core_time:                   0.
% 2.33/1.00  
% 2.33/1.00  ------ QBF
% 2.33/1.00  
% 2.33/1.00  qbf_q_res:                              0
% 2.33/1.00  qbf_num_tautologies:                    0
% 2.33/1.00  qbf_prep_cycles:                        0
% 2.33/1.00  
% 2.33/1.00  ------ BMC1
% 2.33/1.00  
% 2.33/1.00  bmc1_current_bound:                     -1
% 2.33/1.00  bmc1_last_solved_bound:                 -1
% 2.33/1.00  bmc1_unsat_core_size:                   -1
% 2.33/1.00  bmc1_unsat_core_parents_size:           -1
% 2.33/1.00  bmc1_merge_next_fun:                    0
% 2.33/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.33/1.00  
% 2.33/1.00  ------ Instantiation
% 2.33/1.00  
% 2.33/1.00  inst_num_of_clauses:                    638
% 2.33/1.00  inst_num_in_passive:                    265
% 2.33/1.00  inst_num_in_active:                     363
% 2.33/1.00  inst_num_in_unprocessed:                12
% 2.33/1.00  inst_num_of_loops:                      410
% 2.33/1.00  inst_num_of_learning_restarts:          0
% 2.33/1.00  inst_num_moves_active_passive:          43
% 2.33/1.00  inst_lit_activity:                      0
% 2.33/1.00  inst_lit_activity_moves:                0
% 2.33/1.00  inst_num_tautologies:                   0
% 2.33/1.00  inst_num_prop_implied:                  0
% 2.33/1.00  inst_num_existing_simplified:           0
% 2.33/1.00  inst_num_eq_res_simplified:             0
% 2.33/1.00  inst_num_child_elim:                    0
% 2.33/1.00  inst_num_of_dismatching_blockings:      178
% 2.33/1.00  inst_num_of_non_proper_insts:           827
% 2.33/1.00  inst_num_of_duplicates:                 0
% 2.33/1.00  inst_inst_num_from_inst_to_res:         0
% 2.33/1.00  inst_dismatching_checking_time:         0.
% 2.33/1.00  
% 2.33/1.00  ------ Resolution
% 2.33/1.00  
% 2.33/1.00  res_num_of_clauses:                     0
% 2.33/1.00  res_num_in_passive:                     0
% 2.33/1.00  res_num_in_active:                      0
% 2.33/1.00  res_num_of_loops:                       137
% 2.33/1.00  res_forward_subset_subsumed:            153
% 2.33/1.00  res_backward_subset_subsumed:           8
% 2.33/1.00  res_forward_subsumed:                   0
% 2.33/1.00  res_backward_subsumed:                  1
% 2.33/1.00  res_forward_subsumption_resolution:     0
% 2.33/1.00  res_backward_subsumption_resolution:    1
% 2.33/1.00  res_clause_to_clause_subsumption:       636
% 2.33/1.00  res_orphan_elimination:                 0
% 2.33/1.00  res_tautology_del:                      130
% 2.33/1.00  res_num_eq_res_simplified:              0
% 2.33/1.00  res_num_sel_changes:                    0
% 2.33/1.00  res_moves_from_active_to_pass:          0
% 2.33/1.00  
% 2.33/1.00  ------ Superposition
% 2.33/1.00  
% 2.33/1.00  sup_time_total:                         0.
% 2.33/1.00  sup_time_generating:                    0.
% 2.33/1.00  sup_time_sim_full:                      0.
% 2.33/1.00  sup_time_sim_immed:                     0.
% 2.33/1.00  
% 2.33/1.00  sup_num_of_clauses:                     103
% 2.33/1.00  sup_num_in_active:                      69
% 2.33/1.00  sup_num_in_passive:                     34
% 2.33/1.00  sup_num_of_loops:                       80
% 2.33/1.00  sup_fw_superposition:                   68
% 2.33/1.00  sup_bw_superposition:                   72
% 2.33/1.00  sup_immediate_simplified:               28
% 2.33/1.00  sup_given_eliminated:                   1
% 2.33/1.00  comparisons_done:                       0
% 2.33/1.00  comparisons_avoided:                    0
% 2.33/1.00  
% 2.33/1.00  ------ Simplifications
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  sim_fw_subset_subsumed:                 15
% 2.33/1.00  sim_bw_subset_subsumed:                 2
% 2.33/1.00  sim_fw_subsumed:                        8
% 2.33/1.00  sim_bw_subsumed:                        0
% 2.33/1.00  sim_fw_subsumption_res:                 0
% 2.33/1.00  sim_bw_subsumption_res:                 0
% 2.33/1.00  sim_tautology_del:                      7
% 2.33/1.00  sim_eq_tautology_del:                   7
% 2.33/1.00  sim_eq_res_simp:                        0
% 2.33/1.00  sim_fw_demodulated:                     0
% 2.33/1.00  sim_bw_demodulated:                     13
% 2.33/1.00  sim_light_normalised:                   6
% 2.33/1.00  sim_joinable_taut:                      0
% 2.33/1.00  sim_joinable_simp:                      0
% 2.33/1.00  sim_ac_normalised:                      0
% 2.33/1.00  sim_smt_subsumption:                    0
% 2.33/1.00  
%------------------------------------------------------------------------------
