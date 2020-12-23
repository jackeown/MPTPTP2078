%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:50 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :  237 (2602 expanded)
%              Number of clauses        :  148 ( 640 expanded)
%              Number of leaves         :   26 ( 593 expanded)
%              Depth                    :   32
%              Number of atoms          :  927 (19201 expanded)
%              Number of equality atoms :  198 ( 757 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v2_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ( ~ v1_zfmisc_1(sK4)
          | ~ v2_tex_2(sK4,X0) )
        & ( v1_zfmisc_1(sK4)
          | v2_tex_2(sK4,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v2_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,sK3) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,sK3) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK3)
      & v2_tdlat_3(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ( ~ v1_zfmisc_1(sK4)
      | ~ v2_tex_2(sK4,sK3) )
    & ( v1_zfmisc_1(sK4)
      | v2_tex_2(sK4,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & ~ v1_xboole_0(sK4)
    & l1_pre_topc(sK3)
    & v2_tdlat_3(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f56,f58,f57])).

fof(f95,plain,
    ( v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f94,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f59])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK2(X0,X1)) = X1
        & m1_pre_topc(sK2(X0,X1),X0)
        & v1_tdlat_3(sK2(X0,X1))
        & ~ v2_struct_0(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK2(X0,X1)) = X1
            & m1_pre_topc(sK2(X0,X1),X0)
            & v1_tdlat_3(sK2(X0,X1))
            & ~ v2_struct_0(sK2(X0,X1)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f53])).

fof(f87,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK2(X0,X1)) = X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f90,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f89,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f92,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f93,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).

fof(f61,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f83,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK2(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( ~ v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ( ~ v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X1)
      | v7_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f76,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f78,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f77,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f80,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f91,plain,(
    v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f46])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f48,f49])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f98,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f96,plain,
    ( ~ v1_zfmisc_1(sK4)
    | ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_30,negated_conjecture,
    ( v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2976,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2975,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_24,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1121,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(X1,X0)) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_35])).

cnf(c_1122,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(sK3,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_1121])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1126,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1122,c_36,c_33])).

cnf(c_2970,plain,
    ( u1_struct_0(sK2(sK3,X0)) = X0
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1126])).

cnf(c_3267,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v2_tex_2(sK4,sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2975,c_2970])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_41,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1534,plain,
    ( ~ v2_tex_2(X0,sK3)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(sK3,X0)) = X0
    | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_1126])).

cnf(c_1535,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | v1_xboole_0(sK4)
    | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
    inference(unflattening,[status(thm)],[c_1534])).

cnf(c_1536,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v2_tex_2(sK4,sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1535])).

cnf(c_3270,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3267,c_41,c_1536])).

cnf(c_3271,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v2_tex_2(sK4,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3270])).

cnf(c_3276,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2976,c_3271])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2993,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_10,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2983,plain,
    ( r1_tarski(k1_tarski(X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_23,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_14,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_208,plain,
    ( v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X1)
    | ~ r1_tarski(X0,X1)
    | X1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_14,c_12])).

cnf(c_209,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | X1 = X0 ),
    inference(renaming,[status(thm)],[c_208])).

cnf(c_2973,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_209])).

cnf(c_4712,plain,
    ( k1_tarski(X0) = X1
    | r2_hidden(X0,X1) != iProver_top
    | v1_zfmisc_1(X1) != iProver_top
    | v1_xboole_0(k1_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2983,c_2973])).

cnf(c_9,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_94,plain,
    ( v1_xboole_0(k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_9901,plain,
    ( v1_zfmisc_1(X1) != iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | k1_tarski(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4712,c_94])).

cnf(c_9902,plain,
    ( k1_tarski(X0) = X1
    | r2_hidden(X0,X1) != iProver_top
    | v1_zfmisc_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_9901])).

cnf(c_9910,plain,
    ( k1_tarski(sK0(X0)) = X0
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2993,c_9902])).

cnf(c_11852,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | k1_tarski(sK0(sK4)) = sK4
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3276,c_9910])).

cnf(c_11904,plain,
    ( v1_xboole_0(sK4)
    | u1_struct_0(sK2(sK3,sK4)) = sK4
    | k1_tarski(sK0(sK4)) = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11852])).

cnf(c_12038,plain,
    ( k1_tarski(sK0(sK4)) = sK4
    | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11852,c_32,c_11904])).

cnf(c_12039,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | k1_tarski(sK0(sK4)) = sK4 ),
    inference(renaming,[status(thm)],[c_12038])).

cnf(c_26,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v1_tdlat_3(sK2(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1097,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v1_tdlat_3(sK2(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_35])).

cnf(c_1098,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | v1_tdlat_3(sK2(sK3,X0))
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_1097])).

cnf(c_1102,plain,
    ( v1_tdlat_3(sK2(sK3,X0))
    | ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1098,c_36,c_33])).

cnf(c_1103,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tdlat_3(sK2(sK3,X0))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_1102])).

cnf(c_27,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK2(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1073,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK2(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_35])).

cnf(c_1074,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_struct_0(sK2(sK3,X0))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_1073])).

cnf(c_1078,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_struct_0(sK2(sK3,X0))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1074,c_36,c_33])).

cnf(c_25,plain,
    ( ~ v2_tex_2(X0,X1)
    | m1_pre_topc(sK2(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_16,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_18,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_493,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_16,c_18])).

cnf(c_511,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_21,c_493])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_515,plain,
    ( v1_zfmisc_1(u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_511,c_17])).

cnf(c_516,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_515])).

cnf(c_20,plain,
    ( ~ v2_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_535,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X1)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_516,c_20])).

cnf(c_34,negated_conjecture,
    ( v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_556,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_535,c_34])).

cnf(c_557,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ v1_tdlat_3(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_556])).

cnf(c_561,plain,
    ( v1_zfmisc_1(u1_struct_0(X0))
    | ~ v1_tdlat_3(X0)
    | ~ m1_pre_topc(X0,sK3)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_557,c_36,c_33])).

cnf(c_562,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(renaming,[status(thm)],[c_561])).

cnf(c_734,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X2)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK2(X1,X0) != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_562])).

cnf(c_735,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK2(sK3,X0))
    | v2_struct_0(sK3)
    | ~ v1_tdlat_3(sK2(sK3,X0))
    | ~ v2_pre_topc(sK3)
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_734])).

cnf(c_739,plain,
    ( v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
    | v2_struct_0(sK2(sK3,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_tex_2(X0,sK3)
    | ~ v1_tdlat_3(sK2(sK3,X0))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_735,c_36,c_35,c_33])).

cnf(c_740,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK2(sK3,X0))
    | ~ v1_tdlat_3(sK2(sK3,X0))
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_739])).

cnf(c_1156,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tdlat_3(sK2(sK3,X0))
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
    | v1_xboole_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1078,c_740])).

cnf(c_1165,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
    | v1_xboole_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1103,c_1156])).

cnf(c_2969,plain,
    ( v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0))) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1165])).

cnf(c_3283,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2975,c_2969])).

cnf(c_1520,plain,
    ( ~ v2_tex_2(X0,sK3)
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
    | v1_xboole_0(X0)
    | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_1165])).

cnf(c_1521,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1520])).

cnf(c_1523,plain,
    ( v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
    | ~ v2_tex_2(sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1521,c_32])).

cnf(c_1524,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) ),
    inference(renaming,[status(thm)],[c_1523])).

cnf(c_1525,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1524])).

cnf(c_3566,plain,
    ( v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top
    | v2_tex_2(sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3283,c_1525])).

cnf(c_3567,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3566])).

cnf(c_12043,plain,
    ( k1_tarski(sK0(sK4)) = sK4
    | v2_tex_2(sK4,sK3) != iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_12039,c_3567])).

cnf(c_293,plain,
    ( v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3) ),
    inference(prop_impl,[status(thm)],[c_30])).

cnf(c_294,plain,
    ( v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4) ),
    inference(renaming,[status(thm)],[c_293])).

cnf(c_1251,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
    | v1_zfmisc_1(sK4)
    | v1_xboole_0(X0)
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_294,c_1165])).

cnf(c_1252,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
    | v1_zfmisc_1(sK4)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1251])).

cnf(c_1254,plain,
    ( v1_zfmisc_1(sK4)
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1252,c_32,c_31])).

cnf(c_1255,plain,
    ( v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
    | v1_zfmisc_1(sK4) ),
    inference(renaming,[status(thm)],[c_1254])).

cnf(c_1256,plain,
    ( v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1255])).

cnf(c_1265,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_zfmisc_1(sK4)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(sK3,X0)) = X0
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_294,c_1126])).

cnf(c_1266,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_zfmisc_1(sK4)
    | v1_xboole_0(sK4)
    | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
    inference(unflattening,[status(thm)],[c_1265])).

cnf(c_1268,plain,
    ( v1_zfmisc_1(sK4)
    | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1266,c_32,c_31])).

cnf(c_1270,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1268])).

cnf(c_2332,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3354,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2332])).

cnf(c_2333,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3311,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_2333])).

cnf(c_3531,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3311])).

cnf(c_3814,plain,
    ( u1_struct_0(sK2(sK3,sK4)) != sK4
    | sK4 = u1_struct_0(sK2(sK3,sK4))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3531])).

cnf(c_2340,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_zfmisc_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3555,plain,
    ( v1_zfmisc_1(X0)
    | ~ v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
    | X0 != u1_struct_0(sK2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2340])).

cnf(c_5113,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
    | v1_zfmisc_1(sK4)
    | sK4 != u1_struct_0(sK2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3555])).

cnf(c_5114,plain,
    ( sK4 != u1_struct_0(sK2(sK3,sK4))
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) != iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5113])).

cnf(c_12156,plain,
    ( v1_zfmisc_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12043,c_1256,c_1270,c_3354,c_3814,c_5114])).

cnf(c_12161,plain,
    ( k1_tarski(sK0(sK4)) = sK4
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_12156,c_9910])).

cnf(c_12340,plain,
    ( k1_tarski(sK0(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12161,c_41])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2979,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3671,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2975,c_2979])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2985,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3772,plain,
    ( k3_xboole_0(sK4,u1_struct_0(sK3)) = sK4 ),
    inference(superposition,[status(thm)],[c_3671,c_2985])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2987,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4215,plain,
    ( r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3772,c_2987])).

cnf(c_13,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2981,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4407,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4215,c_2981])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2978,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4738,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0)
    | r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4407,c_2978])).

cnf(c_42,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3198,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3199,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3198])).

cnf(c_289,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_290,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_289])).

cnf(c_362,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_290])).

cnf(c_3206,plain,
    ( ~ r1_tarski(sK4,X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_362])).

cnf(c_3308,plain,
    ( ~ r1_tarski(sK4,u1_struct_0(sK3))
    | ~ v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3206])).

cnf(c_3309,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3308])).

cnf(c_5335,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4738,c_41,c_42,c_3199,c_3309])).

cnf(c_5336,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0)
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_5335])).

cnf(c_5343,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4))
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2993,c_5336])).

cnf(c_8931,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5343,c_41])).

cnf(c_28,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1031,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_35])).

cnf(c_1032,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1031])).

cnf(c_1036,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1032,c_36,c_33])).

cnf(c_2971,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1036])).

cnf(c_8934,plain,
    ( v2_tex_2(k1_tarski(sK0(sK4)),sK3) = iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8931,c_2971])).

cnf(c_9012,plain,
    ( v2_tex_2(k1_tarski(sK0(sK4)),sK3) = iProver_top
    | r2_hidden(sK0(sK4),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4407,c_8934])).

cnf(c_3191,plain,
    ( r2_hidden(sK0(sK4),sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3192,plain,
    ( r2_hidden(sK0(sK4),sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3191])).

cnf(c_9015,plain,
    ( v2_tex_2(k1_tarski(sK0(sK4)),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9012,c_41,c_3192])).

cnf(c_12350,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12340,c_9015])).

cnf(c_29,negated_conjecture,
    ( ~ v2_tex_2(sK4,sK3)
    | ~ v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_44,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v1_zfmisc_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12350,c_12156,c_44])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:55:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.69/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.00  
% 3.69/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.69/1.00  
% 3.69/1.00  ------  iProver source info
% 3.69/1.00  
% 3.69/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.69/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.69/1.00  git: non_committed_changes: false
% 3.69/1.00  git: last_make_outside_of_git: false
% 3.69/1.00  
% 3.69/1.00  ------ 
% 3.69/1.00  
% 3.69/1.00  ------ Input Options
% 3.69/1.00  
% 3.69/1.00  --out_options                           all
% 3.69/1.00  --tptp_safe_out                         true
% 3.69/1.00  --problem_path                          ""
% 3.69/1.00  --include_path                          ""
% 3.69/1.00  --clausifier                            res/vclausify_rel
% 3.69/1.00  --clausifier_options                    --mode clausify
% 3.69/1.00  --stdin                                 false
% 3.69/1.00  --stats_out                             all
% 3.69/1.00  
% 3.69/1.00  ------ General Options
% 3.69/1.00  
% 3.69/1.00  --fof                                   false
% 3.69/1.00  --time_out_real                         305.
% 3.69/1.00  --time_out_virtual                      -1.
% 3.69/1.00  --symbol_type_check                     false
% 3.69/1.00  --clausify_out                          false
% 3.69/1.00  --sig_cnt_out                           false
% 3.69/1.00  --trig_cnt_out                          false
% 3.69/1.00  --trig_cnt_out_tolerance                1.
% 3.69/1.00  --trig_cnt_out_sk_spl                   false
% 3.69/1.00  --abstr_cl_out                          false
% 3.69/1.00  
% 3.69/1.00  ------ Global Options
% 3.69/1.00  
% 3.69/1.00  --schedule                              default
% 3.69/1.00  --add_important_lit                     false
% 3.69/1.00  --prop_solver_per_cl                    1000
% 3.69/1.00  --min_unsat_core                        false
% 3.69/1.00  --soft_assumptions                      false
% 3.69/1.00  --soft_lemma_size                       3
% 3.69/1.00  --prop_impl_unit_size                   0
% 3.69/1.00  --prop_impl_unit                        []
% 3.69/1.00  --share_sel_clauses                     true
% 3.69/1.00  --reset_solvers                         false
% 3.69/1.00  --bc_imp_inh                            [conj_cone]
% 3.69/1.00  --conj_cone_tolerance                   3.
% 3.69/1.00  --extra_neg_conj                        none
% 3.69/1.00  --large_theory_mode                     true
% 3.69/1.00  --prolific_symb_bound                   200
% 3.69/1.00  --lt_threshold                          2000
% 3.69/1.00  --clause_weak_htbl                      true
% 3.69/1.00  --gc_record_bc_elim                     false
% 3.69/1.00  
% 3.69/1.00  ------ Preprocessing Options
% 3.69/1.00  
% 3.69/1.00  --preprocessing_flag                    true
% 3.69/1.00  --time_out_prep_mult                    0.1
% 3.69/1.00  --splitting_mode                        input
% 3.69/1.00  --splitting_grd                         true
% 3.69/1.00  --splitting_cvd                         false
% 3.69/1.00  --splitting_cvd_svl                     false
% 3.69/1.00  --splitting_nvd                         32
% 3.69/1.00  --sub_typing                            true
% 3.69/1.00  --prep_gs_sim                           true
% 3.69/1.00  --prep_unflatten                        true
% 3.69/1.00  --prep_res_sim                          true
% 3.69/1.00  --prep_upred                            true
% 3.69/1.00  --prep_sem_filter                       exhaustive
% 3.69/1.00  --prep_sem_filter_out                   false
% 3.69/1.00  --pred_elim                             true
% 3.69/1.00  --res_sim_input                         true
% 3.69/1.00  --eq_ax_congr_red                       true
% 3.69/1.00  --pure_diseq_elim                       true
% 3.69/1.00  --brand_transform                       false
% 3.69/1.00  --non_eq_to_eq                          false
% 3.69/1.00  --prep_def_merge                        true
% 3.69/1.00  --prep_def_merge_prop_impl              false
% 3.69/1.00  --prep_def_merge_mbd                    true
% 3.69/1.00  --prep_def_merge_tr_red                 false
% 3.69/1.00  --prep_def_merge_tr_cl                  false
% 3.69/1.00  --smt_preprocessing                     true
% 3.69/1.00  --smt_ac_axioms                         fast
% 3.69/1.00  --preprocessed_out                      false
% 3.69/1.00  --preprocessed_stats                    false
% 3.69/1.00  
% 3.69/1.00  ------ Abstraction refinement Options
% 3.69/1.00  
% 3.69/1.00  --abstr_ref                             []
% 3.69/1.00  --abstr_ref_prep                        false
% 3.69/1.00  --abstr_ref_until_sat                   false
% 3.69/1.00  --abstr_ref_sig_restrict                funpre
% 3.69/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.69/1.00  --abstr_ref_under                       []
% 3.69/1.00  
% 3.69/1.00  ------ SAT Options
% 3.69/1.00  
% 3.69/1.00  --sat_mode                              false
% 3.69/1.00  --sat_fm_restart_options                ""
% 3.69/1.00  --sat_gr_def                            false
% 3.69/1.00  --sat_epr_types                         true
% 3.69/1.00  --sat_non_cyclic_types                  false
% 3.69/1.00  --sat_finite_models                     false
% 3.69/1.00  --sat_fm_lemmas                         false
% 3.69/1.00  --sat_fm_prep                           false
% 3.69/1.00  --sat_fm_uc_incr                        true
% 3.69/1.00  --sat_out_model                         small
% 3.69/1.00  --sat_out_clauses                       false
% 3.69/1.00  
% 3.69/1.00  ------ QBF Options
% 3.69/1.00  
% 3.69/1.00  --qbf_mode                              false
% 3.69/1.00  --qbf_elim_univ                         false
% 3.69/1.00  --qbf_dom_inst                          none
% 3.69/1.00  --qbf_dom_pre_inst                      false
% 3.69/1.00  --qbf_sk_in                             false
% 3.69/1.00  --qbf_pred_elim                         true
% 3.69/1.00  --qbf_split                             512
% 3.69/1.00  
% 3.69/1.00  ------ BMC1 Options
% 3.69/1.00  
% 3.69/1.00  --bmc1_incremental                      false
% 3.69/1.00  --bmc1_axioms                           reachable_all
% 3.69/1.00  --bmc1_min_bound                        0
% 3.69/1.00  --bmc1_max_bound                        -1
% 3.69/1.00  --bmc1_max_bound_default                -1
% 3.69/1.00  --bmc1_symbol_reachability              true
% 3.69/1.00  --bmc1_property_lemmas                  false
% 3.69/1.00  --bmc1_k_induction                      false
% 3.69/1.00  --bmc1_non_equiv_states                 false
% 3.69/1.00  --bmc1_deadlock                         false
% 3.69/1.00  --bmc1_ucm                              false
% 3.69/1.00  --bmc1_add_unsat_core                   none
% 3.69/1.00  --bmc1_unsat_core_children              false
% 3.69/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.69/1.00  --bmc1_out_stat                         full
% 3.69/1.00  --bmc1_ground_init                      false
% 3.69/1.00  --bmc1_pre_inst_next_state              false
% 3.69/1.00  --bmc1_pre_inst_state                   false
% 3.69/1.00  --bmc1_pre_inst_reach_state             false
% 3.69/1.00  --bmc1_out_unsat_core                   false
% 3.69/1.00  --bmc1_aig_witness_out                  false
% 3.69/1.00  --bmc1_verbose                          false
% 3.69/1.00  --bmc1_dump_clauses_tptp                false
% 3.69/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.69/1.00  --bmc1_dump_file                        -
% 3.69/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.69/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.69/1.00  --bmc1_ucm_extend_mode                  1
% 3.69/1.00  --bmc1_ucm_init_mode                    2
% 3.69/1.00  --bmc1_ucm_cone_mode                    none
% 3.69/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.69/1.00  --bmc1_ucm_relax_model                  4
% 3.69/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.69/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.69/1.00  --bmc1_ucm_layered_model                none
% 3.69/1.00  --bmc1_ucm_max_lemma_size               10
% 3.69/1.00  
% 3.69/1.00  ------ AIG Options
% 3.69/1.00  
% 3.69/1.00  --aig_mode                              false
% 3.69/1.00  
% 3.69/1.00  ------ Instantiation Options
% 3.69/1.00  
% 3.69/1.00  --instantiation_flag                    true
% 3.69/1.00  --inst_sos_flag                         false
% 3.69/1.00  --inst_sos_phase                        true
% 3.69/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.69/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.69/1.00  --inst_lit_sel_side                     num_symb
% 3.69/1.00  --inst_solver_per_active                1400
% 3.69/1.00  --inst_solver_calls_frac                1.
% 3.69/1.00  --inst_passive_queue_type               priority_queues
% 3.69/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.69/1.00  --inst_passive_queues_freq              [25;2]
% 3.69/1.00  --inst_dismatching                      true
% 3.69/1.00  --inst_eager_unprocessed_to_passive     true
% 3.69/1.00  --inst_prop_sim_given                   true
% 3.69/1.00  --inst_prop_sim_new                     false
% 3.69/1.00  --inst_subs_new                         false
% 3.69/1.00  --inst_eq_res_simp                      false
% 3.69/1.00  --inst_subs_given                       false
% 3.69/1.00  --inst_orphan_elimination               true
% 3.69/1.00  --inst_learning_loop_flag               true
% 3.69/1.00  --inst_learning_start                   3000
% 3.69/1.00  --inst_learning_factor                  2
% 3.69/1.00  --inst_start_prop_sim_after_learn       3
% 3.69/1.00  --inst_sel_renew                        solver
% 3.69/1.00  --inst_lit_activity_flag                true
% 3.69/1.00  --inst_restr_to_given                   false
% 3.69/1.00  --inst_activity_threshold               500
% 3.69/1.00  --inst_out_proof                        true
% 3.69/1.00  
% 3.69/1.00  ------ Resolution Options
% 3.69/1.00  
% 3.69/1.00  --resolution_flag                       true
% 3.69/1.00  --res_lit_sel                           adaptive
% 3.69/1.00  --res_lit_sel_side                      none
% 3.69/1.00  --res_ordering                          kbo
% 3.69/1.00  --res_to_prop_solver                    active
% 3.69/1.00  --res_prop_simpl_new                    false
% 3.69/1.00  --res_prop_simpl_given                  true
% 3.69/1.00  --res_passive_queue_type                priority_queues
% 3.69/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.69/1.00  --res_passive_queues_freq               [15;5]
% 3.69/1.00  --res_forward_subs                      full
% 3.69/1.00  --res_backward_subs                     full
% 3.69/1.00  --res_forward_subs_resolution           true
% 3.69/1.00  --res_backward_subs_resolution          true
% 3.69/1.00  --res_orphan_elimination                true
% 3.69/1.00  --res_time_limit                        2.
% 3.69/1.00  --res_out_proof                         true
% 3.69/1.00  
% 3.69/1.00  ------ Superposition Options
% 3.69/1.00  
% 3.69/1.00  --superposition_flag                    true
% 3.69/1.00  --sup_passive_queue_type                priority_queues
% 3.69/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.69/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.69/1.00  --demod_completeness_check              fast
% 3.69/1.00  --demod_use_ground                      true
% 3.69/1.00  --sup_to_prop_solver                    passive
% 3.69/1.00  --sup_prop_simpl_new                    true
% 3.69/1.00  --sup_prop_simpl_given                  true
% 3.69/1.00  --sup_fun_splitting                     false
% 3.69/1.00  --sup_smt_interval                      50000
% 3.69/1.00  
% 3.69/1.00  ------ Superposition Simplification Setup
% 3.69/1.00  
% 3.69/1.00  --sup_indices_passive                   []
% 3.69/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.69/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.69/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.69/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.69/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.69/1.00  --sup_full_bw                           [BwDemod]
% 3.69/1.00  --sup_immed_triv                        [TrivRules]
% 3.69/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.69/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.69/1.00  --sup_immed_bw_main                     []
% 3.69/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.69/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.69/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.69/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.69/1.00  
% 3.69/1.00  ------ Combination Options
% 3.69/1.00  
% 3.69/1.00  --comb_res_mult                         3
% 3.69/1.00  --comb_sup_mult                         2
% 3.69/1.00  --comb_inst_mult                        10
% 3.69/1.00  
% 3.69/1.00  ------ Debug Options
% 3.69/1.00  
% 3.69/1.00  --dbg_backtrace                         false
% 3.69/1.00  --dbg_dump_prop_clauses                 false
% 3.69/1.00  --dbg_dump_prop_clauses_file            -
% 3.69/1.00  --dbg_out_stat                          false
% 3.69/1.00  ------ Parsing...
% 3.69/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.69/1.00  
% 3.69/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.69/1.00  
% 3.69/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.69/1.00  
% 3.69/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.69/1.00  ------ Proving...
% 3.69/1.00  ------ Problem Properties 
% 3.69/1.00  
% 3.69/1.00  
% 3.69/1.00  clauses                                 25
% 3.69/1.00  conjectures                             4
% 3.69/1.00  EPR                                     7
% 3.69/1.00  Horn                                    17
% 3.69/1.00  unary                                   3
% 3.69/1.00  binary                                  13
% 3.69/1.00  lits                                    60
% 3.69/1.00  lits eq                                 7
% 3.69/1.00  fd_pure                                 0
% 3.69/1.00  fd_pseudo                               0
% 3.69/1.00  fd_cond                                 0
% 3.69/1.00  fd_pseudo_cond                          4
% 3.69/1.00  AC symbols                              0
% 3.69/1.00  
% 3.69/1.00  ------ Schedule dynamic 5 is on 
% 3.69/1.00  
% 3.69/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.69/1.00  
% 3.69/1.00  
% 3.69/1.00  ------ 
% 3.69/1.00  Current options:
% 3.69/1.00  ------ 
% 3.69/1.00  
% 3.69/1.00  ------ Input Options
% 3.69/1.00  
% 3.69/1.00  --out_options                           all
% 3.69/1.00  --tptp_safe_out                         true
% 3.69/1.00  --problem_path                          ""
% 3.69/1.00  --include_path                          ""
% 3.69/1.00  --clausifier                            res/vclausify_rel
% 3.69/1.00  --clausifier_options                    --mode clausify
% 3.69/1.00  --stdin                                 false
% 3.69/1.00  --stats_out                             all
% 3.69/1.00  
% 3.69/1.00  ------ General Options
% 3.69/1.00  
% 3.69/1.00  --fof                                   false
% 3.69/1.00  --time_out_real                         305.
% 3.69/1.00  --time_out_virtual                      -1.
% 3.69/1.00  --symbol_type_check                     false
% 3.69/1.00  --clausify_out                          false
% 3.69/1.00  --sig_cnt_out                           false
% 3.69/1.00  --trig_cnt_out                          false
% 3.69/1.00  --trig_cnt_out_tolerance                1.
% 3.69/1.00  --trig_cnt_out_sk_spl                   false
% 3.69/1.00  --abstr_cl_out                          false
% 3.69/1.00  
% 3.69/1.00  ------ Global Options
% 3.69/1.00  
% 3.69/1.00  --schedule                              default
% 3.69/1.00  --add_important_lit                     false
% 3.69/1.00  --prop_solver_per_cl                    1000
% 3.69/1.00  --min_unsat_core                        false
% 3.69/1.00  --soft_assumptions                      false
% 3.69/1.00  --soft_lemma_size                       3
% 3.69/1.00  --prop_impl_unit_size                   0
% 3.69/1.00  --prop_impl_unit                        []
% 3.69/1.00  --share_sel_clauses                     true
% 3.69/1.00  --reset_solvers                         false
% 3.69/1.00  --bc_imp_inh                            [conj_cone]
% 3.69/1.00  --conj_cone_tolerance                   3.
% 3.69/1.00  --extra_neg_conj                        none
% 3.69/1.00  --large_theory_mode                     true
% 3.69/1.00  --prolific_symb_bound                   200
% 3.69/1.00  --lt_threshold                          2000
% 3.69/1.00  --clause_weak_htbl                      true
% 3.69/1.00  --gc_record_bc_elim                     false
% 3.69/1.00  
% 3.69/1.00  ------ Preprocessing Options
% 3.69/1.00  
% 3.69/1.00  --preprocessing_flag                    true
% 3.69/1.00  --time_out_prep_mult                    0.1
% 3.69/1.00  --splitting_mode                        input
% 3.69/1.00  --splitting_grd                         true
% 3.69/1.00  --splitting_cvd                         false
% 3.69/1.00  --splitting_cvd_svl                     false
% 3.69/1.00  --splitting_nvd                         32
% 3.69/1.00  --sub_typing                            true
% 3.69/1.00  --prep_gs_sim                           true
% 3.69/1.00  --prep_unflatten                        true
% 3.69/1.00  --prep_res_sim                          true
% 3.69/1.00  --prep_upred                            true
% 3.69/1.00  --prep_sem_filter                       exhaustive
% 3.69/1.00  --prep_sem_filter_out                   false
% 3.69/1.00  --pred_elim                             true
% 3.69/1.00  --res_sim_input                         true
% 3.69/1.00  --eq_ax_congr_red                       true
% 3.69/1.00  --pure_diseq_elim                       true
% 3.69/1.00  --brand_transform                       false
% 3.69/1.00  --non_eq_to_eq                          false
% 3.69/1.00  --prep_def_merge                        true
% 3.69/1.00  --prep_def_merge_prop_impl              false
% 3.69/1.00  --prep_def_merge_mbd                    true
% 3.69/1.00  --prep_def_merge_tr_red                 false
% 3.69/1.00  --prep_def_merge_tr_cl                  false
% 3.69/1.00  --smt_preprocessing                     true
% 3.69/1.00  --smt_ac_axioms                         fast
% 3.69/1.00  --preprocessed_out                      false
% 3.69/1.00  --preprocessed_stats                    false
% 3.69/1.00  
% 3.69/1.00  ------ Abstraction refinement Options
% 3.69/1.00  
% 3.69/1.00  --abstr_ref                             []
% 3.69/1.00  --abstr_ref_prep                        false
% 3.69/1.00  --abstr_ref_until_sat                   false
% 3.69/1.00  --abstr_ref_sig_restrict                funpre
% 3.69/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.69/1.00  --abstr_ref_under                       []
% 3.69/1.00  
% 3.69/1.00  ------ SAT Options
% 3.69/1.00  
% 3.69/1.00  --sat_mode                              false
% 3.69/1.00  --sat_fm_restart_options                ""
% 3.69/1.00  --sat_gr_def                            false
% 3.69/1.00  --sat_epr_types                         true
% 3.69/1.00  --sat_non_cyclic_types                  false
% 3.69/1.00  --sat_finite_models                     false
% 3.69/1.00  --sat_fm_lemmas                         false
% 3.69/1.00  --sat_fm_prep                           false
% 3.69/1.00  --sat_fm_uc_incr                        true
% 3.69/1.00  --sat_out_model                         small
% 3.69/1.00  --sat_out_clauses                       false
% 3.69/1.00  
% 3.69/1.00  ------ QBF Options
% 3.69/1.00  
% 3.69/1.00  --qbf_mode                              false
% 3.69/1.00  --qbf_elim_univ                         false
% 3.69/1.00  --qbf_dom_inst                          none
% 3.69/1.00  --qbf_dom_pre_inst                      false
% 3.69/1.00  --qbf_sk_in                             false
% 3.69/1.00  --qbf_pred_elim                         true
% 3.69/1.00  --qbf_split                             512
% 3.69/1.00  
% 3.69/1.00  ------ BMC1 Options
% 3.69/1.00  
% 3.69/1.00  --bmc1_incremental                      false
% 3.69/1.00  --bmc1_axioms                           reachable_all
% 3.69/1.00  --bmc1_min_bound                        0
% 3.69/1.00  --bmc1_max_bound                        -1
% 3.69/1.00  --bmc1_max_bound_default                -1
% 3.69/1.00  --bmc1_symbol_reachability              true
% 3.69/1.00  --bmc1_property_lemmas                  false
% 3.69/1.00  --bmc1_k_induction                      false
% 3.69/1.00  --bmc1_non_equiv_states                 false
% 3.69/1.00  --bmc1_deadlock                         false
% 3.69/1.00  --bmc1_ucm                              false
% 3.69/1.00  --bmc1_add_unsat_core                   none
% 3.69/1.00  --bmc1_unsat_core_children              false
% 3.69/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.69/1.00  --bmc1_out_stat                         full
% 3.69/1.00  --bmc1_ground_init                      false
% 3.69/1.00  --bmc1_pre_inst_next_state              false
% 3.69/1.00  --bmc1_pre_inst_state                   false
% 3.69/1.00  --bmc1_pre_inst_reach_state             false
% 3.69/1.00  --bmc1_out_unsat_core                   false
% 3.69/1.00  --bmc1_aig_witness_out                  false
% 3.69/1.00  --bmc1_verbose                          false
% 3.69/1.00  --bmc1_dump_clauses_tptp                false
% 3.69/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.69/1.00  --bmc1_dump_file                        -
% 3.69/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.69/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.69/1.00  --bmc1_ucm_extend_mode                  1
% 3.69/1.00  --bmc1_ucm_init_mode                    2
% 3.69/1.00  --bmc1_ucm_cone_mode                    none
% 3.69/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.69/1.00  --bmc1_ucm_relax_model                  4
% 3.69/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.69/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.69/1.00  --bmc1_ucm_layered_model                none
% 3.69/1.00  --bmc1_ucm_max_lemma_size               10
% 3.69/1.00  
% 3.69/1.00  ------ AIG Options
% 3.69/1.00  
% 3.69/1.00  --aig_mode                              false
% 3.69/1.00  
% 3.69/1.00  ------ Instantiation Options
% 3.69/1.00  
% 3.69/1.00  --instantiation_flag                    true
% 3.69/1.00  --inst_sos_flag                         false
% 3.69/1.00  --inst_sos_phase                        true
% 3.69/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.69/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.69/1.00  --inst_lit_sel_side                     none
% 3.69/1.00  --inst_solver_per_active                1400
% 3.69/1.00  --inst_solver_calls_frac                1.
% 3.69/1.00  --inst_passive_queue_type               priority_queues
% 3.69/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.69/1.00  --inst_passive_queues_freq              [25;2]
% 3.69/1.00  --inst_dismatching                      true
% 3.69/1.00  --inst_eager_unprocessed_to_passive     true
% 3.69/1.00  --inst_prop_sim_given                   true
% 3.69/1.00  --inst_prop_sim_new                     false
% 3.69/1.00  --inst_subs_new                         false
% 3.69/1.00  --inst_eq_res_simp                      false
% 3.69/1.00  --inst_subs_given                       false
% 3.69/1.00  --inst_orphan_elimination               true
% 3.69/1.00  --inst_learning_loop_flag               true
% 3.69/1.00  --inst_learning_start                   3000
% 3.69/1.00  --inst_learning_factor                  2
% 3.69/1.00  --inst_start_prop_sim_after_learn       3
% 3.69/1.00  --inst_sel_renew                        solver
% 3.69/1.00  --inst_lit_activity_flag                true
% 3.69/1.00  --inst_restr_to_given                   false
% 3.69/1.00  --inst_activity_threshold               500
% 3.69/1.00  --inst_out_proof                        true
% 3.69/1.00  
% 3.69/1.00  ------ Resolution Options
% 3.69/1.00  
% 3.69/1.00  --resolution_flag                       false
% 3.69/1.00  --res_lit_sel                           adaptive
% 3.69/1.00  --res_lit_sel_side                      none
% 3.69/1.00  --res_ordering                          kbo
% 3.69/1.00  --res_to_prop_solver                    active
% 3.69/1.00  --res_prop_simpl_new                    false
% 3.69/1.00  --res_prop_simpl_given                  true
% 3.69/1.00  --res_passive_queue_type                priority_queues
% 3.69/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.69/1.00  --res_passive_queues_freq               [15;5]
% 3.69/1.00  --res_forward_subs                      full
% 3.69/1.00  --res_backward_subs                     full
% 3.69/1.00  --res_forward_subs_resolution           true
% 3.69/1.00  --res_backward_subs_resolution          true
% 3.69/1.00  --res_orphan_elimination                true
% 3.69/1.00  --res_time_limit                        2.
% 3.69/1.00  --res_out_proof                         true
% 3.69/1.00  
% 3.69/1.00  ------ Superposition Options
% 3.69/1.00  
% 3.69/1.00  --superposition_flag                    true
% 3.69/1.00  --sup_passive_queue_type                priority_queues
% 3.69/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.69/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.69/1.00  --demod_completeness_check              fast
% 3.69/1.00  --demod_use_ground                      true
% 3.69/1.00  --sup_to_prop_solver                    passive
% 3.69/1.00  --sup_prop_simpl_new                    true
% 3.69/1.00  --sup_prop_simpl_given                  true
% 3.69/1.00  --sup_fun_splitting                     false
% 3.69/1.00  --sup_smt_interval                      50000
% 3.69/1.00  
% 3.69/1.00  ------ Superposition Simplification Setup
% 3.69/1.00  
% 3.69/1.00  --sup_indices_passive                   []
% 3.69/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.69/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.69/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.69/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.69/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.69/1.00  --sup_full_bw                           [BwDemod]
% 3.69/1.00  --sup_immed_triv                        [TrivRules]
% 3.69/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.69/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.69/1.00  --sup_immed_bw_main                     []
% 3.69/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.69/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.69/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.69/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.69/1.00  
% 3.69/1.00  ------ Combination Options
% 3.69/1.00  
% 3.69/1.00  --comb_res_mult                         3
% 3.69/1.00  --comb_sup_mult                         2
% 3.69/1.00  --comb_inst_mult                        10
% 3.69/1.00  
% 3.69/1.00  ------ Debug Options
% 3.69/1.00  
% 3.69/1.00  --dbg_backtrace                         false
% 3.69/1.00  --dbg_dump_prop_clauses                 false
% 3.69/1.00  --dbg_dump_prop_clauses_file            -
% 3.69/1.00  --dbg_out_stat                          false
% 3.69/1.00  
% 3.69/1.00  
% 3.69/1.00  
% 3.69/1.00  
% 3.69/1.00  ------ Proving...
% 3.69/1.00  
% 3.69/1.00  
% 3.69/1.00  % SZS status Theorem for theBenchmark.p
% 3.69/1.00  
% 3.69/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.69/1.00  
% 3.69/1.00  fof(f18,conjecture,(
% 3.69/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f19,negated_conjecture,(
% 3.69/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.69/1.00    inference(negated_conjecture,[],[f18])).
% 3.69/1.00  
% 3.69/1.00  fof(f40,plain,(
% 3.69/1.00    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.69/1.00    inference(ennf_transformation,[],[f19])).
% 3.69/1.00  
% 3.69/1.00  fof(f41,plain,(
% 3.69/1.00    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.69/1.00    inference(flattening,[],[f40])).
% 3.69/1.00  
% 3.69/1.00  fof(f55,plain,(
% 3.69/1.00    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.69/1.00    inference(nnf_transformation,[],[f41])).
% 3.69/1.00  
% 3.69/1.00  fof(f56,plain,(
% 3.69/1.00    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.69/1.00    inference(flattening,[],[f55])).
% 3.69/1.00  
% 3.69/1.00  fof(f58,plain,(
% 3.69/1.00    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,X0)) & (v1_zfmisc_1(sK4) | v2_tex_2(sK4,X0)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK4))) )),
% 3.69/1.00    introduced(choice_axiom,[])).
% 3.69/1.00  
% 3.69/1.00  fof(f57,plain,(
% 3.69/1.00    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK3)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 3.69/1.00    introduced(choice_axiom,[])).
% 3.69/1.00  
% 3.69/1.00  fof(f59,plain,(
% 3.69/1.00    ((~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)) & (v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 3.69/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f56,f58,f57])).
% 3.69/1.00  
% 3.69/1.00  fof(f95,plain,(
% 3.69/1.00    v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)),
% 3.69/1.00    inference(cnf_transformation,[],[f59])).
% 3.69/1.00  
% 3.69/1.00  fof(f94,plain,(
% 3.69/1.00    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 3.69/1.00    inference(cnf_transformation,[],[f59])).
% 3.69/1.00  
% 3.69/1.00  fof(f16,axiom,(
% 3.69/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 3.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f20,plain,(
% 3.69/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 3.69/1.00    inference(pure_predicate_removal,[],[f16])).
% 3.69/1.00  
% 3.69/1.00  fof(f36,plain,(
% 3.69/1.00    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.69/1.00    inference(ennf_transformation,[],[f20])).
% 3.69/1.00  
% 3.69/1.00  fof(f37,plain,(
% 3.69/1.00    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.69/1.00    inference(flattening,[],[f36])).
% 3.69/1.00  
% 3.69/1.00  fof(f53,plain,(
% 3.69/1.00    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))))),
% 3.69/1.00    introduced(choice_axiom,[])).
% 3.69/1.00  
% 3.69/1.00  fof(f54,plain,(
% 3.69/1.00    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.69/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f53])).
% 3.69/1.00  
% 3.69/1.00  fof(f87,plain,(
% 3.69/1.00    ( ! [X0,X1] : (u1_struct_0(sK2(X0,X1)) = X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f54])).
% 3.69/1.00  
% 3.69/1.00  fof(f90,plain,(
% 3.69/1.00    v2_pre_topc(sK3)),
% 3.69/1.00    inference(cnf_transformation,[],[f59])).
% 3.69/1.00  
% 3.69/1.00  fof(f89,plain,(
% 3.69/1.00    ~v2_struct_0(sK3)),
% 3.69/1.00    inference(cnf_transformation,[],[f59])).
% 3.69/1.00  
% 3.69/1.00  fof(f92,plain,(
% 3.69/1.00    l1_pre_topc(sK3)),
% 3.69/1.00    inference(cnf_transformation,[],[f59])).
% 3.69/1.00  
% 3.69/1.00  fof(f93,plain,(
% 3.69/1.00    ~v1_xboole_0(sK4)),
% 3.69/1.00    inference(cnf_transformation,[],[f59])).
% 3.69/1.00  
% 3.69/1.00  fof(f1,axiom,(
% 3.69/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f42,plain,(
% 3.69/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.69/1.00    inference(nnf_transformation,[],[f1])).
% 3.69/1.00  
% 3.69/1.00  fof(f43,plain,(
% 3.69/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.69/1.00    inference(rectify,[],[f42])).
% 3.69/1.00  
% 3.69/1.00  fof(f44,plain,(
% 3.69/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.69/1.00    introduced(choice_axiom,[])).
% 3.69/1.00  
% 3.69/1.00  fof(f45,plain,(
% 3.69/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.69/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 3.69/1.00  
% 3.69/1.00  fof(f61,plain,(
% 3.69/1.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f45])).
% 3.69/1.00  
% 3.69/1.00  fof(f5,axiom,(
% 3.69/1.00    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f51,plain,(
% 3.69/1.00    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 3.69/1.00    inference(nnf_transformation,[],[f5])).
% 3.69/1.00  
% 3.69/1.00  fof(f71,plain,(
% 3.69/1.00    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f51])).
% 3.69/1.00  
% 3.69/1.00  fof(f15,axiom,(
% 3.69/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 3.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f34,plain,(
% 3.69/1.00    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 3.69/1.00    inference(ennf_transformation,[],[f15])).
% 3.69/1.00  
% 3.69/1.00  fof(f35,plain,(
% 3.69/1.00    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.69/1.00    inference(flattening,[],[f34])).
% 3.69/1.00  
% 3.69/1.00  fof(f83,plain,(
% 3.69/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f35])).
% 3.69/1.00  
% 3.69/1.00  fof(f8,axiom,(
% 3.69/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f52,plain,(
% 3.69/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.69/1.00    inference(nnf_transformation,[],[f8])).
% 3.69/1.00  
% 3.69/1.00  fof(f75,plain,(
% 3.69/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f52])).
% 3.69/1.00  
% 3.69/1.00  fof(f6,axiom,(
% 3.69/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f22,plain,(
% 3.69/1.00    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.69/1.00    inference(ennf_transformation,[],[f6])).
% 3.69/1.00  
% 3.69/1.00  fof(f72,plain,(
% 3.69/1.00    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f22])).
% 3.69/1.00  
% 3.69/1.00  fof(f4,axiom,(
% 3.69/1.00    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 3.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f69,plain,(
% 3.69/1.00    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 3.69/1.00    inference(cnf_transformation,[],[f4])).
% 3.69/1.00  
% 3.69/1.00  fof(f85,plain,(
% 3.69/1.00    ( ! [X0,X1] : (v1_tdlat_3(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f54])).
% 3.69/1.00  
% 3.69/1.00  fof(f84,plain,(
% 3.69/1.00    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f54])).
% 3.69/1.00  
% 3.69/1.00  fof(f86,plain,(
% 3.69/1.00    ( ! [X0,X1] : (m1_pre_topc(sK2(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f54])).
% 3.69/1.00  
% 3.69/1.00  fof(f14,axiom,(
% 3.69/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((~v7_struct_0(X1) & ~v2_struct_0(X1)) => (~v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 3.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f32,plain,(
% 3.69/1.00    ! [X0] : (! [X1] : (((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.69/1.00    inference(ennf_transformation,[],[f14])).
% 3.69/1.00  
% 3.69/1.00  fof(f33,plain,(
% 3.69/1.00    ! [X0] : (! [X1] : ((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.69/1.00    inference(flattening,[],[f32])).
% 3.69/1.00  
% 3.69/1.00  fof(f82,plain,(
% 3.69/1.00    ( ! [X0,X1] : (~v1_tdlat_3(X1) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f33])).
% 3.69/1.00  
% 3.69/1.00  fof(f9,axiom,(
% 3.69/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f24,plain,(
% 3.69/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.69/1.00    inference(ennf_transformation,[],[f9])).
% 3.69/1.00  
% 3.69/1.00  fof(f76,plain,(
% 3.69/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f24])).
% 3.69/1.00  
% 3.69/1.00  fof(f11,axiom,(
% 3.69/1.00    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 3.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f26,plain,(
% 3.69/1.00    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 3.69/1.00    inference(ennf_transformation,[],[f11])).
% 3.69/1.00  
% 3.69/1.00  fof(f27,plain,(
% 3.69/1.00    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 3.69/1.00    inference(flattening,[],[f26])).
% 3.69/1.00  
% 3.69/1.00  fof(f78,plain,(
% 3.69/1.00    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f27])).
% 3.69/1.00  
% 3.69/1.00  fof(f10,axiom,(
% 3.69/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f25,plain,(
% 3.69/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.69/1.00    inference(ennf_transformation,[],[f10])).
% 3.69/1.00  
% 3.69/1.00  fof(f77,plain,(
% 3.69/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f25])).
% 3.69/1.00  
% 3.69/1.00  fof(f13,axiom,(
% 3.69/1.00    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 3.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f30,plain,(
% 3.69/1.00    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 3.69/1.00    inference(ennf_transformation,[],[f13])).
% 3.69/1.00  
% 3.69/1.00  fof(f31,plain,(
% 3.69/1.00    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 3.69/1.00    inference(flattening,[],[f30])).
% 3.69/1.00  
% 3.69/1.00  fof(f80,plain,(
% 3.69/1.00    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f31])).
% 3.69/1.00  
% 3.69/1.00  fof(f91,plain,(
% 3.69/1.00    v2_tdlat_3(sK3)),
% 3.69/1.00    inference(cnf_transformation,[],[f59])).
% 3.69/1.00  
% 3.69/1.00  fof(f74,plain,(
% 3.69/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.69/1.00    inference(cnf_transformation,[],[f52])).
% 3.69/1.00  
% 3.69/1.00  fof(f3,axiom,(
% 3.69/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f21,plain,(
% 3.69/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.69/1.00    inference(ennf_transformation,[],[f3])).
% 3.69/1.00  
% 3.69/1.00  fof(f68,plain,(
% 3.69/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f21])).
% 3.69/1.00  
% 3.69/1.00  fof(f2,axiom,(
% 3.69/1.00    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f46,plain,(
% 3.69/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.69/1.00    inference(nnf_transformation,[],[f2])).
% 3.69/1.00  
% 3.69/1.00  fof(f47,plain,(
% 3.69/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.69/1.00    inference(flattening,[],[f46])).
% 3.69/1.00  
% 3.69/1.00  fof(f48,plain,(
% 3.69/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.69/1.00    inference(rectify,[],[f47])).
% 3.69/1.00  
% 3.69/1.00  fof(f49,plain,(
% 3.69/1.00    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.69/1.00    introduced(choice_axiom,[])).
% 3.69/1.00  
% 3.69/1.00  fof(f50,plain,(
% 3.69/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.69/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f48,f49])).
% 3.69/1.00  
% 3.69/1.00  fof(f63,plain,(
% 3.69/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.69/1.00    inference(cnf_transformation,[],[f50])).
% 3.69/1.00  
% 3.69/1.00  fof(f98,plain,(
% 3.69/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 3.69/1.00    inference(equality_resolution,[],[f63])).
% 3.69/1.00  
% 3.69/1.00  fof(f7,axiom,(
% 3.69/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f23,plain,(
% 3.69/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.69/1.00    inference(ennf_transformation,[],[f7])).
% 3.69/1.00  
% 3.69/1.00  fof(f73,plain,(
% 3.69/1.00    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f23])).
% 3.69/1.00  
% 3.69/1.00  fof(f12,axiom,(
% 3.69/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f28,plain,(
% 3.69/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.69/1.00    inference(ennf_transformation,[],[f12])).
% 3.69/1.00  
% 3.69/1.00  fof(f29,plain,(
% 3.69/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.69/1.00    inference(flattening,[],[f28])).
% 3.69/1.00  
% 3.69/1.00  fof(f79,plain,(
% 3.69/1.00    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f29])).
% 3.69/1.00  
% 3.69/1.00  fof(f17,axiom,(
% 3.69/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 3.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f38,plain,(
% 3.69/1.00    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.69/1.00    inference(ennf_transformation,[],[f17])).
% 3.69/1.00  
% 3.69/1.00  fof(f39,plain,(
% 3.69/1.00    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.69/1.00    inference(flattening,[],[f38])).
% 3.69/1.00  
% 3.69/1.00  fof(f88,plain,(
% 3.69/1.00    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f39])).
% 3.69/1.00  
% 3.69/1.00  fof(f96,plain,(
% 3.69/1.00    ~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)),
% 3.69/1.00    inference(cnf_transformation,[],[f59])).
% 3.69/1.00  
% 3.69/1.00  cnf(c_30,negated_conjecture,
% 3.69/1.00      ( v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) ),
% 3.69/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2976,plain,
% 3.69/1.00      ( v2_tex_2(sK4,sK3) = iProver_top
% 3.69/1.00      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_31,negated_conjecture,
% 3.69/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.69/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2975,plain,
% 3.69/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_24,plain,
% 3.69/1.00      ( ~ v2_tex_2(X0,X1)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | v2_struct_0(X1)
% 3.69/1.00      | ~ v2_pre_topc(X1)
% 3.69/1.00      | ~ l1_pre_topc(X1)
% 3.69/1.00      | v1_xboole_0(X0)
% 3.69/1.00      | u1_struct_0(sK2(X1,X0)) = X0 ),
% 3.69/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_35,negated_conjecture,
% 3.69/1.00      ( v2_pre_topc(sK3) ),
% 3.69/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1121,plain,
% 3.69/1.00      ( ~ v2_tex_2(X0,X1)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | v2_struct_0(X1)
% 3.69/1.00      | ~ l1_pre_topc(X1)
% 3.69/1.00      | v1_xboole_0(X0)
% 3.69/1.00      | u1_struct_0(sK2(X1,X0)) = X0
% 3.69/1.00      | sK3 != X1 ),
% 3.69/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_35]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1122,plain,
% 3.69/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/1.00      | v2_struct_0(sK3)
% 3.69/1.00      | ~ l1_pre_topc(sK3)
% 3.69/1.00      | v1_xboole_0(X0)
% 3.69/1.00      | u1_struct_0(sK2(sK3,X0)) = X0 ),
% 3.69/1.00      inference(unflattening,[status(thm)],[c_1121]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_36,negated_conjecture,
% 3.69/1.00      ( ~ v2_struct_0(sK3) ),
% 3.69/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_33,negated_conjecture,
% 3.69/1.00      ( l1_pre_topc(sK3) ),
% 3.69/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1126,plain,
% 3.69/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/1.00      | v1_xboole_0(X0)
% 3.69/1.00      | u1_struct_0(sK2(sK3,X0)) = X0 ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_1122,c_36,c_33]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2970,plain,
% 3.69/1.00      ( u1_struct_0(sK2(sK3,X0)) = X0
% 3.69/1.00      | v2_tex_2(X0,sK3) != iProver_top
% 3.69/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.69/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_1126]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3267,plain,
% 3.69/1.00      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 3.69/1.00      | v2_tex_2(sK4,sK3) != iProver_top
% 3.69/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_2975,c_2970]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_32,negated_conjecture,
% 3.69/1.00      ( ~ v1_xboole_0(sK4) ),
% 3.69/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_41,plain,
% 3.69/1.00      ( v1_xboole_0(sK4) != iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1534,plain,
% 3.69/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.69/1.00      | v1_xboole_0(X0)
% 3.69/1.00      | u1_struct_0(sK2(sK3,X0)) = X0
% 3.69/1.00      | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3))
% 3.69/1.00      | sK4 != X0 ),
% 3.69/1.00      inference(resolution_lifted,[status(thm)],[c_31,c_1126]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1535,plain,
% 3.69/1.00      ( ~ v2_tex_2(sK4,sK3)
% 3.69/1.00      | v1_xboole_0(sK4)
% 3.69/1.00      | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
% 3.69/1.00      inference(unflattening,[status(thm)],[c_1534]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1536,plain,
% 3.69/1.00      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 3.69/1.00      | v2_tex_2(sK4,sK3) != iProver_top
% 3.69/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_1535]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3270,plain,
% 3.69/1.00      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.69/1.00      | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_3267,c_41,c_1536]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3271,plain,
% 3.69/1.00      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 3.69/1.00      | v2_tex_2(sK4,sK3) != iProver_top ),
% 3.69/1.00      inference(renaming,[status(thm)],[c_3270]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3276,plain,
% 3.69/1.00      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 3.69/1.00      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_2976,c_3271]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_0,plain,
% 3.69/1.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.69/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2993,plain,
% 3.69/1.00      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.69/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_10,plain,
% 3.69/1.00      ( r1_tarski(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 3.69/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2983,plain,
% 3.69/1.00      ( r1_tarski(k1_tarski(X0),X1) = iProver_top
% 3.69/1.00      | r2_hidden(X0,X1) != iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_23,plain,
% 3.69/1.00      ( ~ r1_tarski(X0,X1)
% 3.69/1.00      | ~ v1_zfmisc_1(X1)
% 3.69/1.00      | v1_xboole_0(X0)
% 3.69/1.00      | v1_xboole_0(X1)
% 3.69/1.00      | X1 = X0 ),
% 3.69/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_14,plain,
% 3.69/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.69/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_12,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.69/1.00      | ~ v1_xboole_0(X1)
% 3.69/1.00      | v1_xboole_0(X0) ),
% 3.69/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_208,plain,
% 3.69/1.00      ( v1_xboole_0(X0)
% 3.69/1.00      | ~ v1_zfmisc_1(X1)
% 3.69/1.00      | ~ r1_tarski(X0,X1)
% 3.69/1.00      | X1 = X0 ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_23,c_14,c_12]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_209,plain,
% 3.69/1.00      ( ~ r1_tarski(X0,X1)
% 3.69/1.00      | ~ v1_zfmisc_1(X1)
% 3.69/1.00      | v1_xboole_0(X0)
% 3.69/1.00      | X1 = X0 ),
% 3.69/1.00      inference(renaming,[status(thm)],[c_208]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2973,plain,
% 3.69/1.00      ( X0 = X1
% 3.69/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.69/1.00      | v1_zfmisc_1(X0) != iProver_top
% 3.69/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_209]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_4712,plain,
% 3.69/1.00      ( k1_tarski(X0) = X1
% 3.69/1.00      | r2_hidden(X0,X1) != iProver_top
% 3.69/1.00      | v1_zfmisc_1(X1) != iProver_top
% 3.69/1.00      | v1_xboole_0(k1_tarski(X0)) = iProver_top ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_2983,c_2973]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_9,plain,
% 3.69/1.00      ( ~ v1_xboole_0(k1_tarski(X0)) ),
% 3.69/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_94,plain,
% 3.69/1.00      ( v1_xboole_0(k1_tarski(X0)) != iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_9901,plain,
% 3.69/1.00      ( v1_zfmisc_1(X1) != iProver_top
% 3.69/1.00      | r2_hidden(X0,X1) != iProver_top
% 3.69/1.00      | k1_tarski(X0) = X1 ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_4712,c_94]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_9902,plain,
% 3.69/1.00      ( k1_tarski(X0) = X1
% 3.69/1.00      | r2_hidden(X0,X1) != iProver_top
% 3.69/1.00      | v1_zfmisc_1(X1) != iProver_top ),
% 3.69/1.00      inference(renaming,[status(thm)],[c_9901]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_9910,plain,
% 3.69/1.00      ( k1_tarski(sK0(X0)) = X0
% 3.69/1.00      | v1_zfmisc_1(X0) != iProver_top
% 3.69/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_2993,c_9902]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_11852,plain,
% 3.69/1.00      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 3.69/1.00      | k1_tarski(sK0(sK4)) = sK4
% 3.69/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_3276,c_9910]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_11904,plain,
% 3.69/1.00      ( v1_xboole_0(sK4)
% 3.69/1.00      | u1_struct_0(sK2(sK3,sK4)) = sK4
% 3.69/1.00      | k1_tarski(sK0(sK4)) = sK4 ),
% 3.69/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_11852]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_12038,plain,
% 3.69/1.00      ( k1_tarski(sK0(sK4)) = sK4 | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_11852,c_32,c_11904]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_12039,plain,
% 3.69/1.00      ( u1_struct_0(sK2(sK3,sK4)) = sK4 | k1_tarski(sK0(sK4)) = sK4 ),
% 3.69/1.00      inference(renaming,[status(thm)],[c_12038]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_26,plain,
% 3.69/1.00      ( ~ v2_tex_2(X0,X1)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | v2_struct_0(X1)
% 3.69/1.00      | v1_tdlat_3(sK2(X1,X0))
% 3.69/1.00      | ~ v2_pre_topc(X1)
% 3.69/1.00      | ~ l1_pre_topc(X1)
% 3.69/1.00      | v1_xboole_0(X0) ),
% 3.69/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1097,plain,
% 3.69/1.00      ( ~ v2_tex_2(X0,X1)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | v2_struct_0(X1)
% 3.69/1.00      | v1_tdlat_3(sK2(X1,X0))
% 3.69/1.00      | ~ l1_pre_topc(X1)
% 3.69/1.00      | v1_xboole_0(X0)
% 3.69/1.00      | sK3 != X1 ),
% 3.69/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_35]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1098,plain,
% 3.69/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/1.00      | v2_struct_0(sK3)
% 3.69/1.00      | v1_tdlat_3(sK2(sK3,X0))
% 3.69/1.00      | ~ l1_pre_topc(sK3)
% 3.69/1.00      | v1_xboole_0(X0) ),
% 3.69/1.00      inference(unflattening,[status(thm)],[c_1097]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1102,plain,
% 3.69/1.00      ( v1_tdlat_3(sK2(sK3,X0))
% 3.69/1.00      | ~ v2_tex_2(X0,sK3)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/1.00      | v1_xboole_0(X0) ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_1098,c_36,c_33]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1103,plain,
% 3.69/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/1.00      | v1_tdlat_3(sK2(sK3,X0))
% 3.69/1.00      | v1_xboole_0(X0) ),
% 3.69/1.00      inference(renaming,[status(thm)],[c_1102]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_27,plain,
% 3.69/1.00      ( ~ v2_tex_2(X0,X1)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | v2_struct_0(X1)
% 3.69/1.00      | ~ v2_struct_0(sK2(X1,X0))
% 3.69/1.00      | ~ v2_pre_topc(X1)
% 3.69/1.00      | ~ l1_pre_topc(X1)
% 3.69/1.00      | v1_xboole_0(X0) ),
% 3.69/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1073,plain,
% 3.69/1.00      ( ~ v2_tex_2(X0,X1)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | v2_struct_0(X1)
% 3.69/1.00      | ~ v2_struct_0(sK2(X1,X0))
% 3.69/1.00      | ~ l1_pre_topc(X1)
% 3.69/1.00      | v1_xboole_0(X0)
% 3.69/1.00      | sK3 != X1 ),
% 3.69/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_35]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1074,plain,
% 3.69/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/1.00      | ~ v2_struct_0(sK2(sK3,X0))
% 3.69/1.00      | v2_struct_0(sK3)
% 3.69/1.00      | ~ l1_pre_topc(sK3)
% 3.69/1.00      | v1_xboole_0(X0) ),
% 3.69/1.00      inference(unflattening,[status(thm)],[c_1073]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1078,plain,
% 3.69/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/1.00      | ~ v2_struct_0(sK2(sK3,X0))
% 3.69/1.00      | v1_xboole_0(X0) ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_1074,c_36,c_33]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_25,plain,
% 3.69/1.00      ( ~ v2_tex_2(X0,X1)
% 3.69/1.00      | m1_pre_topc(sK2(X1,X0),X1)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | v2_struct_0(X1)
% 3.69/1.00      | ~ v2_pre_topc(X1)
% 3.69/1.00      | ~ l1_pre_topc(X1)
% 3.69/1.00      | v1_xboole_0(X0) ),
% 3.69/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_21,plain,
% 3.69/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.69/1.00      | v2_struct_0(X1)
% 3.69/1.00      | v2_struct_0(X0)
% 3.69/1.00      | ~ v1_tdlat_3(X0)
% 3.69/1.00      | ~ v2_tdlat_3(X1)
% 3.69/1.00      | ~ v2_pre_topc(X1)
% 3.69/1.00      | v7_struct_0(X0)
% 3.69/1.00      | ~ l1_pre_topc(X1) ),
% 3.69/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_16,plain,
% 3.69/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.69/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_18,plain,
% 3.69/1.00      ( ~ v7_struct_0(X0)
% 3.69/1.00      | v1_zfmisc_1(u1_struct_0(X0))
% 3.69/1.00      | ~ l1_struct_0(X0) ),
% 3.69/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_493,plain,
% 3.69/1.00      ( ~ v7_struct_0(X0)
% 3.69/1.00      | v1_zfmisc_1(u1_struct_0(X0))
% 3.69/1.00      | ~ l1_pre_topc(X0) ),
% 3.69/1.00      inference(resolution,[status(thm)],[c_16,c_18]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_511,plain,
% 3.69/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.69/1.00      | v2_struct_0(X0)
% 3.69/1.00      | v2_struct_0(X1)
% 3.69/1.00      | ~ v1_tdlat_3(X0)
% 3.69/1.00      | ~ v2_tdlat_3(X1)
% 3.69/1.00      | ~ v2_pre_topc(X1)
% 3.69/1.00      | v1_zfmisc_1(u1_struct_0(X0))
% 3.69/1.00      | ~ l1_pre_topc(X0)
% 3.69/1.00      | ~ l1_pre_topc(X1) ),
% 3.69/1.00      inference(resolution,[status(thm)],[c_21,c_493]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_17,plain,
% 3.69/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.69/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_515,plain,
% 3.69/1.00      ( v1_zfmisc_1(u1_struct_0(X0))
% 3.69/1.00      | ~ v2_pre_topc(X1)
% 3.69/1.00      | ~ v2_tdlat_3(X1)
% 3.69/1.00      | ~ v1_tdlat_3(X0)
% 3.69/1.00      | v2_struct_0(X1)
% 3.69/1.00      | v2_struct_0(X0)
% 3.69/1.00      | ~ m1_pre_topc(X0,X1)
% 3.69/1.00      | ~ l1_pre_topc(X1) ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_511,c_17]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_516,plain,
% 3.69/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.69/1.00      | v2_struct_0(X0)
% 3.69/1.00      | v2_struct_0(X1)
% 3.69/1.00      | ~ v1_tdlat_3(X0)
% 3.69/1.00      | ~ v2_tdlat_3(X1)
% 3.69/1.00      | ~ v2_pre_topc(X1)
% 3.69/1.00      | v1_zfmisc_1(u1_struct_0(X0))
% 3.69/1.00      | ~ l1_pre_topc(X1) ),
% 3.69/1.00      inference(renaming,[status(thm)],[c_515]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_20,plain,
% 3.69/1.00      ( ~ v2_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 3.69/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_535,plain,
% 3.69/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.69/1.00      | v2_struct_0(X0)
% 3.69/1.00      | v2_struct_0(X1)
% 3.69/1.00      | ~ v1_tdlat_3(X0)
% 3.69/1.00      | ~ v2_tdlat_3(X1)
% 3.69/1.00      | v1_zfmisc_1(u1_struct_0(X0))
% 3.69/1.00      | ~ l1_pre_topc(X1) ),
% 3.69/1.00      inference(forward_subsumption_resolution,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_516,c_20]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_34,negated_conjecture,
% 3.69/1.00      ( v2_tdlat_3(sK3) ),
% 3.69/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_556,plain,
% 3.69/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.69/1.00      | v2_struct_0(X0)
% 3.69/1.00      | v2_struct_0(X1)
% 3.69/1.00      | ~ v1_tdlat_3(X0)
% 3.69/1.00      | v1_zfmisc_1(u1_struct_0(X0))
% 3.69/1.00      | ~ l1_pre_topc(X1)
% 3.69/1.00      | sK3 != X1 ),
% 3.69/1.00      inference(resolution_lifted,[status(thm)],[c_535,c_34]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_557,plain,
% 3.69/1.00      ( ~ m1_pre_topc(X0,sK3)
% 3.69/1.00      | v2_struct_0(X0)
% 3.69/1.00      | v2_struct_0(sK3)
% 3.69/1.00      | ~ v1_tdlat_3(X0)
% 3.69/1.00      | v1_zfmisc_1(u1_struct_0(X0))
% 3.69/1.00      | ~ l1_pre_topc(sK3) ),
% 3.69/1.00      inference(unflattening,[status(thm)],[c_556]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_561,plain,
% 3.69/1.00      ( v1_zfmisc_1(u1_struct_0(X0))
% 3.69/1.00      | ~ v1_tdlat_3(X0)
% 3.69/1.00      | ~ m1_pre_topc(X0,sK3)
% 3.69/1.00      | v2_struct_0(X0) ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_557,c_36,c_33]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_562,plain,
% 3.69/1.00      ( ~ m1_pre_topc(X0,sK3)
% 3.69/1.00      | v2_struct_0(X0)
% 3.69/1.00      | ~ v1_tdlat_3(X0)
% 3.69/1.00      | v1_zfmisc_1(u1_struct_0(X0)) ),
% 3.69/1.00      inference(renaming,[status(thm)],[c_561]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_734,plain,
% 3.69/1.00      ( ~ v2_tex_2(X0,X1)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | v2_struct_0(X2)
% 3.69/1.00      | v2_struct_0(X1)
% 3.69/1.00      | ~ v1_tdlat_3(X2)
% 3.69/1.00      | ~ v2_pre_topc(X1)
% 3.69/1.00      | v1_zfmisc_1(u1_struct_0(X2))
% 3.69/1.00      | ~ l1_pre_topc(X1)
% 3.69/1.00      | v1_xboole_0(X0)
% 3.69/1.00      | sK2(X1,X0) != X2
% 3.69/1.00      | sK3 != X1 ),
% 3.69/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_562]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_735,plain,
% 3.69/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/1.00      | v2_struct_0(sK2(sK3,X0))
% 3.69/1.00      | v2_struct_0(sK3)
% 3.69/1.00      | ~ v1_tdlat_3(sK2(sK3,X0))
% 3.69/1.00      | ~ v2_pre_topc(sK3)
% 3.69/1.00      | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
% 3.69/1.00      | ~ l1_pre_topc(sK3)
% 3.69/1.00      | v1_xboole_0(X0) ),
% 3.69/1.00      inference(unflattening,[status(thm)],[c_734]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_739,plain,
% 3.69/1.00      ( v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
% 3.69/1.00      | v2_struct_0(sK2(sK3,X0))
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/1.00      | ~ v2_tex_2(X0,sK3)
% 3.69/1.00      | ~ v1_tdlat_3(sK2(sK3,X0))
% 3.69/1.00      | v1_xboole_0(X0) ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_735,c_36,c_35,c_33]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_740,plain,
% 3.69/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/1.00      | v2_struct_0(sK2(sK3,X0))
% 3.69/1.00      | ~ v1_tdlat_3(sK2(sK3,X0))
% 3.69/1.00      | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
% 3.69/1.00      | v1_xboole_0(X0) ),
% 3.69/1.00      inference(renaming,[status(thm)],[c_739]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1156,plain,
% 3.69/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/1.00      | ~ v1_tdlat_3(sK2(sK3,X0))
% 3.69/1.00      | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
% 3.69/1.00      | v1_xboole_0(X0) ),
% 3.69/1.00      inference(backward_subsumption_resolution,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_1078,c_740]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1165,plain,
% 3.69/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/1.00      | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
% 3.69/1.00      | v1_xboole_0(X0) ),
% 3.69/1.00      inference(backward_subsumption_resolution,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_1103,c_1156]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2969,plain,
% 3.69/1.00      ( v2_tex_2(X0,sK3) != iProver_top
% 3.69/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.69/1.00      | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0))) = iProver_top
% 3.69/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_1165]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3283,plain,
% 3.69/1.00      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.69/1.00      | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top
% 3.69/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_2975,c_2969]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1520,plain,
% 3.69/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.69/1.00      | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
% 3.69/1.00      | v1_xboole_0(X0)
% 3.69/1.00      | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3))
% 3.69/1.00      | sK4 != X0 ),
% 3.69/1.00      inference(resolution_lifted,[status(thm)],[c_31,c_1165]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1521,plain,
% 3.69/1.00      ( ~ v2_tex_2(sK4,sK3)
% 3.69/1.00      | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
% 3.69/1.00      | v1_xboole_0(sK4) ),
% 3.69/1.00      inference(unflattening,[status(thm)],[c_1520]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1523,plain,
% 3.69/1.00      ( v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) | ~ v2_tex_2(sK4,sK3) ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_1521,c_32]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1524,plain,
% 3.69/1.00      ( ~ v2_tex_2(sK4,sK3) | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) ),
% 3.69/1.00      inference(renaming,[status(thm)],[c_1523]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1525,plain,
% 3.69/1.00      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.69/1.00      | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_1524]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3566,plain,
% 3.69/1.00      ( v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top
% 3.69/1.00      | v2_tex_2(sK4,sK3) != iProver_top ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_3283,c_1525]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3567,plain,
% 3.69/1.00      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.69/1.00      | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top ),
% 3.69/1.00      inference(renaming,[status(thm)],[c_3566]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_12043,plain,
% 3.69/1.00      ( k1_tarski(sK0(sK4)) = sK4
% 3.69/1.00      | v2_tex_2(sK4,sK3) != iProver_top
% 3.69/1.00      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_12039,c_3567]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_293,plain,
% 3.69/1.00      ( v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3) ),
% 3.69/1.00      inference(prop_impl,[status(thm)],[c_30]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_294,plain,
% 3.69/1.00      ( v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) ),
% 3.69/1.00      inference(renaming,[status(thm)],[c_293]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1251,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/1.00      | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
% 3.69/1.00      | v1_zfmisc_1(sK4)
% 3.69/1.00      | v1_xboole_0(X0)
% 3.69/1.00      | sK3 != sK3
% 3.69/1.00      | sK4 != X0 ),
% 3.69/1.00      inference(resolution_lifted,[status(thm)],[c_294,c_1165]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1252,plain,
% 3.69/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/1.00      | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
% 3.69/1.00      | v1_zfmisc_1(sK4)
% 3.69/1.00      | v1_xboole_0(sK4) ),
% 3.69/1.00      inference(unflattening,[status(thm)],[c_1251]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1254,plain,
% 3.69/1.00      ( v1_zfmisc_1(sK4) | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_1252,c_32,c_31]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1255,plain,
% 3.69/1.00      ( v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) | v1_zfmisc_1(sK4) ),
% 3.69/1.00      inference(renaming,[status(thm)],[c_1254]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1256,plain,
% 3.69/1.00      ( v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top
% 3.69/1.00      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_1255]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1265,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/1.00      | v1_zfmisc_1(sK4)
% 3.69/1.00      | v1_xboole_0(X0)
% 3.69/1.00      | u1_struct_0(sK2(sK3,X0)) = X0
% 3.69/1.00      | sK3 != sK3
% 3.69/1.00      | sK4 != X0 ),
% 3.69/1.00      inference(resolution_lifted,[status(thm)],[c_294,c_1126]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1266,plain,
% 3.69/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/1.00      | v1_zfmisc_1(sK4)
% 3.69/1.00      | v1_xboole_0(sK4)
% 3.69/1.00      | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
% 3.69/1.00      inference(unflattening,[status(thm)],[c_1265]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1268,plain,
% 3.69/1.00      ( v1_zfmisc_1(sK4) | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_1266,c_32,c_31]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1270,plain,
% 3.69/1.00      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 3.69/1.00      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_1268]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2332,plain,( X0 = X0 ),theory(equality) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3354,plain,
% 3.69/1.00      ( sK4 = sK4 ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_2332]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2333,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3311,plain,
% 3.69/1.00      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_2333]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3531,plain,
% 3.69/1.00      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_3311]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3814,plain,
% 3.69/1.00      ( u1_struct_0(sK2(sK3,sK4)) != sK4
% 3.69/1.00      | sK4 = u1_struct_0(sK2(sK3,sK4))
% 3.69/1.00      | sK4 != sK4 ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_3531]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2340,plain,
% 3.69/1.00      ( ~ v1_zfmisc_1(X0) | v1_zfmisc_1(X1) | X1 != X0 ),
% 3.69/1.00      theory(equality) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3555,plain,
% 3.69/1.00      ( v1_zfmisc_1(X0)
% 3.69/1.00      | ~ v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
% 3.69/1.00      | X0 != u1_struct_0(sK2(sK3,sK4)) ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_2340]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_5113,plain,
% 3.69/1.00      ( ~ v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
% 3.69/1.00      | v1_zfmisc_1(sK4)
% 3.69/1.00      | sK4 != u1_struct_0(sK2(sK3,sK4)) ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_3555]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_5114,plain,
% 3.69/1.00      ( sK4 != u1_struct_0(sK2(sK3,sK4))
% 3.69/1.00      | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) != iProver_top
% 3.69/1.00      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_5113]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_12156,plain,
% 3.69/1.00      ( v1_zfmisc_1(sK4) = iProver_top ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_12043,c_1256,c_1270,c_3354,c_3814,c_5114]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_12161,plain,
% 3.69/1.00      ( k1_tarski(sK0(sK4)) = sK4 | v1_xboole_0(sK4) = iProver_top ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_12156,c_9910]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_12340,plain,
% 3.69/1.00      ( k1_tarski(sK0(sK4)) = sK4 ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_12161,c_41]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_15,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.69/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2979,plain,
% 3.69/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.69/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3671,plain,
% 3.69/1.00      ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_2975,c_2979]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_8,plain,
% 3.69/1.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.69/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2985,plain,
% 3.69/1.00      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3772,plain,
% 3.69/1.00      ( k3_xboole_0(sK4,u1_struct_0(sK3)) = sK4 ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_3671,c_2985]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_6,plain,
% 3.69/1.00      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 3.69/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2987,plain,
% 3.69/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.69/1.00      | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_4215,plain,
% 3.69/1.00      ( r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
% 3.69/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_3772,c_2987]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_13,plain,
% 3.69/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.69/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2981,plain,
% 3.69/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 3.69/1.00      | r2_hidden(X0,X1) != iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_4407,plain,
% 3.69/1.00      ( m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
% 3.69/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_4215,c_2981]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_19,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,X1)
% 3.69/1.00      | v1_xboole_0(X1)
% 3.69/1.00      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 3.69/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2978,plain,
% 3.69/1.00      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 3.69/1.00      | m1_subset_1(X1,X0) != iProver_top
% 3.69/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_4738,plain,
% 3.69/1.00      ( k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0)
% 3.69/1.00      | r2_hidden(X0,sK4) != iProver_top
% 3.69/1.00      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_4407,c_2978]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_42,plain,
% 3.69/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3198,plain,
% 3.69/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/1.00      | r1_tarski(sK4,u1_struct_0(sK3)) ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3199,plain,
% 3.69/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.69/1.00      | r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_3198]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_289,plain,
% 3.69/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.69/1.00      inference(prop_impl,[status(thm)],[c_14]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_290,plain,
% 3.69/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.69/1.00      inference(renaming,[status(thm)],[c_289]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_362,plain,
% 3.69/1.00      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 3.69/1.00      inference(bin_hyper_res,[status(thm)],[c_12,c_290]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3206,plain,
% 3.69/1.00      ( ~ r1_tarski(sK4,X0) | ~ v1_xboole_0(X0) | v1_xboole_0(sK4) ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_362]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3308,plain,
% 3.69/1.00      ( ~ r1_tarski(sK4,u1_struct_0(sK3))
% 3.69/1.00      | ~ v1_xboole_0(u1_struct_0(sK3))
% 3.69/1.00      | v1_xboole_0(sK4) ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_3206]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3309,plain,
% 3.69/1.00      ( r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top
% 3.69/1.00      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
% 3.69/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_3308]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_5335,plain,
% 3.69/1.00      ( r2_hidden(X0,sK4) != iProver_top
% 3.69/1.00      | k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0) ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_4738,c_41,c_42,c_3199,c_3309]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_5336,plain,
% 3.69/1.00      ( k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0)
% 3.69/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 3.69/1.00      inference(renaming,[status(thm)],[c_5335]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_5343,plain,
% 3.69/1.00      ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4))
% 3.69/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_2993,c_5336]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_8931,plain,
% 3.69/1.00      ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4)) ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_5343,c_41]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_28,plain,
% 3.69/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 3.69/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.69/1.00      | v2_struct_0(X0)
% 3.69/1.00      | ~ v2_pre_topc(X0)
% 3.69/1.00      | ~ l1_pre_topc(X0) ),
% 3.69/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1031,plain,
% 3.69/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 3.69/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.69/1.00      | v2_struct_0(X0)
% 3.69/1.00      | ~ l1_pre_topc(X0)
% 3.69/1.00      | sK3 != X0 ),
% 3.69/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_35]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1032,plain,
% 3.69/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
% 3.69/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.69/1.00      | v2_struct_0(sK3)
% 3.69/1.00      | ~ l1_pre_topc(sK3) ),
% 3.69/1.00      inference(unflattening,[status(thm)],[c_1031]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1036,plain,
% 3.69/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
% 3.69/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_1032,c_36,c_33]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2971,plain,
% 3.69/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) = iProver_top
% 3.69/1.00      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_1036]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_8934,plain,
% 3.69/1.00      ( v2_tex_2(k1_tarski(sK0(sK4)),sK3) = iProver_top
% 3.69/1.00      | m1_subset_1(sK0(sK4),u1_struct_0(sK3)) != iProver_top ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_8931,c_2971]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_9012,plain,
% 3.69/1.00      ( v2_tex_2(k1_tarski(sK0(sK4)),sK3) = iProver_top
% 3.69/1.00      | r2_hidden(sK0(sK4),sK4) != iProver_top ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_4407,c_8934]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3191,plain,
% 3.69/1.00      ( r2_hidden(sK0(sK4),sK4) | v1_xboole_0(sK4) ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3192,plain,
% 3.69/1.00      ( r2_hidden(sK0(sK4),sK4) = iProver_top
% 3.69/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_3191]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_9015,plain,
% 3.69/1.00      ( v2_tex_2(k1_tarski(sK0(sK4)),sK3) = iProver_top ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_9012,c_41,c_3192]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_12350,plain,
% 3.69/1.00      ( v2_tex_2(sK4,sK3) = iProver_top ),
% 3.69/1.00      inference(demodulation,[status(thm)],[c_12340,c_9015]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_29,negated_conjecture,
% 3.69/1.00      ( ~ v2_tex_2(sK4,sK3) | ~ v1_zfmisc_1(sK4) ),
% 3.69/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_44,plain,
% 3.69/1.00      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.69/1.00      | v1_zfmisc_1(sK4) != iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(contradiction,plain,
% 3.69/1.00      ( $false ),
% 3.69/1.00      inference(minisat,[status(thm)],[c_12350,c_12156,c_44]) ).
% 3.69/1.00  
% 3.69/1.00  
% 3.69/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.69/1.00  
% 3.69/1.00  ------                               Statistics
% 3.69/1.00  
% 3.69/1.00  ------ General
% 3.69/1.00  
% 3.69/1.00  abstr_ref_over_cycles:                  0
% 3.69/1.00  abstr_ref_under_cycles:                 0
% 3.69/1.00  gc_basic_clause_elim:                   0
% 3.69/1.00  forced_gc_time:                         0
% 3.69/1.00  parsing_time:                           0.028
% 3.69/1.00  unif_index_cands_time:                  0.
% 3.69/1.00  unif_index_add_time:                    0.
% 3.69/1.00  orderings_time:                         0.
% 3.69/1.00  out_proof_time:                         0.013
% 3.69/1.00  total_time:                             0.324
% 3.69/1.00  num_of_symbols:                         55
% 3.69/1.00  num_of_terms:                           11000
% 3.69/1.00  
% 3.69/1.00  ------ Preprocessing
% 3.69/1.00  
% 3.69/1.00  num_of_splits:                          0
% 3.69/1.00  num_of_split_atoms:                     0
% 3.69/1.00  num_of_reused_defs:                     0
% 3.69/1.00  num_eq_ax_congr_red:                    34
% 3.69/1.00  num_of_sem_filtered_clauses:            1
% 3.69/1.00  num_of_subtypes:                        0
% 3.69/1.00  monotx_restored_types:                  0
% 3.69/1.00  sat_num_of_epr_types:                   0
% 3.69/1.00  sat_num_of_non_cyclic_types:            0
% 3.69/1.00  sat_guarded_non_collapsed_types:        0
% 3.69/1.00  num_pure_diseq_elim:                    0
% 3.69/1.00  simp_replaced_by:                       0
% 3.69/1.00  res_preprocessed:                       136
% 3.69/1.00  prep_upred:                             0
% 3.69/1.00  prep_unflattend:                        86
% 3.69/1.00  smt_new_axioms:                         0
% 3.69/1.00  pred_elim_cands:                        6
% 3.69/1.00  pred_elim:                              8
% 3.69/1.00  pred_elim_cl:                           11
% 3.69/1.00  pred_elim_cycles:                       20
% 3.69/1.00  merged_defs:                            24
% 3.69/1.00  merged_defs_ncl:                        0
% 3.69/1.00  bin_hyper_res:                          25
% 3.69/1.00  prep_cycles:                            4
% 3.69/1.00  pred_elim_time:                         0.028
% 3.69/1.00  splitting_time:                         0.
% 3.69/1.00  sem_filter_time:                        0.
% 3.69/1.00  monotx_time:                            0.001
% 3.69/1.00  subtype_inf_time:                       0.
% 3.69/1.00  
% 3.69/1.00  ------ Problem properties
% 3.69/1.00  
% 3.69/1.00  clauses:                                25
% 3.69/1.00  conjectures:                            4
% 3.69/1.00  epr:                                    7
% 3.69/1.00  horn:                                   17
% 3.69/1.00  ground:                                 4
% 3.69/1.00  unary:                                  3
% 3.69/1.00  binary:                                 13
% 3.69/1.00  lits:                                   60
% 3.69/1.00  lits_eq:                                7
% 3.69/1.00  fd_pure:                                0
% 3.69/1.00  fd_pseudo:                              0
% 3.69/1.00  fd_cond:                                0
% 3.69/1.00  fd_pseudo_cond:                         4
% 3.69/1.00  ac_symbols:                             0
% 3.69/1.00  
% 3.69/1.00  ------ Propositional Solver
% 3.69/1.00  
% 3.69/1.00  prop_solver_calls:                      27
% 3.69/1.00  prop_fast_solver_calls:                 1386
% 3.69/1.00  smt_solver_calls:                       0
% 3.69/1.00  smt_fast_solver_calls:                  0
% 3.69/1.00  prop_num_of_clauses:                    4703
% 3.69/1.00  prop_preprocess_simplified:             9714
% 3.69/1.00  prop_fo_subsumed:                       60
% 3.69/1.00  prop_solver_time:                       0.
% 3.69/1.00  smt_solver_time:                        0.
% 3.69/1.00  smt_fast_solver_time:                   0.
% 3.69/1.00  prop_fast_solver_time:                  0.
% 3.69/1.00  prop_unsat_core_time:                   0.
% 3.69/1.00  
% 3.69/1.00  ------ QBF
% 3.69/1.00  
% 3.69/1.00  qbf_q_res:                              0
% 3.69/1.00  qbf_num_tautologies:                    0
% 3.69/1.00  qbf_prep_cycles:                        0
% 3.69/1.00  
% 3.69/1.00  ------ BMC1
% 3.69/1.00  
% 3.69/1.00  bmc1_current_bound:                     -1
% 3.69/1.00  bmc1_last_solved_bound:                 -1
% 3.69/1.00  bmc1_unsat_core_size:                   -1
% 3.69/1.00  bmc1_unsat_core_parents_size:           -1
% 3.69/1.00  bmc1_merge_next_fun:                    0
% 3.69/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.69/1.00  
% 3.69/1.00  ------ Instantiation
% 3.69/1.00  
% 3.69/1.00  inst_num_of_clauses:                    1213
% 3.69/1.00  inst_num_in_passive:                    237
% 3.69/1.00  inst_num_in_active:                     413
% 3.69/1.00  inst_num_in_unprocessed:                563
% 3.69/1.00  inst_num_of_loops:                      520
% 3.69/1.00  inst_num_of_learning_restarts:          0
% 3.69/1.00  inst_num_moves_active_passive:          104
% 3.69/1.00  inst_lit_activity:                      0
% 3.69/1.00  inst_lit_activity_moves:                0
% 3.69/1.00  inst_num_tautologies:                   0
% 3.69/1.00  inst_num_prop_implied:                  0
% 3.69/1.00  inst_num_existing_simplified:           0
% 3.69/1.00  inst_num_eq_res_simplified:             0
% 3.69/1.00  inst_num_child_elim:                    0
% 3.69/1.00  inst_num_of_dismatching_blockings:      275
% 3.69/1.00  inst_num_of_non_proper_insts:           817
% 3.69/1.00  inst_num_of_duplicates:                 0
% 3.69/1.00  inst_inst_num_from_inst_to_res:         0
% 3.69/1.00  inst_dismatching_checking_time:         0.
% 3.69/1.00  
% 3.69/1.00  ------ Resolution
% 3.69/1.00  
% 3.69/1.00  res_num_of_clauses:                     0
% 3.69/1.00  res_num_in_passive:                     0
% 3.69/1.00  res_num_in_active:                      0
% 3.69/1.00  res_num_of_loops:                       140
% 3.69/1.00  res_forward_subset_subsumed:            68
% 3.69/1.00  res_backward_subset_subsumed:           0
% 3.69/1.00  res_forward_subsumed:                   0
% 3.69/1.00  res_backward_subsumed:                  0
% 3.69/1.00  res_forward_subsumption_resolution:     1
% 3.69/1.00  res_backward_subsumption_resolution:    2
% 3.69/1.00  res_clause_to_clause_subsumption:       1193
% 3.69/1.00  res_orphan_elimination:                 0
% 3.69/1.00  res_tautology_del:                      103
% 3.69/1.00  res_num_eq_res_simplified:              0
% 3.69/1.00  res_num_sel_changes:                    0
% 3.69/1.00  res_moves_from_active_to_pass:          0
% 3.69/1.00  
% 3.69/1.00  ------ Superposition
% 3.69/1.00  
% 3.69/1.00  sup_time_total:                         0.
% 3.69/1.00  sup_time_generating:                    0.
% 3.69/1.00  sup_time_sim_full:                      0.
% 3.69/1.00  sup_time_sim_immed:                     0.
% 3.69/1.00  
% 3.69/1.00  sup_num_of_clauses:                     303
% 3.69/1.00  sup_num_in_active:                      75
% 3.69/1.00  sup_num_in_passive:                     228
% 3.69/1.00  sup_num_of_loops:                       103
% 3.69/1.00  sup_fw_superposition:                   195
% 3.69/1.00  sup_bw_superposition:                   227
% 3.69/1.00  sup_immediate_simplified:               76
% 3.69/1.00  sup_given_eliminated:                   0
% 3.69/1.00  comparisons_done:                       0
% 3.69/1.00  comparisons_avoided:                    13
% 3.69/1.00  
% 3.69/1.00  ------ Simplifications
% 3.69/1.00  
% 3.69/1.00  
% 3.69/1.00  sim_fw_subset_subsumed:                 31
% 3.69/1.00  sim_bw_subset_subsumed:                 9
% 3.69/1.00  sim_fw_subsumed:                        35
% 3.69/1.00  sim_bw_subsumed:                        1
% 3.69/1.00  sim_fw_subsumption_res:                 5
% 3.69/1.00  sim_bw_subsumption_res:                 0
% 3.69/1.00  sim_tautology_del:                      40
% 3.69/1.00  sim_eq_tautology_del:                   0
% 3.69/1.00  sim_eq_res_simp:                        6
% 3.69/1.00  sim_fw_demodulated:                     1
% 3.69/1.00  sim_bw_demodulated:                     20
% 3.69/1.00  sim_light_normalised:                   17
% 3.69/1.00  sim_joinable_taut:                      0
% 3.69/1.00  sim_joinable_simp:                      0
% 3.69/1.00  sim_ac_normalised:                      0
% 3.69/1.00  sim_smt_subsumption:                    0
% 3.69/1.00  
%------------------------------------------------------------------------------
