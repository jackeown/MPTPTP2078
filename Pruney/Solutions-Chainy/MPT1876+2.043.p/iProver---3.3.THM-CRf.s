%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:56 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :  206 (2477 expanded)
%              Number of clauses        :  124 ( 609 expanded)
%              Number of leaves         :   24 ( 564 expanded)
%              Depth                    :   33
%              Number of atoms          :  801 (17632 expanded)
%              Number of equality atoms :  166 ( 760 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f54,plain,(
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

fof(f53,plain,
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

fof(f55,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f52,f54,f53])).

fof(f86,plain,
    ( v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f85,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f55])).

fof(f14,axiom,(
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

fof(f18,plain,(
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
    inference(pure_predicate_removal,[],[f14])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f49,plain,(
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

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f49])).

fof(f78,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK2(X0,X1)) = X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f81,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f80,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f83,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f84,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f57,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f74,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK2(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f12,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X1)
      | v7_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

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

fof(f67,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f69,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f68,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f71,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f82,plain,(
    v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f45])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f87,plain,
    ( ~ v1_zfmisc_1(sK4)
    | ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2427,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_zfmisc_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4339,plain,
    ( v1_zfmisc_1(X0)
    | ~ v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
    | X0 != u1_struct_0(sK2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2427])).

cnf(c_6245,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
    | v1_zfmisc_1(sK4)
    | sK4 != u1_struct_0(sK2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_4339])).

cnf(c_25,negated_conjecture,
    ( v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2971,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2970,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_19,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_871,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(X1,X0)) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_872,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(sK3,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_871])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_876,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_872,c_31,c_28])).

cnf(c_2967,plain,
    ( u1_struct_0(sK2(sK3,X0)) = X0
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_876])).

cnf(c_3159,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v2_tex_2(sK4,sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2970,c_2967])).

cnf(c_27,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_36,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1292,plain,
    ( ~ v2_tex_2(X0,sK3)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(sK3,X0)) = X0
    | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_876])).

cnf(c_1293,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | v1_xboole_0(sK4)
    | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
    inference(unflattening,[status(thm)],[c_1292])).

cnf(c_1294,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v2_tex_2(sK4,sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1293])).

cnf(c_3216,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3159,c_36,c_1294])).

cnf(c_3217,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v2_tex_2(sK4,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3216])).

cnf(c_3222,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2971,c_3217])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2985,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2979,plain,
    ( r1_tarski(k1_tarski(X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2973,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3668,plain,
    ( k1_tarski(X0) = X1
    | r2_hidden(X0,X1) != iProver_top
    | v1_zfmisc_1(X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k1_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2979,c_2973])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_88,plain,
    ( v1_xboole_0(k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_98,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4737,plain,
    ( k1_tarski(X0) = X1
    | r2_hidden(X0,X1) != iProver_top
    | v1_zfmisc_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3668,c_88,c_98])).

cnf(c_4746,plain,
    ( k1_tarski(sK0(X0)) = X0
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2985,c_4737])).

cnf(c_5441,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | k1_tarski(sK0(sK4)) = sK4
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3222,c_4746])).

cnf(c_5488,plain,
    ( v1_xboole_0(sK4)
    | u1_struct_0(sK2(sK3,sK4)) = sK4
    | k1_tarski(sK0(sK4)) = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5441])).

cnf(c_5562,plain,
    ( k1_tarski(sK0(sK4)) = sK4
    | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5441,c_27,c_5488])).

cnf(c_5563,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | k1_tarski(sK0(sK4)) = sK4 ),
    inference(renaming,[status(thm)],[c_5562])).

cnf(c_21,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v1_tdlat_3(sK2(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_847,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v1_tdlat_3(sK2(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_30])).

cnf(c_848,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | v1_tdlat_3(sK2(sK3,X0))
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_847])).

cnf(c_852,plain,
    ( v1_tdlat_3(sK2(sK3,X0))
    | ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_848,c_31,c_28])).

cnf(c_853,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tdlat_3(sK2(sK3,X0))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_852])).

cnf(c_22,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK2(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_823,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK2(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_824,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_struct_0(sK2(sK3,X0))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_823])).

cnf(c_828,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_struct_0(sK2(sK3,X0))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_824,c_31,c_28])).

cnf(c_20,plain,
    ( ~ v2_tex_2(X0,X1)
    | m1_pre_topc(sK2(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_11,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_13,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_428,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_11,c_13])).

cnf(c_446,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_16,c_428])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_450,plain,
    ( v1_zfmisc_1(u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_446,c_12])).

cnf(c_451,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_450])).

cnf(c_15,plain,
    ( ~ v2_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_470,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X1)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_451,c_15])).

cnf(c_29,negated_conjecture,
    ( v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_491,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_470,c_29])).

cnf(c_492,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ v1_tdlat_3(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_496,plain,
    ( v1_zfmisc_1(u1_struct_0(X0))
    | ~ v1_tdlat_3(X0)
    | ~ m1_pre_topc(X0,sK3)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_492,c_31,c_28])).

cnf(c_497,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(renaming,[status(thm)],[c_496])).

cnf(c_591,plain,
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
    inference(resolution_lifted,[status(thm)],[c_20,c_497])).

cnf(c_592,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK2(sK3,X0))
    | v2_struct_0(sK3)
    | ~ v1_tdlat_3(sK2(sK3,X0))
    | ~ v2_pre_topc(sK3)
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_591])).

cnf(c_596,plain,
    ( v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
    | v2_struct_0(sK2(sK3,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_tex_2(X0,sK3)
    | ~ v1_tdlat_3(sK2(sK3,X0))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_592,c_31,c_30,c_28])).

cnf(c_597,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK2(sK3,X0))
    | ~ v1_tdlat_3(sK2(sK3,X0))
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_596])).

cnf(c_906,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tdlat_3(sK2(sK3,X0))
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
    | v1_xboole_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_828,c_597])).

cnf(c_915,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
    | v1_xboole_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_853,c_906])).

cnf(c_2966,plain,
    ( v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0))) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_915])).

cnf(c_3229,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2970,c_2966])).

cnf(c_1278,plain,
    ( ~ v2_tex_2(X0,sK3)
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
    | v1_xboole_0(X0)
    | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_915])).

cnf(c_1279,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1278])).

cnf(c_1281,plain,
    ( v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
    | ~ v2_tex_2(sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1279,c_27])).

cnf(c_1282,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) ),
    inference(renaming,[status(thm)],[c_1281])).

cnf(c_1283,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1282])).

cnf(c_3426,plain,
    ( v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top
    | v2_tex_2(sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3229,c_1283])).

cnf(c_3427,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3426])).

cnf(c_5567,plain,
    ( k1_tarski(sK0(sK4)) = sK4
    | v2_tex_2(sK4,sK3) != iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5563,c_3427])).

cnf(c_38,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5710,plain,
    ( k1_tarski(sK0(sK4)) = sK4
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5567,c_38])).

cnf(c_5716,plain,
    ( k1_tarski(sK0(sK4)) = sK4
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5710,c_4746])).

cnf(c_5807,plain,
    ( k1_tarski(sK0(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5716,c_36])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2975,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3455,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2970,c_2975])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2981,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4142,plain,
    ( r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3455,c_2981])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2977,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4471,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4142,c_2977])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2974,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4659,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0)
    | r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4471,c_2974])).

cnf(c_2984,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4470,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4142,c_2984])).

cnf(c_5130,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4659,c_4470])).

cnf(c_5131,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0)
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_5130])).

cnf(c_5138,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4))
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2985,c_5131])).

cnf(c_5190,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5138,c_36])).

cnf(c_23,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_781,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_782,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_781])).

cnf(c_786,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_782,c_31,c_28])).

cnf(c_2968,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_786])).

cnf(c_5193,plain,
    ( v2_tex_2(k1_tarski(sK0(sK4)),sK3) = iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5190,c_2968])).

cnf(c_5212,plain,
    ( v2_tex_2(k1_tarski(sK0(sK4)),sK3) = iProver_top
    | r2_hidden(sK0(sK4),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4471,c_5193])).

cnf(c_3562,plain,
    ( r2_hidden(sK0(sK4),sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3565,plain,
    ( r2_hidden(sK0(sK4),sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3562])).

cnf(c_5215,plain,
    ( v2_tex_2(k1_tarski(sK0(sK4)),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5212,c_36,c_3565])).

cnf(c_5810,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5807,c_5215])).

cnf(c_5824,plain,
    ( v2_tex_2(sK4,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5810])).

cnf(c_2420,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3202,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_2420])).

cnf(c_3392,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3202])).

cnf(c_4346,plain,
    ( u1_struct_0(sK2(sK3,sK4)) != sK4
    | sK4 = u1_struct_0(sK2(sK3,sK4))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3392])).

cnf(c_2419,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3393,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2419])).

cnf(c_24,negated_conjecture,
    ( ~ v2_tex_2(sK4,sK3)
    | ~ v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6245,c_5824,c_5810,c_4346,c_3393,c_1294,c_1279,c_24,c_36,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:45:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.81/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/0.99  
% 2.81/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.81/0.99  
% 2.81/0.99  ------  iProver source info
% 2.81/0.99  
% 2.81/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.81/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.81/0.99  git: non_committed_changes: false
% 2.81/0.99  git: last_make_outside_of_git: false
% 2.81/0.99  
% 2.81/0.99  ------ 
% 2.81/0.99  
% 2.81/0.99  ------ Input Options
% 2.81/0.99  
% 2.81/0.99  --out_options                           all
% 2.81/0.99  --tptp_safe_out                         true
% 2.81/0.99  --problem_path                          ""
% 2.81/0.99  --include_path                          ""
% 2.81/0.99  --clausifier                            res/vclausify_rel
% 2.81/0.99  --clausifier_options                    --mode clausify
% 2.81/0.99  --stdin                                 false
% 2.81/0.99  --stats_out                             all
% 2.81/0.99  
% 2.81/0.99  ------ General Options
% 2.81/0.99  
% 2.81/0.99  --fof                                   false
% 2.81/0.99  --time_out_real                         305.
% 2.81/0.99  --time_out_virtual                      -1.
% 2.81/0.99  --symbol_type_check                     false
% 2.81/0.99  --clausify_out                          false
% 2.81/0.99  --sig_cnt_out                           false
% 2.81/0.99  --trig_cnt_out                          false
% 2.81/0.99  --trig_cnt_out_tolerance                1.
% 2.81/0.99  --trig_cnt_out_sk_spl                   false
% 2.81/0.99  --abstr_cl_out                          false
% 2.81/0.99  
% 2.81/0.99  ------ Global Options
% 2.81/0.99  
% 2.81/0.99  --schedule                              default
% 2.81/0.99  --add_important_lit                     false
% 2.81/0.99  --prop_solver_per_cl                    1000
% 2.81/0.99  --min_unsat_core                        false
% 2.81/0.99  --soft_assumptions                      false
% 2.81/0.99  --soft_lemma_size                       3
% 2.81/0.99  --prop_impl_unit_size                   0
% 2.81/0.99  --prop_impl_unit                        []
% 2.81/0.99  --share_sel_clauses                     true
% 2.81/0.99  --reset_solvers                         false
% 2.81/0.99  --bc_imp_inh                            [conj_cone]
% 2.81/0.99  --conj_cone_tolerance                   3.
% 2.81/0.99  --extra_neg_conj                        none
% 2.81/0.99  --large_theory_mode                     true
% 2.81/0.99  --prolific_symb_bound                   200
% 2.81/0.99  --lt_threshold                          2000
% 2.81/0.99  --clause_weak_htbl                      true
% 2.81/0.99  --gc_record_bc_elim                     false
% 2.81/0.99  
% 2.81/0.99  ------ Preprocessing Options
% 2.81/0.99  
% 2.81/0.99  --preprocessing_flag                    true
% 2.81/0.99  --time_out_prep_mult                    0.1
% 2.81/0.99  --splitting_mode                        input
% 2.81/0.99  --splitting_grd                         true
% 2.81/0.99  --splitting_cvd                         false
% 2.81/0.99  --splitting_cvd_svl                     false
% 2.81/0.99  --splitting_nvd                         32
% 2.81/0.99  --sub_typing                            true
% 2.81/0.99  --prep_gs_sim                           true
% 2.81/0.99  --prep_unflatten                        true
% 2.81/0.99  --prep_res_sim                          true
% 2.81/0.99  --prep_upred                            true
% 2.81/0.99  --prep_sem_filter                       exhaustive
% 2.81/0.99  --prep_sem_filter_out                   false
% 2.81/0.99  --pred_elim                             true
% 2.81/0.99  --res_sim_input                         true
% 2.81/0.99  --eq_ax_congr_red                       true
% 2.81/0.99  --pure_diseq_elim                       true
% 2.81/0.99  --brand_transform                       false
% 2.81/0.99  --non_eq_to_eq                          false
% 2.81/0.99  --prep_def_merge                        true
% 2.81/0.99  --prep_def_merge_prop_impl              false
% 2.81/0.99  --prep_def_merge_mbd                    true
% 2.81/0.99  --prep_def_merge_tr_red                 false
% 2.81/0.99  --prep_def_merge_tr_cl                  false
% 2.81/0.99  --smt_preprocessing                     true
% 2.81/0.99  --smt_ac_axioms                         fast
% 2.81/0.99  --preprocessed_out                      false
% 2.81/0.99  --preprocessed_stats                    false
% 2.81/0.99  
% 2.81/0.99  ------ Abstraction refinement Options
% 2.81/0.99  
% 2.81/0.99  --abstr_ref                             []
% 2.81/0.99  --abstr_ref_prep                        false
% 2.81/0.99  --abstr_ref_until_sat                   false
% 2.81/0.99  --abstr_ref_sig_restrict                funpre
% 2.81/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.81/0.99  --abstr_ref_under                       []
% 2.81/0.99  
% 2.81/0.99  ------ SAT Options
% 2.81/0.99  
% 2.81/0.99  --sat_mode                              false
% 2.81/0.99  --sat_fm_restart_options                ""
% 2.81/0.99  --sat_gr_def                            false
% 2.81/0.99  --sat_epr_types                         true
% 2.81/0.99  --sat_non_cyclic_types                  false
% 2.81/0.99  --sat_finite_models                     false
% 2.81/0.99  --sat_fm_lemmas                         false
% 2.81/0.99  --sat_fm_prep                           false
% 2.81/0.99  --sat_fm_uc_incr                        true
% 2.81/0.99  --sat_out_model                         small
% 2.81/0.99  --sat_out_clauses                       false
% 2.81/0.99  
% 2.81/0.99  ------ QBF Options
% 2.81/0.99  
% 2.81/0.99  --qbf_mode                              false
% 2.81/0.99  --qbf_elim_univ                         false
% 2.81/0.99  --qbf_dom_inst                          none
% 2.81/0.99  --qbf_dom_pre_inst                      false
% 2.81/0.99  --qbf_sk_in                             false
% 2.81/0.99  --qbf_pred_elim                         true
% 2.81/0.99  --qbf_split                             512
% 2.81/0.99  
% 2.81/0.99  ------ BMC1 Options
% 2.81/0.99  
% 2.81/0.99  --bmc1_incremental                      false
% 2.81/0.99  --bmc1_axioms                           reachable_all
% 2.81/0.99  --bmc1_min_bound                        0
% 2.81/0.99  --bmc1_max_bound                        -1
% 2.81/0.99  --bmc1_max_bound_default                -1
% 2.81/0.99  --bmc1_symbol_reachability              true
% 2.81/0.99  --bmc1_property_lemmas                  false
% 2.81/0.99  --bmc1_k_induction                      false
% 2.81/0.99  --bmc1_non_equiv_states                 false
% 2.81/0.99  --bmc1_deadlock                         false
% 2.81/0.99  --bmc1_ucm                              false
% 2.81/0.99  --bmc1_add_unsat_core                   none
% 2.81/0.99  --bmc1_unsat_core_children              false
% 2.81/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.81/0.99  --bmc1_out_stat                         full
% 2.81/0.99  --bmc1_ground_init                      false
% 2.81/0.99  --bmc1_pre_inst_next_state              false
% 2.81/0.99  --bmc1_pre_inst_state                   false
% 2.81/0.99  --bmc1_pre_inst_reach_state             false
% 2.81/0.99  --bmc1_out_unsat_core                   false
% 2.81/0.99  --bmc1_aig_witness_out                  false
% 2.81/0.99  --bmc1_verbose                          false
% 2.81/0.99  --bmc1_dump_clauses_tptp                false
% 2.81/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.81/0.99  --bmc1_dump_file                        -
% 2.81/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.81/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.81/0.99  --bmc1_ucm_extend_mode                  1
% 2.81/0.99  --bmc1_ucm_init_mode                    2
% 2.81/0.99  --bmc1_ucm_cone_mode                    none
% 2.81/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.81/0.99  --bmc1_ucm_relax_model                  4
% 2.81/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.81/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.81/0.99  --bmc1_ucm_layered_model                none
% 2.81/0.99  --bmc1_ucm_max_lemma_size               10
% 2.81/0.99  
% 2.81/0.99  ------ AIG Options
% 2.81/0.99  
% 2.81/0.99  --aig_mode                              false
% 2.81/0.99  
% 2.81/0.99  ------ Instantiation Options
% 2.81/0.99  
% 2.81/0.99  --instantiation_flag                    true
% 2.81/0.99  --inst_sos_flag                         false
% 2.81/0.99  --inst_sos_phase                        true
% 2.81/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.81/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.81/0.99  --inst_lit_sel_side                     num_symb
% 2.81/0.99  --inst_solver_per_active                1400
% 2.81/0.99  --inst_solver_calls_frac                1.
% 2.81/0.99  --inst_passive_queue_type               priority_queues
% 2.81/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.81/0.99  --inst_passive_queues_freq              [25;2]
% 2.81/0.99  --inst_dismatching                      true
% 2.81/0.99  --inst_eager_unprocessed_to_passive     true
% 2.81/0.99  --inst_prop_sim_given                   true
% 2.81/0.99  --inst_prop_sim_new                     false
% 2.81/0.99  --inst_subs_new                         false
% 2.81/0.99  --inst_eq_res_simp                      false
% 2.81/0.99  --inst_subs_given                       false
% 2.81/0.99  --inst_orphan_elimination               true
% 2.81/0.99  --inst_learning_loop_flag               true
% 2.81/0.99  --inst_learning_start                   3000
% 2.81/0.99  --inst_learning_factor                  2
% 2.81/0.99  --inst_start_prop_sim_after_learn       3
% 2.81/0.99  --inst_sel_renew                        solver
% 2.81/0.99  --inst_lit_activity_flag                true
% 2.81/0.99  --inst_restr_to_given                   false
% 2.81/0.99  --inst_activity_threshold               500
% 2.81/0.99  --inst_out_proof                        true
% 2.81/0.99  
% 2.81/0.99  ------ Resolution Options
% 2.81/0.99  
% 2.81/0.99  --resolution_flag                       true
% 2.81/0.99  --res_lit_sel                           adaptive
% 2.81/0.99  --res_lit_sel_side                      none
% 2.81/0.99  --res_ordering                          kbo
% 2.81/0.99  --res_to_prop_solver                    active
% 2.81/0.99  --res_prop_simpl_new                    false
% 2.81/0.99  --res_prop_simpl_given                  true
% 2.81/0.99  --res_passive_queue_type                priority_queues
% 2.81/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.81/0.99  --res_passive_queues_freq               [15;5]
% 2.81/0.99  --res_forward_subs                      full
% 2.81/0.99  --res_backward_subs                     full
% 2.81/0.99  --res_forward_subs_resolution           true
% 2.81/0.99  --res_backward_subs_resolution          true
% 2.81/0.99  --res_orphan_elimination                true
% 2.81/0.99  --res_time_limit                        2.
% 2.81/0.99  --res_out_proof                         true
% 2.81/0.99  
% 2.81/0.99  ------ Superposition Options
% 2.81/0.99  
% 2.81/0.99  --superposition_flag                    true
% 2.81/0.99  --sup_passive_queue_type                priority_queues
% 2.81/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.81/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.81/0.99  --demod_completeness_check              fast
% 2.81/0.99  --demod_use_ground                      true
% 2.81/0.99  --sup_to_prop_solver                    passive
% 2.81/0.99  --sup_prop_simpl_new                    true
% 2.81/0.99  --sup_prop_simpl_given                  true
% 2.81/0.99  --sup_fun_splitting                     false
% 2.81/0.99  --sup_smt_interval                      50000
% 2.81/0.99  
% 2.81/0.99  ------ Superposition Simplification Setup
% 2.81/0.99  
% 2.81/0.99  --sup_indices_passive                   []
% 2.81/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.81/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/0.99  --sup_full_bw                           [BwDemod]
% 2.81/0.99  --sup_immed_triv                        [TrivRules]
% 2.81/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.81/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/0.99  --sup_immed_bw_main                     []
% 2.81/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.81/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/0.99  
% 2.81/0.99  ------ Combination Options
% 2.81/0.99  
% 2.81/0.99  --comb_res_mult                         3
% 2.81/0.99  --comb_sup_mult                         2
% 2.81/0.99  --comb_inst_mult                        10
% 2.81/0.99  
% 2.81/0.99  ------ Debug Options
% 2.81/0.99  
% 2.81/0.99  --dbg_backtrace                         false
% 2.81/0.99  --dbg_dump_prop_clauses                 false
% 2.81/0.99  --dbg_dump_prop_clauses_file            -
% 2.81/0.99  --dbg_out_stat                          false
% 2.81/0.99  ------ Parsing...
% 2.81/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.81/0.99  
% 2.81/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.81/0.99  
% 2.81/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.81/0.99  
% 2.81/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.81/0.99  ------ Proving...
% 2.81/0.99  ------ Problem Properties 
% 2.81/0.99  
% 2.81/0.99  
% 2.81/0.99  clauses                                 20
% 2.81/0.99  conjectures                             4
% 2.81/0.99  EPR                                     7
% 2.81/0.99  Horn                                    13
% 2.81/0.99  unary                                   3
% 2.81/0.99  binary                                  12
% 2.81/0.99  lits                                    46
% 2.81/0.99  lits eq                                 3
% 2.81/0.99  fd_pure                                 0
% 2.81/0.99  fd_pseudo                               0
% 2.81/0.99  fd_cond                                 0
% 2.81/0.99  fd_pseudo_cond                          1
% 2.81/0.99  AC symbols                              0
% 2.81/0.99  
% 2.81/0.99  ------ Schedule dynamic 5 is on 
% 2.81/0.99  
% 2.81/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.81/0.99  
% 2.81/0.99  
% 2.81/0.99  ------ 
% 2.81/0.99  Current options:
% 2.81/0.99  ------ 
% 2.81/0.99  
% 2.81/0.99  ------ Input Options
% 2.81/0.99  
% 2.81/0.99  --out_options                           all
% 2.81/0.99  --tptp_safe_out                         true
% 2.81/0.99  --problem_path                          ""
% 2.81/0.99  --include_path                          ""
% 2.81/0.99  --clausifier                            res/vclausify_rel
% 2.81/0.99  --clausifier_options                    --mode clausify
% 2.81/0.99  --stdin                                 false
% 2.81/0.99  --stats_out                             all
% 2.81/0.99  
% 2.81/0.99  ------ General Options
% 2.81/0.99  
% 2.81/0.99  --fof                                   false
% 2.81/0.99  --time_out_real                         305.
% 2.81/0.99  --time_out_virtual                      -1.
% 2.81/0.99  --symbol_type_check                     false
% 2.81/0.99  --clausify_out                          false
% 2.81/0.99  --sig_cnt_out                           false
% 2.81/0.99  --trig_cnt_out                          false
% 2.81/0.99  --trig_cnt_out_tolerance                1.
% 2.81/0.99  --trig_cnt_out_sk_spl                   false
% 2.81/0.99  --abstr_cl_out                          false
% 2.81/0.99  
% 2.81/0.99  ------ Global Options
% 2.81/0.99  
% 2.81/0.99  --schedule                              default
% 2.81/0.99  --add_important_lit                     false
% 2.81/0.99  --prop_solver_per_cl                    1000
% 2.81/0.99  --min_unsat_core                        false
% 2.81/0.99  --soft_assumptions                      false
% 2.81/0.99  --soft_lemma_size                       3
% 2.81/0.99  --prop_impl_unit_size                   0
% 2.81/0.99  --prop_impl_unit                        []
% 2.81/0.99  --share_sel_clauses                     true
% 2.81/0.99  --reset_solvers                         false
% 2.81/0.99  --bc_imp_inh                            [conj_cone]
% 2.81/0.99  --conj_cone_tolerance                   3.
% 2.81/0.99  --extra_neg_conj                        none
% 2.81/0.99  --large_theory_mode                     true
% 2.81/0.99  --prolific_symb_bound                   200
% 2.81/0.99  --lt_threshold                          2000
% 2.81/0.99  --clause_weak_htbl                      true
% 2.81/0.99  --gc_record_bc_elim                     false
% 2.81/0.99  
% 2.81/0.99  ------ Preprocessing Options
% 2.81/0.99  
% 2.81/0.99  --preprocessing_flag                    true
% 2.81/0.99  --time_out_prep_mult                    0.1
% 2.81/0.99  --splitting_mode                        input
% 2.81/0.99  --splitting_grd                         true
% 2.81/0.99  --splitting_cvd                         false
% 2.81/0.99  --splitting_cvd_svl                     false
% 2.81/0.99  --splitting_nvd                         32
% 2.81/0.99  --sub_typing                            true
% 2.81/0.99  --prep_gs_sim                           true
% 2.81/0.99  --prep_unflatten                        true
% 2.81/0.99  --prep_res_sim                          true
% 2.81/0.99  --prep_upred                            true
% 2.81/0.99  --prep_sem_filter                       exhaustive
% 2.81/0.99  --prep_sem_filter_out                   false
% 2.81/0.99  --pred_elim                             true
% 2.81/0.99  --res_sim_input                         true
% 2.81/0.99  --eq_ax_congr_red                       true
% 2.81/0.99  --pure_diseq_elim                       true
% 2.81/0.99  --brand_transform                       false
% 2.81/0.99  --non_eq_to_eq                          false
% 2.81/0.99  --prep_def_merge                        true
% 2.81/0.99  --prep_def_merge_prop_impl              false
% 2.81/0.99  --prep_def_merge_mbd                    true
% 2.81/0.99  --prep_def_merge_tr_red                 false
% 2.81/0.99  --prep_def_merge_tr_cl                  false
% 2.81/0.99  --smt_preprocessing                     true
% 2.81/0.99  --smt_ac_axioms                         fast
% 2.81/0.99  --preprocessed_out                      false
% 2.81/0.99  --preprocessed_stats                    false
% 2.81/0.99  
% 2.81/0.99  ------ Abstraction refinement Options
% 2.81/0.99  
% 2.81/0.99  --abstr_ref                             []
% 2.81/0.99  --abstr_ref_prep                        false
% 2.81/0.99  --abstr_ref_until_sat                   false
% 2.81/0.99  --abstr_ref_sig_restrict                funpre
% 2.81/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.81/0.99  --abstr_ref_under                       []
% 2.81/0.99  
% 2.81/0.99  ------ SAT Options
% 2.81/0.99  
% 2.81/0.99  --sat_mode                              false
% 2.81/0.99  --sat_fm_restart_options                ""
% 2.81/0.99  --sat_gr_def                            false
% 2.81/0.99  --sat_epr_types                         true
% 2.81/0.99  --sat_non_cyclic_types                  false
% 2.81/0.99  --sat_finite_models                     false
% 2.81/0.99  --sat_fm_lemmas                         false
% 2.81/0.99  --sat_fm_prep                           false
% 2.81/0.99  --sat_fm_uc_incr                        true
% 2.81/0.99  --sat_out_model                         small
% 2.81/0.99  --sat_out_clauses                       false
% 2.81/0.99  
% 2.81/0.99  ------ QBF Options
% 2.81/0.99  
% 2.81/0.99  --qbf_mode                              false
% 2.81/0.99  --qbf_elim_univ                         false
% 2.81/0.99  --qbf_dom_inst                          none
% 2.81/0.99  --qbf_dom_pre_inst                      false
% 2.81/0.99  --qbf_sk_in                             false
% 2.81/0.99  --qbf_pred_elim                         true
% 2.81/0.99  --qbf_split                             512
% 2.81/0.99  
% 2.81/0.99  ------ BMC1 Options
% 2.81/0.99  
% 2.81/0.99  --bmc1_incremental                      false
% 2.81/0.99  --bmc1_axioms                           reachable_all
% 2.81/0.99  --bmc1_min_bound                        0
% 2.81/0.99  --bmc1_max_bound                        -1
% 2.81/0.99  --bmc1_max_bound_default                -1
% 2.81/0.99  --bmc1_symbol_reachability              true
% 2.81/0.99  --bmc1_property_lemmas                  false
% 2.81/0.99  --bmc1_k_induction                      false
% 2.81/0.99  --bmc1_non_equiv_states                 false
% 2.81/0.99  --bmc1_deadlock                         false
% 2.81/0.99  --bmc1_ucm                              false
% 2.81/0.99  --bmc1_add_unsat_core                   none
% 2.81/0.99  --bmc1_unsat_core_children              false
% 2.81/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.81/0.99  --bmc1_out_stat                         full
% 2.81/0.99  --bmc1_ground_init                      false
% 2.81/0.99  --bmc1_pre_inst_next_state              false
% 2.81/0.99  --bmc1_pre_inst_state                   false
% 2.81/0.99  --bmc1_pre_inst_reach_state             false
% 2.81/0.99  --bmc1_out_unsat_core                   false
% 2.81/0.99  --bmc1_aig_witness_out                  false
% 2.81/0.99  --bmc1_verbose                          false
% 2.81/0.99  --bmc1_dump_clauses_tptp                false
% 2.81/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.81/0.99  --bmc1_dump_file                        -
% 2.81/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.81/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.81/0.99  --bmc1_ucm_extend_mode                  1
% 2.81/0.99  --bmc1_ucm_init_mode                    2
% 2.81/0.99  --bmc1_ucm_cone_mode                    none
% 2.81/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.81/0.99  --bmc1_ucm_relax_model                  4
% 2.81/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.81/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.81/0.99  --bmc1_ucm_layered_model                none
% 2.81/0.99  --bmc1_ucm_max_lemma_size               10
% 2.81/0.99  
% 2.81/0.99  ------ AIG Options
% 2.81/0.99  
% 2.81/0.99  --aig_mode                              false
% 2.81/0.99  
% 2.81/0.99  ------ Instantiation Options
% 2.81/0.99  
% 2.81/0.99  --instantiation_flag                    true
% 2.81/0.99  --inst_sos_flag                         false
% 2.81/0.99  --inst_sos_phase                        true
% 2.81/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.81/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.81/0.99  --inst_lit_sel_side                     none
% 2.81/0.99  --inst_solver_per_active                1400
% 2.81/0.99  --inst_solver_calls_frac                1.
% 2.81/0.99  --inst_passive_queue_type               priority_queues
% 2.81/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.81/0.99  --inst_passive_queues_freq              [25;2]
% 2.81/0.99  --inst_dismatching                      true
% 2.81/0.99  --inst_eager_unprocessed_to_passive     true
% 2.81/0.99  --inst_prop_sim_given                   true
% 2.81/0.99  --inst_prop_sim_new                     false
% 2.81/0.99  --inst_subs_new                         false
% 2.81/0.99  --inst_eq_res_simp                      false
% 2.81/0.99  --inst_subs_given                       false
% 2.81/0.99  --inst_orphan_elimination               true
% 2.81/0.99  --inst_learning_loop_flag               true
% 2.81/0.99  --inst_learning_start                   3000
% 2.81/0.99  --inst_learning_factor                  2
% 2.81/0.99  --inst_start_prop_sim_after_learn       3
% 2.81/0.99  --inst_sel_renew                        solver
% 2.81/0.99  --inst_lit_activity_flag                true
% 2.81/0.99  --inst_restr_to_given                   false
% 2.81/0.99  --inst_activity_threshold               500
% 2.81/0.99  --inst_out_proof                        true
% 2.81/0.99  
% 2.81/0.99  ------ Resolution Options
% 2.81/0.99  
% 2.81/0.99  --resolution_flag                       false
% 2.81/0.99  --res_lit_sel                           adaptive
% 2.81/0.99  --res_lit_sel_side                      none
% 2.81/0.99  --res_ordering                          kbo
% 2.81/0.99  --res_to_prop_solver                    active
% 2.81/0.99  --res_prop_simpl_new                    false
% 2.81/0.99  --res_prop_simpl_given                  true
% 2.81/0.99  --res_passive_queue_type                priority_queues
% 2.81/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.81/0.99  --res_passive_queues_freq               [15;5]
% 2.81/0.99  --res_forward_subs                      full
% 2.81/0.99  --res_backward_subs                     full
% 2.81/0.99  --res_forward_subs_resolution           true
% 2.81/0.99  --res_backward_subs_resolution          true
% 2.81/0.99  --res_orphan_elimination                true
% 2.81/0.99  --res_time_limit                        2.
% 2.81/0.99  --res_out_proof                         true
% 2.81/0.99  
% 2.81/0.99  ------ Superposition Options
% 2.81/0.99  
% 2.81/0.99  --superposition_flag                    true
% 2.81/0.99  --sup_passive_queue_type                priority_queues
% 2.81/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.81/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.81/0.99  --demod_completeness_check              fast
% 2.81/0.99  --demod_use_ground                      true
% 2.81/0.99  --sup_to_prop_solver                    passive
% 2.81/0.99  --sup_prop_simpl_new                    true
% 2.81/0.99  --sup_prop_simpl_given                  true
% 2.81/0.99  --sup_fun_splitting                     false
% 2.81/0.99  --sup_smt_interval                      50000
% 2.81/0.99  
% 2.81/0.99  ------ Superposition Simplification Setup
% 2.81/0.99  
% 2.81/0.99  --sup_indices_passive                   []
% 2.81/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.81/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/0.99  --sup_full_bw                           [BwDemod]
% 2.81/0.99  --sup_immed_triv                        [TrivRules]
% 2.81/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.81/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/0.99  --sup_immed_bw_main                     []
% 2.81/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.81/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/0.99  
% 2.81/0.99  ------ Combination Options
% 2.81/0.99  
% 2.81/0.99  --comb_res_mult                         3
% 2.81/0.99  --comb_sup_mult                         2
% 2.81/0.99  --comb_inst_mult                        10
% 2.81/0.99  
% 2.81/0.99  ------ Debug Options
% 2.81/0.99  
% 2.81/0.99  --dbg_backtrace                         false
% 2.81/0.99  --dbg_dump_prop_clauses                 false
% 2.81/0.99  --dbg_dump_prop_clauses_file            -
% 2.81/0.99  --dbg_out_stat                          false
% 2.81/0.99  
% 2.81/0.99  
% 2.81/0.99  
% 2.81/0.99  
% 2.81/0.99  ------ Proving...
% 2.81/0.99  
% 2.81/0.99  
% 2.81/0.99  % SZS status Theorem for theBenchmark.p
% 2.81/0.99  
% 2.81/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.81/0.99  
% 2.81/0.99  fof(f16,conjecture,(
% 2.81/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f17,negated_conjecture,(
% 2.81/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 2.81/0.99    inference(negated_conjecture,[],[f16])).
% 2.81/0.99  
% 2.81/0.99  fof(f37,plain,(
% 2.81/0.99    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.81/0.99    inference(ennf_transformation,[],[f17])).
% 2.81/0.99  
% 2.81/0.99  fof(f38,plain,(
% 2.81/0.99    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.81/0.99    inference(flattening,[],[f37])).
% 2.81/0.99  
% 2.81/0.99  fof(f51,plain,(
% 2.81/0.99    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.81/0.99    inference(nnf_transformation,[],[f38])).
% 2.81/0.99  
% 2.81/0.99  fof(f52,plain,(
% 2.81/0.99    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.81/0.99    inference(flattening,[],[f51])).
% 2.81/0.99  
% 2.81/0.99  fof(f54,plain,(
% 2.81/0.99    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,X0)) & (v1_zfmisc_1(sK4) | v2_tex_2(sK4,X0)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK4))) )),
% 2.81/0.99    introduced(choice_axiom,[])).
% 2.81/0.99  
% 2.81/0.99  fof(f53,plain,(
% 2.81/0.99    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK3)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 2.81/0.99    introduced(choice_axiom,[])).
% 2.81/0.99  
% 2.81/0.99  fof(f55,plain,(
% 2.81/0.99    ((~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)) & (v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 2.81/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f52,f54,f53])).
% 2.81/0.99  
% 2.81/0.99  fof(f86,plain,(
% 2.81/0.99    v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)),
% 2.81/0.99    inference(cnf_transformation,[],[f55])).
% 2.81/0.99  
% 2.81/0.99  fof(f85,plain,(
% 2.81/0.99    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.81/0.99    inference(cnf_transformation,[],[f55])).
% 2.81/0.99  
% 2.81/0.99  fof(f14,axiom,(
% 2.81/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f18,plain,(
% 2.81/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 2.81/0.99    inference(pure_predicate_removal,[],[f14])).
% 2.81/0.99  
% 2.81/0.99  fof(f33,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.81/0.99    inference(ennf_transformation,[],[f18])).
% 2.81/0.99  
% 2.81/0.99  fof(f34,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.81/0.99    inference(flattening,[],[f33])).
% 2.81/0.99  
% 2.81/0.99  fof(f49,plain,(
% 2.81/0.99    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))))),
% 2.81/0.99    introduced(choice_axiom,[])).
% 2.81/0.99  
% 2.81/0.99  fof(f50,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.81/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f49])).
% 2.81/0.99  
% 2.81/0.99  fof(f78,plain,(
% 2.81/0.99    ( ! [X0,X1] : (u1_struct_0(sK2(X0,X1)) = X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f50])).
% 2.81/0.99  
% 2.81/0.99  fof(f81,plain,(
% 2.81/0.99    v2_pre_topc(sK3)),
% 2.81/0.99    inference(cnf_transformation,[],[f55])).
% 2.81/0.99  
% 2.81/0.99  fof(f80,plain,(
% 2.81/0.99    ~v2_struct_0(sK3)),
% 2.81/0.99    inference(cnf_transformation,[],[f55])).
% 2.81/0.99  
% 2.81/0.99  fof(f83,plain,(
% 2.81/0.99    l1_pre_topc(sK3)),
% 2.81/0.99    inference(cnf_transformation,[],[f55])).
% 2.81/0.99  
% 2.81/0.99  fof(f84,plain,(
% 2.81/0.99    ~v1_xboole_0(sK4)),
% 2.81/0.99    inference(cnf_transformation,[],[f55])).
% 2.81/0.99  
% 2.81/0.99  fof(f1,axiom,(
% 2.81/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f39,plain,(
% 2.81/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.81/0.99    inference(nnf_transformation,[],[f1])).
% 2.81/0.99  
% 2.81/0.99  fof(f40,plain,(
% 2.81/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.81/0.99    inference(rectify,[],[f39])).
% 2.81/0.99  
% 2.81/0.99  fof(f41,plain,(
% 2.81/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.81/0.99    introduced(choice_axiom,[])).
% 2.81/0.99  
% 2.81/0.99  fof(f42,plain,(
% 2.81/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.81/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 2.81/0.99  
% 2.81/0.99  fof(f57,plain,(
% 2.81/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f42])).
% 2.81/0.99  
% 2.81/0.99  fof(f4,axiom,(
% 2.81/0.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f47,plain,(
% 2.81/0.99    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.81/0.99    inference(nnf_transformation,[],[f4])).
% 2.81/0.99  
% 2.81/0.99  fof(f63,plain,(
% 2.81/0.99    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f47])).
% 2.81/0.99  
% 2.81/0.99  fof(f13,axiom,(
% 2.81/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f31,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 2.81/0.99    inference(ennf_transformation,[],[f13])).
% 2.81/0.99  
% 2.81/0.99  fof(f32,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.81/0.99    inference(flattening,[],[f31])).
% 2.81/0.99  
% 2.81/0.99  fof(f74,plain,(
% 2.81/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f32])).
% 2.81/0.99  
% 2.81/0.99  fof(f3,axiom,(
% 2.81/0.99    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f61,plain,(
% 2.81/0.99    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 2.81/0.99    inference(cnf_transformation,[],[f3])).
% 2.81/0.99  
% 2.81/0.99  fof(f56,plain,(
% 2.81/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f42])).
% 2.81/0.99  
% 2.81/0.99  fof(f76,plain,(
% 2.81/0.99    ( ! [X0,X1] : (v1_tdlat_3(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f50])).
% 2.81/0.99  
% 2.81/0.99  fof(f75,plain,(
% 2.81/0.99    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f50])).
% 2.81/0.99  
% 2.81/0.99  fof(f77,plain,(
% 2.81/0.99    ( ! [X0,X1] : (m1_pre_topc(sK2(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f50])).
% 2.81/0.99  
% 2.81/0.99  fof(f12,axiom,(
% 2.81/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((~v7_struct_0(X1) & ~v2_struct_0(X1)) => (~v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f29,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : (((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.81/0.99    inference(ennf_transformation,[],[f12])).
% 2.81/0.99  
% 2.81/0.99  fof(f30,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : ((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.81/0.99    inference(flattening,[],[f29])).
% 2.81/0.99  
% 2.81/0.99  fof(f73,plain,(
% 2.81/0.99    ( ! [X0,X1] : (~v1_tdlat_3(X1) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f30])).
% 2.81/0.99  
% 2.81/0.99  fof(f7,axiom,(
% 2.81/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f21,plain,(
% 2.81/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.81/0.99    inference(ennf_transformation,[],[f7])).
% 2.81/0.99  
% 2.81/0.99  fof(f67,plain,(
% 2.81/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f21])).
% 2.81/0.99  
% 2.81/0.99  fof(f9,axiom,(
% 2.81/0.99    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f23,plain,(
% 2.81/0.99    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 2.81/0.99    inference(ennf_transformation,[],[f9])).
% 2.81/0.99  
% 2.81/0.99  fof(f24,plain,(
% 2.81/0.99    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 2.81/0.99    inference(flattening,[],[f23])).
% 2.81/0.99  
% 2.81/0.99  fof(f69,plain,(
% 2.81/0.99    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f24])).
% 2.81/0.99  
% 2.81/0.99  fof(f8,axiom,(
% 2.81/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f22,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.81/0.99    inference(ennf_transformation,[],[f8])).
% 2.81/0.99  
% 2.81/0.99  fof(f68,plain,(
% 2.81/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f22])).
% 2.81/0.99  
% 2.81/0.99  fof(f11,axiom,(
% 2.81/0.99    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f27,plain,(
% 2.81/0.99    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 2.81/0.99    inference(ennf_transformation,[],[f11])).
% 2.81/0.99  
% 2.81/0.99  fof(f28,plain,(
% 2.81/0.99    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 2.81/0.99    inference(flattening,[],[f27])).
% 2.81/0.99  
% 2.81/0.99  fof(f71,plain,(
% 2.81/0.99    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f28])).
% 2.81/0.99  
% 2.81/0.99  fof(f82,plain,(
% 2.81/0.99    v2_tdlat_3(sK3)),
% 2.81/0.99    inference(cnf_transformation,[],[f55])).
% 2.81/0.99  
% 2.81/0.99  fof(f6,axiom,(
% 2.81/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f48,plain,(
% 2.81/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.81/0.99    inference(nnf_transformation,[],[f6])).
% 2.81/0.99  
% 2.81/0.99  fof(f65,plain,(
% 2.81/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.81/0.99    inference(cnf_transformation,[],[f48])).
% 2.81/0.99  
% 2.81/0.99  fof(f2,axiom,(
% 2.81/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f19,plain,(
% 2.81/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.81/0.99    inference(ennf_transformation,[],[f2])).
% 2.81/0.99  
% 2.81/0.99  fof(f43,plain,(
% 2.81/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.81/0.99    inference(nnf_transformation,[],[f19])).
% 2.81/0.99  
% 2.81/0.99  fof(f44,plain,(
% 2.81/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.81/0.99    inference(rectify,[],[f43])).
% 2.81/0.99  
% 2.81/0.99  fof(f45,plain,(
% 2.81/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.81/0.99    introduced(choice_axiom,[])).
% 2.81/0.99  
% 2.81/0.99  fof(f46,plain,(
% 2.81/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.81/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f45])).
% 2.81/0.99  
% 2.81/0.99  fof(f58,plain,(
% 2.81/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f46])).
% 2.81/0.99  
% 2.81/0.99  fof(f5,axiom,(
% 2.81/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f20,plain,(
% 2.81/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.81/0.99    inference(ennf_transformation,[],[f5])).
% 2.81/0.99  
% 2.81/0.99  fof(f64,plain,(
% 2.81/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f20])).
% 2.81/0.99  
% 2.81/0.99  fof(f10,axiom,(
% 2.81/0.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f25,plain,(
% 2.81/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.81/0.99    inference(ennf_transformation,[],[f10])).
% 2.81/0.99  
% 2.81/0.99  fof(f26,plain,(
% 2.81/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.81/0.99    inference(flattening,[],[f25])).
% 2.81/0.99  
% 2.81/0.99  fof(f70,plain,(
% 2.81/0.99    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f26])).
% 2.81/0.99  
% 2.81/0.99  fof(f15,axiom,(
% 2.81/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f35,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.81/0.99    inference(ennf_transformation,[],[f15])).
% 2.81/0.99  
% 2.81/0.99  fof(f36,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.81/0.99    inference(flattening,[],[f35])).
% 2.81/0.99  
% 2.81/0.99  fof(f79,plain,(
% 2.81/0.99    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f36])).
% 2.81/0.99  
% 2.81/0.99  fof(f87,plain,(
% 2.81/0.99    ~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)),
% 2.81/0.99    inference(cnf_transformation,[],[f55])).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2427,plain,
% 2.81/0.99      ( ~ v1_zfmisc_1(X0) | v1_zfmisc_1(X1) | X1 != X0 ),
% 2.81/0.99      theory(equality) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_4339,plain,
% 2.81/0.99      ( v1_zfmisc_1(X0)
% 2.81/0.99      | ~ v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
% 2.81/0.99      | X0 != u1_struct_0(sK2(sK3,sK4)) ),
% 2.81/0.99      inference(instantiation,[status(thm)],[c_2427]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_6245,plain,
% 2.81/0.99      ( ~ v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
% 2.81/0.99      | v1_zfmisc_1(sK4)
% 2.81/0.99      | sK4 != u1_struct_0(sK2(sK3,sK4)) ),
% 2.81/0.99      inference(instantiation,[status(thm)],[c_4339]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_25,negated_conjecture,
% 2.81/0.99      ( v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) ),
% 2.81/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2971,plain,
% 2.81/0.99      ( v2_tex_2(sK4,sK3) = iProver_top
% 2.81/0.99      | v1_zfmisc_1(sK4) = iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_26,negated_conjecture,
% 2.81/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.81/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2970,plain,
% 2.81/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_19,plain,
% 2.81/0.99      ( ~ v2_tex_2(X0,X1)
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | ~ v2_pre_topc(X1)
% 2.81/0.99      | ~ l1_pre_topc(X1)
% 2.81/0.99      | v1_xboole_0(X0)
% 2.81/0.99      | u1_struct_0(sK2(X1,X0)) = X0 ),
% 2.81/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_30,negated_conjecture,
% 2.81/0.99      ( v2_pre_topc(sK3) ),
% 2.81/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_871,plain,
% 2.81/0.99      ( ~ v2_tex_2(X0,X1)
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | ~ l1_pre_topc(X1)
% 2.81/0.99      | v1_xboole_0(X0)
% 2.81/0.99      | u1_struct_0(sK2(X1,X0)) = X0
% 2.81/0.99      | sK3 != X1 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_872,plain,
% 2.81/0.99      ( ~ v2_tex_2(X0,sK3)
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.81/0.99      | v2_struct_0(sK3)
% 2.81/0.99      | ~ l1_pre_topc(sK3)
% 2.81/0.99      | v1_xboole_0(X0)
% 2.81/0.99      | u1_struct_0(sK2(sK3,X0)) = X0 ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_871]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_31,negated_conjecture,
% 2.81/0.99      ( ~ v2_struct_0(sK3) ),
% 2.81/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_28,negated_conjecture,
% 2.81/0.99      ( l1_pre_topc(sK3) ),
% 2.81/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_876,plain,
% 2.81/0.99      ( ~ v2_tex_2(X0,sK3)
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.81/0.99      | v1_xboole_0(X0)
% 2.81/0.99      | u1_struct_0(sK2(sK3,X0)) = X0 ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_872,c_31,c_28]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2967,plain,
% 2.81/0.99      ( u1_struct_0(sK2(sK3,X0)) = X0
% 2.81/0.99      | v2_tex_2(X0,sK3) != iProver_top
% 2.81/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.81/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_876]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_3159,plain,
% 2.81/0.99      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 2.81/0.99      | v2_tex_2(sK4,sK3) != iProver_top
% 2.81/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 2.81/0.99      inference(superposition,[status(thm)],[c_2970,c_2967]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_27,negated_conjecture,
% 2.81/0.99      ( ~ v1_xboole_0(sK4) ),
% 2.81/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_36,plain,
% 2.81/0.99      ( v1_xboole_0(sK4) != iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1292,plain,
% 2.81/0.99      ( ~ v2_tex_2(X0,sK3)
% 2.81/0.99      | v1_xboole_0(X0)
% 2.81/0.99      | u1_struct_0(sK2(sK3,X0)) = X0
% 2.81/0.99      | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3))
% 2.81/0.99      | sK4 != X0 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_876]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1293,plain,
% 2.81/0.99      ( ~ v2_tex_2(sK4,sK3)
% 2.81/0.99      | v1_xboole_0(sK4)
% 2.81/0.99      | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_1292]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1294,plain,
% 2.81/0.99      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 2.81/0.99      | v2_tex_2(sK4,sK3) != iProver_top
% 2.81/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_1293]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_3216,plain,
% 2.81/0.99      ( v2_tex_2(sK4,sK3) != iProver_top
% 2.81/0.99      | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_3159,c_36,c_1294]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_3217,plain,
% 2.81/0.99      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 2.81/0.99      | v2_tex_2(sK4,sK3) != iProver_top ),
% 2.81/0.99      inference(renaming,[status(thm)],[c_3216]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_3222,plain,
% 2.81/0.99      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 2.81/0.99      | v1_zfmisc_1(sK4) = iProver_top ),
% 2.81/0.99      inference(superposition,[status(thm)],[c_2971,c_3217]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_0,plain,
% 2.81/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.81/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2985,plain,
% 2.81/0.99      ( r2_hidden(sK0(X0),X0) = iProver_top
% 2.81/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_6,plain,
% 2.81/0.99      ( r1_tarski(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 2.81/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2979,plain,
% 2.81/0.99      ( r1_tarski(k1_tarski(X0),X1) = iProver_top
% 2.81/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_18,plain,
% 2.81/0.99      ( ~ r1_tarski(X0,X1)
% 2.81/0.99      | ~ v1_zfmisc_1(X1)
% 2.81/0.99      | v1_xboole_0(X0)
% 2.81/0.99      | v1_xboole_0(X1)
% 2.81/0.99      | X1 = X0 ),
% 2.81/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2973,plain,
% 2.81/0.99      ( X0 = X1
% 2.81/0.99      | r1_tarski(X1,X0) != iProver_top
% 2.81/0.99      | v1_zfmisc_1(X0) != iProver_top
% 2.81/0.99      | v1_xboole_0(X1) = iProver_top
% 2.81/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_3668,plain,
% 2.81/0.99      ( k1_tarski(X0) = X1
% 2.81/0.99      | r2_hidden(X0,X1) != iProver_top
% 2.81/0.99      | v1_zfmisc_1(X1) != iProver_top
% 2.81/0.99      | v1_xboole_0(X1) = iProver_top
% 2.81/0.99      | v1_xboole_0(k1_tarski(X0)) = iProver_top ),
% 2.81/0.99      inference(superposition,[status(thm)],[c_2979,c_2973]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_5,plain,
% 2.81/0.99      ( ~ v1_xboole_0(k1_tarski(X0)) ),
% 2.81/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_88,plain,
% 2.81/0.99      ( v1_xboole_0(k1_tarski(X0)) != iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1,plain,
% 2.81/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.81/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_98,plain,
% 2.81/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.81/0.99      | v1_xboole_0(X1) != iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_4737,plain,
% 2.81/0.99      ( k1_tarski(X0) = X1
% 2.81/0.99      | r2_hidden(X0,X1) != iProver_top
% 2.81/0.99      | v1_zfmisc_1(X1) != iProver_top ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_3668,c_88,c_98]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_4746,plain,
% 2.81/0.99      ( k1_tarski(sK0(X0)) = X0
% 2.81/0.99      | v1_zfmisc_1(X0) != iProver_top
% 2.81/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.81/0.99      inference(superposition,[status(thm)],[c_2985,c_4737]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_5441,plain,
% 2.81/0.99      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 2.81/0.99      | k1_tarski(sK0(sK4)) = sK4
% 2.81/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 2.81/0.99      inference(superposition,[status(thm)],[c_3222,c_4746]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_5488,plain,
% 2.81/0.99      ( v1_xboole_0(sK4)
% 2.81/0.99      | u1_struct_0(sK2(sK3,sK4)) = sK4
% 2.81/0.99      | k1_tarski(sK0(sK4)) = sK4 ),
% 2.81/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_5441]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_5562,plain,
% 2.81/0.99      ( k1_tarski(sK0(sK4)) = sK4 | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_5441,c_27,c_5488]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_5563,plain,
% 2.81/0.99      ( u1_struct_0(sK2(sK3,sK4)) = sK4 | k1_tarski(sK0(sK4)) = sK4 ),
% 2.81/0.99      inference(renaming,[status(thm)],[c_5562]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_21,plain,
% 2.81/0.99      ( ~ v2_tex_2(X0,X1)
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | v1_tdlat_3(sK2(X1,X0))
% 2.81/0.99      | ~ v2_pre_topc(X1)
% 2.81/0.99      | ~ l1_pre_topc(X1)
% 2.81/0.99      | v1_xboole_0(X0) ),
% 2.81/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_847,plain,
% 2.81/0.99      ( ~ v2_tex_2(X0,X1)
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | v1_tdlat_3(sK2(X1,X0))
% 2.81/0.99      | ~ l1_pre_topc(X1)
% 2.81/0.99      | v1_xboole_0(X0)
% 2.81/0.99      | sK3 != X1 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_30]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_848,plain,
% 2.81/0.99      ( ~ v2_tex_2(X0,sK3)
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.81/0.99      | v2_struct_0(sK3)
% 2.81/0.99      | v1_tdlat_3(sK2(sK3,X0))
% 2.81/0.99      | ~ l1_pre_topc(sK3)
% 2.81/0.99      | v1_xboole_0(X0) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_847]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_852,plain,
% 2.81/0.99      ( v1_tdlat_3(sK2(sK3,X0))
% 2.81/0.99      | ~ v2_tex_2(X0,sK3)
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.81/0.99      | v1_xboole_0(X0) ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_848,c_31,c_28]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_853,plain,
% 2.81/0.99      ( ~ v2_tex_2(X0,sK3)
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.81/0.99      | v1_tdlat_3(sK2(sK3,X0))
% 2.81/0.99      | v1_xboole_0(X0) ),
% 2.81/0.99      inference(renaming,[status(thm)],[c_852]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_22,plain,
% 2.81/0.99      ( ~ v2_tex_2(X0,X1)
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | ~ v2_struct_0(sK2(X1,X0))
% 2.81/0.99      | ~ v2_pre_topc(X1)
% 2.81/0.99      | ~ l1_pre_topc(X1)
% 2.81/0.99      | v1_xboole_0(X0) ),
% 2.81/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_823,plain,
% 2.81/0.99      ( ~ v2_tex_2(X0,X1)
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | ~ v2_struct_0(sK2(X1,X0))
% 2.81/0.99      | ~ l1_pre_topc(X1)
% 2.81/0.99      | v1_xboole_0(X0)
% 2.81/0.99      | sK3 != X1 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_30]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_824,plain,
% 2.81/0.99      ( ~ v2_tex_2(X0,sK3)
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.81/0.99      | ~ v2_struct_0(sK2(sK3,X0))
% 2.81/0.99      | v2_struct_0(sK3)
% 2.81/0.99      | ~ l1_pre_topc(sK3)
% 2.81/0.99      | v1_xboole_0(X0) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_823]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_828,plain,
% 2.81/0.99      ( ~ v2_tex_2(X0,sK3)
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.81/0.99      | ~ v2_struct_0(sK2(sK3,X0))
% 2.81/0.99      | v1_xboole_0(X0) ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_824,c_31,c_28]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_20,plain,
% 2.81/0.99      ( ~ v2_tex_2(X0,X1)
% 2.81/0.99      | m1_pre_topc(sK2(X1,X0),X1)
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | ~ v2_pre_topc(X1)
% 2.81/0.99      | ~ l1_pre_topc(X1)
% 2.81/0.99      | v1_xboole_0(X0) ),
% 2.81/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_16,plain,
% 2.81/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | v2_struct_0(X0)
% 2.81/0.99      | ~ v1_tdlat_3(X0)
% 2.81/0.99      | ~ v2_tdlat_3(X1)
% 2.81/0.99      | ~ v2_pre_topc(X1)
% 2.81/0.99      | v7_struct_0(X0)
% 2.81/0.99      | ~ l1_pre_topc(X1) ),
% 2.81/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_11,plain,
% 2.81/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.81/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_13,plain,
% 2.81/0.99      ( ~ v7_struct_0(X0)
% 2.81/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 2.81/0.99      | ~ l1_struct_0(X0) ),
% 2.81/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_428,plain,
% 2.81/0.99      ( ~ v7_struct_0(X0)
% 2.81/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 2.81/0.99      | ~ l1_pre_topc(X0) ),
% 2.81/0.99      inference(resolution,[status(thm)],[c_11,c_13]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_446,plain,
% 2.81/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.81/0.99      | v2_struct_0(X0)
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | ~ v1_tdlat_3(X0)
% 2.81/0.99      | ~ v2_tdlat_3(X1)
% 2.81/0.99      | ~ v2_pre_topc(X1)
% 2.81/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 2.81/0.99      | ~ l1_pre_topc(X0)
% 2.81/0.99      | ~ l1_pre_topc(X1) ),
% 2.81/0.99      inference(resolution,[status(thm)],[c_16,c_428]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_12,plain,
% 2.81/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.81/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_450,plain,
% 2.81/0.99      ( v1_zfmisc_1(u1_struct_0(X0))
% 2.81/0.99      | ~ v2_pre_topc(X1)
% 2.81/0.99      | ~ v2_tdlat_3(X1)
% 2.81/0.99      | ~ v1_tdlat_3(X0)
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | v2_struct_0(X0)
% 2.81/0.99      | ~ m1_pre_topc(X0,X1)
% 2.81/0.99      | ~ l1_pre_topc(X1) ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_446,c_12]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_451,plain,
% 2.81/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.81/0.99      | v2_struct_0(X0)
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | ~ v1_tdlat_3(X0)
% 2.81/0.99      | ~ v2_tdlat_3(X1)
% 2.81/0.99      | ~ v2_pre_topc(X1)
% 2.81/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 2.81/0.99      | ~ l1_pre_topc(X1) ),
% 2.81/0.99      inference(renaming,[status(thm)],[c_450]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_15,plain,
% 2.81/0.99      ( ~ v2_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 2.81/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_470,plain,
% 2.81/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.81/0.99      | v2_struct_0(X0)
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | ~ v1_tdlat_3(X0)
% 2.81/0.99      | ~ v2_tdlat_3(X1)
% 2.81/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 2.81/0.99      | ~ l1_pre_topc(X1) ),
% 2.81/0.99      inference(forward_subsumption_resolution,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_451,c_15]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_29,negated_conjecture,
% 2.81/0.99      ( v2_tdlat_3(sK3) ),
% 2.81/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_491,plain,
% 2.81/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.81/0.99      | v2_struct_0(X0)
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | ~ v1_tdlat_3(X0)
% 2.81/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 2.81/0.99      | ~ l1_pre_topc(X1)
% 2.81/0.99      | sK3 != X1 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_470,c_29]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_492,plain,
% 2.81/0.99      ( ~ m1_pre_topc(X0,sK3)
% 2.81/0.99      | v2_struct_0(X0)
% 2.81/0.99      | v2_struct_0(sK3)
% 2.81/0.99      | ~ v1_tdlat_3(X0)
% 2.81/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 2.81/0.99      | ~ l1_pre_topc(sK3) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_491]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_496,plain,
% 2.81/0.99      ( v1_zfmisc_1(u1_struct_0(X0))
% 2.81/0.99      | ~ v1_tdlat_3(X0)
% 2.81/0.99      | ~ m1_pre_topc(X0,sK3)
% 2.81/0.99      | v2_struct_0(X0) ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_492,c_31,c_28]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_497,plain,
% 2.81/0.99      ( ~ m1_pre_topc(X0,sK3)
% 2.81/0.99      | v2_struct_0(X0)
% 2.81/0.99      | ~ v1_tdlat_3(X0)
% 2.81/0.99      | v1_zfmisc_1(u1_struct_0(X0)) ),
% 2.81/0.99      inference(renaming,[status(thm)],[c_496]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_591,plain,
% 2.81/0.99      ( ~ v2_tex_2(X0,X1)
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.81/0.99      | v2_struct_0(X2)
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | ~ v1_tdlat_3(X2)
% 2.81/0.99      | ~ v2_pre_topc(X1)
% 2.81/0.99      | v1_zfmisc_1(u1_struct_0(X2))
% 2.81/0.99      | ~ l1_pre_topc(X1)
% 2.81/0.99      | v1_xboole_0(X0)
% 2.81/0.99      | sK2(X1,X0) != X2
% 2.81/0.99      | sK3 != X1 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_497]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_592,plain,
% 2.81/0.99      ( ~ v2_tex_2(X0,sK3)
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.81/0.99      | v2_struct_0(sK2(sK3,X0))
% 2.81/0.99      | v2_struct_0(sK3)
% 2.81/0.99      | ~ v1_tdlat_3(sK2(sK3,X0))
% 2.81/0.99      | ~ v2_pre_topc(sK3)
% 2.81/0.99      | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
% 2.81/0.99      | ~ l1_pre_topc(sK3)
% 2.81/0.99      | v1_xboole_0(X0) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_591]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_596,plain,
% 2.81/0.99      ( v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
% 2.81/0.99      | v2_struct_0(sK2(sK3,X0))
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.81/0.99      | ~ v2_tex_2(X0,sK3)
% 2.81/0.99      | ~ v1_tdlat_3(sK2(sK3,X0))
% 2.81/0.99      | v1_xboole_0(X0) ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_592,c_31,c_30,c_28]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_597,plain,
% 2.81/0.99      ( ~ v2_tex_2(X0,sK3)
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.81/0.99      | v2_struct_0(sK2(sK3,X0))
% 2.81/0.99      | ~ v1_tdlat_3(sK2(sK3,X0))
% 2.81/0.99      | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
% 2.81/0.99      | v1_xboole_0(X0) ),
% 2.81/0.99      inference(renaming,[status(thm)],[c_596]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_906,plain,
% 2.81/0.99      ( ~ v2_tex_2(X0,sK3)
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.81/0.99      | ~ v1_tdlat_3(sK2(sK3,X0))
% 2.81/0.99      | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
% 2.81/0.99      | v1_xboole_0(X0) ),
% 2.81/0.99      inference(backward_subsumption_resolution,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_828,c_597]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_915,plain,
% 2.81/0.99      ( ~ v2_tex_2(X0,sK3)
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.81/0.99      | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
% 2.81/0.99      | v1_xboole_0(X0) ),
% 2.81/0.99      inference(backward_subsumption_resolution,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_853,c_906]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2966,plain,
% 2.81/0.99      ( v2_tex_2(X0,sK3) != iProver_top
% 2.81/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.81/0.99      | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0))) = iProver_top
% 2.81/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_915]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_3229,plain,
% 2.81/0.99      ( v2_tex_2(sK4,sK3) != iProver_top
% 2.81/0.99      | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top
% 2.81/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 2.81/0.99      inference(superposition,[status(thm)],[c_2970,c_2966]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1278,plain,
% 2.81/0.99      ( ~ v2_tex_2(X0,sK3)
% 2.81/0.99      | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
% 2.81/0.99      | v1_xboole_0(X0)
% 2.81/0.99      | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3))
% 2.81/0.99      | sK4 != X0 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_915]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1279,plain,
% 2.81/0.99      ( ~ v2_tex_2(sK4,sK3)
% 2.81/0.99      | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
% 2.81/0.99      | v1_xboole_0(sK4) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_1278]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1281,plain,
% 2.81/0.99      ( v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) | ~ v2_tex_2(sK4,sK3) ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_1279,c_27]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1282,plain,
% 2.81/0.99      ( ~ v2_tex_2(sK4,sK3) | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) ),
% 2.81/0.99      inference(renaming,[status(thm)],[c_1281]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1283,plain,
% 2.81/0.99      ( v2_tex_2(sK4,sK3) != iProver_top
% 2.81/0.99      | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_1282]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_3426,plain,
% 2.81/0.99      ( v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top
% 2.81/0.99      | v2_tex_2(sK4,sK3) != iProver_top ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_3229,c_1283]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_3427,plain,
% 2.81/0.99      ( v2_tex_2(sK4,sK3) != iProver_top
% 2.81/0.99      | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top ),
% 2.81/0.99      inference(renaming,[status(thm)],[c_3426]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_5567,plain,
% 2.81/0.99      ( k1_tarski(sK0(sK4)) = sK4
% 2.81/0.99      | v2_tex_2(sK4,sK3) != iProver_top
% 2.81/0.99      | v1_zfmisc_1(sK4) = iProver_top ),
% 2.81/0.99      inference(superposition,[status(thm)],[c_5563,c_3427]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_38,plain,
% 2.81/0.99      ( v2_tex_2(sK4,sK3) = iProver_top
% 2.81/0.99      | v1_zfmisc_1(sK4) = iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_5710,plain,
% 2.81/0.99      ( k1_tarski(sK0(sK4)) = sK4 | v1_zfmisc_1(sK4) = iProver_top ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_5567,c_38]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_5716,plain,
% 2.81/0.99      ( k1_tarski(sK0(sK4)) = sK4 | v1_xboole_0(sK4) = iProver_top ),
% 2.81/0.99      inference(superposition,[status(thm)],[c_5710,c_4746]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_5807,plain,
% 2.81/0.99      ( k1_tarski(sK0(sK4)) = sK4 ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_5716,c_36]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_10,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.81/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2975,plain,
% 2.81/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.81/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_3455,plain,
% 2.81/0.99      ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
% 2.81/0.99      inference(superposition,[status(thm)],[c_2970,c_2975]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_4,plain,
% 2.81/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 2.81/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2981,plain,
% 2.81/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.81/0.99      | r2_hidden(X2,X0) != iProver_top
% 2.81/0.99      | r2_hidden(X2,X1) = iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_4142,plain,
% 2.81/0.99      ( r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
% 2.81/0.99      | r2_hidden(X0,sK4) != iProver_top ),
% 2.81/0.99      inference(superposition,[status(thm)],[c_3455,c_2981]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_8,plain,
% 2.81/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.81/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2977,plain,
% 2.81/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 2.81/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_4471,plain,
% 2.81/0.99      ( m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
% 2.81/0.99      | r2_hidden(X0,sK4) != iProver_top ),
% 2.81/0.99      inference(superposition,[status(thm)],[c_4142,c_2977]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_14,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,X1)
% 2.81/0.99      | v1_xboole_0(X1)
% 2.81/0.99      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 2.81/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2974,plain,
% 2.81/0.99      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 2.81/0.99      | m1_subset_1(X1,X0) != iProver_top
% 2.81/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_4659,plain,
% 2.81/0.99      ( k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0)
% 2.81/0.99      | r2_hidden(X0,sK4) != iProver_top
% 2.81/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.81/0.99      inference(superposition,[status(thm)],[c_4471,c_2974]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2984,plain,
% 2.81/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.81/0.99      | v1_xboole_0(X1) != iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_4470,plain,
% 2.81/0.99      ( r2_hidden(X0,sK4) != iProver_top
% 2.81/0.99      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 2.81/0.99      inference(superposition,[status(thm)],[c_4142,c_2984]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_5130,plain,
% 2.81/0.99      ( r2_hidden(X0,sK4) != iProver_top
% 2.81/0.99      | k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0) ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_4659,c_4470]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_5131,plain,
% 2.81/0.99      ( k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0)
% 2.81/0.99      | r2_hidden(X0,sK4) != iProver_top ),
% 2.81/0.99      inference(renaming,[status(thm)],[c_5130]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_5138,plain,
% 2.81/0.99      ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4))
% 2.81/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 2.81/0.99      inference(superposition,[status(thm)],[c_2985,c_5131]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_5190,plain,
% 2.81/0.99      ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4)) ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_5138,c_36]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_23,plain,
% 2.81/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 2.81/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.81/0.99      | v2_struct_0(X0)
% 2.81/0.99      | ~ v2_pre_topc(X0)
% 2.81/0.99      | ~ l1_pre_topc(X0) ),
% 2.81/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_781,plain,
% 2.81/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 2.81/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.81/0.99      | v2_struct_0(X0)
% 2.81/0.99      | ~ l1_pre_topc(X0)
% 2.81/0.99      | sK3 != X0 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_782,plain,
% 2.81/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
% 2.81/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.81/0.99      | v2_struct_0(sK3)
% 2.81/0.99      | ~ l1_pre_topc(sK3) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_781]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_786,plain,
% 2.81/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
% 2.81/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_782,c_31,c_28]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2968,plain,
% 2.81/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) = iProver_top
% 2.81/0.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_786]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_5193,plain,
% 2.81/0.99      ( v2_tex_2(k1_tarski(sK0(sK4)),sK3) = iProver_top
% 2.81/0.99      | m1_subset_1(sK0(sK4),u1_struct_0(sK3)) != iProver_top ),
% 2.81/0.99      inference(superposition,[status(thm)],[c_5190,c_2968]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_5212,plain,
% 2.81/0.99      ( v2_tex_2(k1_tarski(sK0(sK4)),sK3) = iProver_top
% 2.81/0.99      | r2_hidden(sK0(sK4),sK4) != iProver_top ),
% 2.81/0.99      inference(superposition,[status(thm)],[c_4471,c_5193]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_3562,plain,
% 2.81/0.99      ( r2_hidden(sK0(sK4),sK4) | v1_xboole_0(sK4) ),
% 2.81/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3565,plain,
% 2.81/1.00      ( r2_hidden(sK0(sK4),sK4) = iProver_top
% 2.81/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_3562]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_5215,plain,
% 2.81/1.00      ( v2_tex_2(k1_tarski(sK0(sK4)),sK3) = iProver_top ),
% 2.81/1.00      inference(global_propositional_subsumption,
% 2.81/1.00                [status(thm)],
% 2.81/1.00                [c_5212,c_36,c_3565]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_5810,plain,
% 2.81/1.00      ( v2_tex_2(sK4,sK3) = iProver_top ),
% 2.81/1.00      inference(demodulation,[status(thm)],[c_5807,c_5215]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_5824,plain,
% 2.81/1.00      ( v2_tex_2(sK4,sK3) ),
% 2.81/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_5810]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2420,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3202,plain,
% 2.81/1.00      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_2420]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3392,plain,
% 2.81/1.00      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_3202]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_4346,plain,
% 2.81/1.00      ( u1_struct_0(sK2(sK3,sK4)) != sK4
% 2.81/1.00      | sK4 = u1_struct_0(sK2(sK3,sK4))
% 2.81/1.00      | sK4 != sK4 ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_3392]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2419,plain,( X0 = X0 ),theory(equality) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3393,plain,
% 2.81/1.00      ( sK4 = sK4 ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_2419]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_24,negated_conjecture,
% 2.81/1.00      ( ~ v2_tex_2(sK4,sK3) | ~ v1_zfmisc_1(sK4) ),
% 2.81/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(contradiction,plain,
% 2.81/1.00      ( $false ),
% 2.81/1.00      inference(minisat,
% 2.81/1.00                [status(thm)],
% 2.81/1.00                [c_6245,c_5824,c_5810,c_4346,c_3393,c_1294,c_1279,c_24,
% 2.81/1.00                 c_36,c_27]) ).
% 2.81/1.00  
% 2.81/1.00  
% 2.81/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.81/1.00  
% 2.81/1.00  ------                               Statistics
% 2.81/1.00  
% 2.81/1.00  ------ General
% 2.81/1.00  
% 2.81/1.00  abstr_ref_over_cycles:                  0
% 2.81/1.00  abstr_ref_under_cycles:                 0
% 2.81/1.00  gc_basic_clause_elim:                   0
% 2.81/1.00  forced_gc_time:                         0
% 2.81/1.00  parsing_time:                           0.01
% 2.81/1.00  unif_index_cands_time:                  0.
% 2.81/1.00  unif_index_add_time:                    0.
% 2.81/1.00  orderings_time:                         0.
% 2.81/1.00  out_proof_time:                         0.011
% 2.81/1.00  total_time:                             0.169
% 2.81/1.00  num_of_symbols:                         54
% 2.81/1.00  num_of_terms:                           3383
% 2.81/1.00  
% 2.81/1.00  ------ Preprocessing
% 2.81/1.00  
% 2.81/1.00  num_of_splits:                          0
% 2.81/1.00  num_of_split_atoms:                     0
% 2.81/1.00  num_of_reused_defs:                     0
% 2.81/1.00  num_eq_ax_congr_red:                    28
% 2.81/1.00  num_of_sem_filtered_clauses:            1
% 2.81/1.00  num_of_subtypes:                        0
% 2.81/1.00  monotx_restored_types:                  0
% 2.81/1.00  sat_num_of_epr_types:                   0
% 2.81/1.00  sat_num_of_non_cyclic_types:            0
% 2.81/1.00  sat_guarded_non_collapsed_types:        0
% 2.81/1.00  num_pure_diseq_elim:                    0
% 2.81/1.00  simp_replaced_by:                       0
% 2.81/1.00  res_preprocessed:                       116
% 2.81/1.00  prep_upred:                             0
% 2.81/1.00  prep_unflattend:                        88
% 2.81/1.00  smt_new_axioms:                         0
% 2.81/1.00  pred_elim_cands:                        6
% 2.81/1.00  pred_elim:                              8
% 2.81/1.00  pred_elim_cl:                           11
% 2.81/1.00  pred_elim_cycles:                       19
% 2.81/1.00  merged_defs:                            24
% 2.81/1.00  merged_defs_ncl:                        0
% 2.81/1.00  bin_hyper_res:                          24
% 2.81/1.00  prep_cycles:                            4
% 2.81/1.00  pred_elim_time:                         0.028
% 2.81/1.00  splitting_time:                         0.
% 2.81/1.00  sem_filter_time:                        0.
% 2.81/1.00  monotx_time:                            0.001
% 2.81/1.00  subtype_inf_time:                       0.
% 2.81/1.00  
% 2.81/1.00  ------ Problem properties
% 2.81/1.00  
% 2.81/1.00  clauses:                                20
% 2.81/1.00  conjectures:                            4
% 2.81/1.00  epr:                                    7
% 2.81/1.00  horn:                                   13
% 2.81/1.00  ground:                                 4
% 2.81/1.00  unary:                                  3
% 2.81/1.00  binary:                                 12
% 2.81/1.00  lits:                                   46
% 2.81/1.00  lits_eq:                                3
% 2.81/1.00  fd_pure:                                0
% 2.81/1.00  fd_pseudo:                              0
% 2.81/1.00  fd_cond:                                0
% 2.81/1.00  fd_pseudo_cond:                         1
% 2.81/1.00  ac_symbols:                             0
% 2.81/1.00  
% 2.81/1.00  ------ Propositional Solver
% 2.81/1.00  
% 2.81/1.00  prop_solver_calls:                      31
% 2.81/1.00  prop_fast_solver_calls:                 1242
% 2.81/1.00  smt_solver_calls:                       0
% 2.81/1.00  smt_fast_solver_calls:                  0
% 2.81/1.00  prop_num_of_clauses:                    1635
% 2.81/1.00  prop_preprocess_simplified:             5655
% 2.81/1.00  prop_fo_subsumed:                       60
% 2.81/1.00  prop_solver_time:                       0.
% 2.81/1.00  smt_solver_time:                        0.
% 2.81/1.00  smt_fast_solver_time:                   0.
% 2.81/1.00  prop_fast_solver_time:                  0.
% 2.81/1.00  prop_unsat_core_time:                   0.
% 2.81/1.00  
% 2.81/1.00  ------ QBF
% 2.81/1.00  
% 2.81/1.00  qbf_q_res:                              0
% 2.81/1.00  qbf_num_tautologies:                    0
% 2.81/1.00  qbf_prep_cycles:                        0
% 2.81/1.00  
% 2.81/1.00  ------ BMC1
% 2.81/1.00  
% 2.81/1.00  bmc1_current_bound:                     -1
% 2.81/1.00  bmc1_last_solved_bound:                 -1
% 2.81/1.00  bmc1_unsat_core_size:                   -1
% 2.81/1.00  bmc1_unsat_core_parents_size:           -1
% 2.81/1.00  bmc1_merge_next_fun:                    0
% 2.81/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.81/1.00  
% 2.81/1.00  ------ Instantiation
% 2.81/1.00  
% 2.81/1.00  inst_num_of_clauses:                    399
% 2.81/1.00  inst_num_in_passive:                    68
% 2.81/1.00  inst_num_in_active:                     294
% 2.81/1.00  inst_num_in_unprocessed:                36
% 2.81/1.00  inst_num_of_loops:                      373
% 2.81/1.00  inst_num_of_learning_restarts:          0
% 2.81/1.00  inst_num_moves_active_passive:          72
% 2.81/1.00  inst_lit_activity:                      0
% 2.81/1.00  inst_lit_activity_moves:                0
% 2.81/1.00  inst_num_tautologies:                   0
% 2.81/1.00  inst_num_prop_implied:                  0
% 2.81/1.00  inst_num_existing_simplified:           0
% 2.81/1.00  inst_num_eq_res_simplified:             0
% 2.81/1.00  inst_num_child_elim:                    0
% 2.81/1.00  inst_num_of_dismatching_blockings:      137
% 2.81/1.00  inst_num_of_non_proper_insts:           536
% 2.81/1.00  inst_num_of_duplicates:                 0
% 2.81/1.00  inst_inst_num_from_inst_to_res:         0
% 2.81/1.00  inst_dismatching_checking_time:         0.
% 2.81/1.00  
% 2.81/1.00  ------ Resolution
% 2.81/1.00  
% 2.81/1.00  res_num_of_clauses:                     0
% 2.81/1.00  res_num_in_passive:                     0
% 2.81/1.00  res_num_in_active:                      0
% 2.81/1.00  res_num_of_loops:                       120
% 2.81/1.00  res_forward_subset_subsumed:            77
% 2.81/1.00  res_backward_subset_subsumed:           0
% 2.81/1.00  res_forward_subsumed:                   0
% 2.81/1.00  res_backward_subsumed:                  0
% 2.81/1.00  res_forward_subsumption_resolution:     2
% 2.81/1.00  res_backward_subsumption_resolution:    2
% 2.81/1.00  res_clause_to_clause_subsumption:       270
% 2.81/1.00  res_orphan_elimination:                 0
% 2.81/1.00  res_tautology_del:                      137
% 2.81/1.00  res_num_eq_res_simplified:              0
% 2.81/1.00  res_num_sel_changes:                    0
% 2.81/1.00  res_moves_from_active_to_pass:          0
% 2.81/1.00  
% 2.81/1.00  ------ Superposition
% 2.81/1.00  
% 2.81/1.00  sup_time_total:                         0.
% 2.81/1.00  sup_time_generating:                    0.
% 2.81/1.00  sup_time_sim_full:                      0.
% 2.81/1.00  sup_time_sim_immed:                     0.
% 2.81/1.00  
% 2.81/1.00  sup_num_of_clauses:                     101
% 2.81/1.00  sup_num_in_active:                      65
% 2.81/1.00  sup_num_in_passive:                     36
% 2.81/1.00  sup_num_of_loops:                       74
% 2.81/1.00  sup_fw_superposition:                   46
% 2.81/1.00  sup_bw_superposition:                   71
% 2.81/1.00  sup_immediate_simplified:               16
% 2.81/1.00  sup_given_eliminated:                   0
% 2.81/1.00  comparisons_done:                       0
% 2.81/1.00  comparisons_avoided:                    0
% 2.81/1.00  
% 2.81/1.00  ------ Simplifications
% 2.81/1.00  
% 2.81/1.00  
% 2.81/1.00  sim_fw_subset_subsumed:                 4
% 2.81/1.00  sim_bw_subset_subsumed:                 6
% 2.81/1.00  sim_fw_subsumed:                        6
% 2.81/1.00  sim_bw_subsumed:                        0
% 2.81/1.00  sim_fw_subsumption_res:                 0
% 2.81/1.00  sim_bw_subsumption_res:                 0
% 2.81/1.00  sim_tautology_del:                      8
% 2.81/1.00  sim_eq_tautology_del:                   2
% 2.81/1.00  sim_eq_res_simp:                        0
% 2.81/1.00  sim_fw_demodulated:                     1
% 2.81/1.00  sim_bw_demodulated:                     4
% 2.81/1.00  sim_light_normalised:                   6
% 2.81/1.00  sim_joinable_taut:                      0
% 2.81/1.00  sim_joinable_simp:                      0
% 2.81/1.00  sim_ac_normalised:                      0
% 2.81/1.00  sim_smt_subsumption:                    0
% 2.81/1.00  
%------------------------------------------------------------------------------
