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
% DateTime   : Thu Dec  3 12:26:50 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :  240 (2375 expanded)
%              Number of clauses        :  140 ( 583 expanded)
%              Number of leaves         :   28 ( 542 expanded)
%              Depth                    :   26
%              Number of atoms          :  967 (17314 expanded)
%              Number of equality atoms :  319 (1061 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
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

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

fof(f56,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f74,plain,(
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
    inference(nnf_transformation,[],[f57])).

fof(f75,plain,(
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
    inference(flattening,[],[f74])).

fof(f77,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ( ~ v1_zfmisc_1(sK6)
          | ~ v2_tex_2(sK6,X0) )
        & ( v1_zfmisc_1(sK6)
          | v2_tex_2(sK6,X0) )
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,
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
            | ~ v2_tex_2(X1,sK5) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,sK5) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK5)
      & v2_tdlat_3(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,
    ( ( ~ v1_zfmisc_1(sK6)
      | ~ v2_tex_2(sK6,sK5) )
    & ( v1_zfmisc_1(sK6)
      | v2_tex_2(sK6,sK5) )
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    & ~ v1_xboole_0(sK6)
    & l1_pre_topc(sK5)
    & v2_tdlat_3(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f75,f77,f76])).

fof(f118,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f78])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f70,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK3(X0,X1)) = X1
        & m1_pre_topc(sK3(X0,X1),X0)
        & ~ v2_struct_0(sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK3(X0,X1)) = X1
            & m1_pre_topc(sK3(X0,X1),X0)
            & ~ v2_struct_0(sK3(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f70])).

fof(f105,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK3(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f113,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f78])).

fof(f116,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f78])).

fof(f117,plain,(
    ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f78])).

fof(f106,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK3(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK3(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f119,plain,
    ( v1_zfmisc_1(sK6)
    | v2_tex_2(sK6,sK5) ),
    inference(cnf_transformation,[],[f78])).

fof(f20,axiom,(
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

fof(f24,plain,(
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
    inference(pure_predicate_removal,[],[f20])).

fof(f52,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f72,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK4(X0,X1)) = X1
        & m1_pre_topc(sK4(X0,X1),X0)
        & v1_tdlat_3(sK4(X0,X1))
        & ~ v2_struct_0(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK4(X0,X1)) = X1
            & m1_pre_topc(sK4(X0,X1),X0)
            & v1_tdlat_3(sK4(X0,X1))
            & ~ v2_struct_0(sK4(X0,X1)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f53,f72])).

fof(f110,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK4(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f114,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f78])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f95,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f99,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f120,plain,
    ( ~ v1_zfmisc_1(sK6)
    | ~ v2_tex_2(sK6,sK5) ),
    inference(cnf_transformation,[],[f78])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_tdlat_3(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f101,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f94,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f96,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f109,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK4(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f111,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK4(X0,X1)) = X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK4(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v2_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f115,plain,(
    v2_tdlat_3(sK5) ),
    inference(cnf_transformation,[],[f78])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f59,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f58])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f59,f60])).

fof(f80,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f19,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f107,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f79,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f62])).

fof(f64,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f63,f64])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f121,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f82])).

fof(f122,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f121])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f112,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_4342,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_26,plain,
    ( m1_pre_topc(sK3(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_4351,plain,
    ( m1_pre_topc(sK3(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5937,plain,
    ( m1_pre_topc(sK3(sK5,sK6),sK5) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4342,c_4351])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_42,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_38,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_45,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_46,plain,
    ( v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_47,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_4457,plain,
    ( m1_pre_topc(sK3(X0,sK6),X0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_4473,plain,
    ( m1_pre_topc(sK3(X0,sK6),X0) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4457])).

cnf(c_4475,plain,
    ( m1_pre_topc(sK3(sK5,sK6),sK5) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4473])).

cnf(c_6213,plain,
    ( m1_pre_topc(sK3(sK5,sK6),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5937,c_42,c_45,c_46,c_47,c_4475])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK3(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_4352,plain,
    ( u1_struct_0(sK3(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5824,plain,
    ( u1_struct_0(sK3(sK5,sK6)) = sK6
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4342,c_4352])).

cnf(c_4418,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(sK6)
    | u1_struct_0(sK3(X0,sK6)) = sK6 ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_4438,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5)
    | v1_xboole_0(sK6)
    | u1_struct_0(sK3(sK5,sK6)) = sK6 ),
    inference(instantiation,[status(thm)],[c_4418])).

cnf(c_6068,plain,
    ( u1_struct_0(sK3(sK5,sK6)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5824,c_41,c_38,c_37,c_36,c_4438])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_4355,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6542,plain,
    ( m1_pre_topc(sK3(sK5,sK6),X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) = iProver_top
    | m1_subset_1(X1,sK6) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3(sK5,sK6)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6068,c_4355])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK3(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_4419,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK3(X0,sK6))
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_4433,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3(X0,sK6)) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4419])).

cnf(c_4435,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v2_struct_0(sK3(sK5,sK6)) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4433])).

cnf(c_7566,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_subset_1(X1,sK6) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) = iProver_top
    | m1_pre_topc(sK3(sK5,sK6),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6542,c_42,c_45,c_46,c_47,c_4435])).

cnf(c_7567,plain,
    ( m1_pre_topc(sK3(sK5,sK6),X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) = iProver_top
    | m1_subset_1(X1,sK6) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7566])).

cnf(c_7572,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(X0,sK6) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6213,c_7567])).

cnf(c_7577,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7572,c_42,c_45])).

cnf(c_35,negated_conjecture,
    ( v2_tex_2(sK6,sK5)
    | v1_zfmisc_1(sK6) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_4343,plain,
    ( v2_tex_2(sK6,sK5) = iProver_top
    | v1_zfmisc_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_30,plain,
    ( ~ v2_tex_2(X0,X1)
    | m1_pre_topc(sK4(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_4348,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | m1_pre_topc(sK4(X1,X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6654,plain,
    ( v2_tex_2(sK6,sK5) != iProver_top
    | m1_pre_topc(sK4(sK5,sK6),sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4342,c_4348])).

cnf(c_40,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_43,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_6903,plain,
    ( v2_tex_2(sK6,sK5) != iProver_top
    | m1_pre_topc(sK4(sK5,sK6),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6654,c_42,c_43,c_45,c_46])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_4356,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6907,plain,
    ( v2_tex_2(sK6,sK5) != iProver_top
    | l1_pre_topc(sK4(sK5,sK6)) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6903,c_4356])).

cnf(c_6912,plain,
    ( l1_pre_topc(sK4(sK5,sK6)) = iProver_top
    | v2_tex_2(sK6,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6907,c_45])).

cnf(c_6913,plain,
    ( v2_tex_2(sK6,sK5) != iProver_top
    | l1_pre_topc(sK4(sK5,sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6912])).

cnf(c_20,plain,
    ( ~ v2_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_4353,plain,
    ( v2_tdlat_3(X0) != iProver_top
    | v2_pre_topc(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_6916,plain,
    ( v2_tex_2(sK6,sK5) != iProver_top
    | v2_tdlat_3(sK4(sK5,sK6)) != iProver_top
    | v2_pre_topc(sK4(sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6913,c_4353])).

cnf(c_34,negated_conjecture,
    ( ~ v2_tex_2(sK6,sK5)
    | ~ v1_zfmisc_1(sK6) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_49,plain,
    ( v2_tex_2(sK6,sK5) != iProver_top
    | v1_zfmisc_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3530,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4680,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_3530])).

cnf(c_3531,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4529,plain,
    ( X0 != X1
    | sK6 != X1
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_3531])).

cnf(c_4830,plain,
    ( X0 != sK6
    | sK6 = X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_4529])).

cnf(c_5452,plain,
    ( u1_struct_0(sK4(X0,sK6)) != sK6
    | sK6 = u1_struct_0(sK4(X0,sK6))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_4830])).

cnf(c_5453,plain,
    ( u1_struct_0(sK4(sK5,sK6)) != sK6
    | sK6 = u1_struct_0(sK4(sK5,sK6))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_5452])).

cnf(c_22,plain,
    ( ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_241,plain,
    ( ~ v2_tdlat_3(X0)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22,c_20])).

cnf(c_242,plain,
    ( ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X0)
    | v2_struct_0(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_241])).

cnf(c_15,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_17,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_542,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_15,c_17])).

cnf(c_560,plain,
    ( ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X0)
    | v2_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_242,c_542])).

cnf(c_5464,plain,
    ( ~ v1_tdlat_3(sK4(X0,sK6))
    | ~ v2_tdlat_3(sK4(X0,sK6))
    | v2_struct_0(sK4(X0,sK6))
    | v1_zfmisc_1(u1_struct_0(sK4(X0,sK6)))
    | ~ l1_pre_topc(sK4(X0,sK6)) ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_5473,plain,
    ( v1_tdlat_3(sK4(X0,sK6)) != iProver_top
    | v2_tdlat_3(sK4(X0,sK6)) != iProver_top
    | v2_struct_0(sK4(X0,sK6)) = iProver_top
    | v1_zfmisc_1(u1_struct_0(sK4(X0,sK6))) = iProver_top
    | l1_pre_topc(sK4(X0,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5464])).

cnf(c_5475,plain,
    ( v1_tdlat_3(sK4(sK5,sK6)) != iProver_top
    | v2_tdlat_3(sK4(sK5,sK6)) != iProver_top
    | v2_struct_0(sK4(sK5,sK6)) = iProver_top
    | v1_zfmisc_1(u1_struct_0(sK4(sK5,sK6))) = iProver_top
    | l1_pre_topc(sK4(sK5,sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5473])).

cnf(c_31,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tdlat_3(sK4(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_4347,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v1_tdlat_3(sK4(X1,X0)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6551,plain,
    ( v2_tex_2(sK6,sK5) != iProver_top
    | v1_tdlat_3(sK4(sK5,sK6)) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4342,c_4347])).

cnf(c_6718,plain,
    ( v2_tex_2(sK6,sK5) != iProver_top
    | v1_tdlat_3(sK4(sK5,sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6551,c_42,c_43,c_45,c_46])).

cnf(c_29,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK4(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_4349,plain,
    ( u1_struct_0(sK4(X0,X1)) = X1
    | v2_tex_2(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6639,plain,
    ( u1_struct_0(sK4(sK5,sK6)) = sK6
    | v2_tex_2(sK6,sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4342,c_4349])).

cnf(c_6723,plain,
    ( u1_struct_0(sK4(sK5,sK6)) = sK6
    | v2_tex_2(sK6,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6639,c_42,c_43,c_45,c_46])).

cnf(c_32,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK4(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_4346,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK4(X1,X0)) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_6440,plain,
    ( v2_tex_2(sK6,sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_struct_0(sK4(sK5,sK6)) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4342,c_4346])).

cnf(c_6807,plain,
    ( v2_struct_0(sK4(sK5,sK6)) != iProver_top
    | v2_tex_2(sK6,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6440,c_42,c_43,c_45,c_46])).

cnf(c_6808,plain,
    ( v2_tex_2(sK6,sK5) != iProver_top
    | v2_struct_0(sK4(sK5,sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6807])).

cnf(c_24,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1574,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_tdlat_3(X2)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_24])).

cnf(c_1575,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_1574])).

cnf(c_4333,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_tdlat_3(X1) != iProver_top
    | v2_tdlat_3(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1575])).

cnf(c_6908,plain,
    ( v2_tex_2(sK6,sK5) != iProver_top
    | v2_tdlat_3(sK4(sK5,sK6)) = iProver_top
    | v2_tdlat_3(sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6903,c_4333])).

cnf(c_39,negated_conjecture,
    ( v2_tdlat_3(sK5) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_44,plain,
    ( v2_tdlat_3(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_7002,plain,
    ( v2_tdlat_3(sK4(sK5,sK6)) = iProver_top
    | v2_tex_2(sK6,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6908,c_42,c_44,c_45])).

cnf(c_7003,plain,
    ( v2_tex_2(sK6,sK5) != iProver_top
    | v2_tdlat_3(sK4(sK5,sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7002])).

cnf(c_3539,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_zfmisc_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_5446,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_zfmisc_1(sK6)
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_3539])).

cnf(c_7438,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK4(X0,sK6)))
    | v1_zfmisc_1(sK6)
    | sK6 != u1_struct_0(sK4(X0,sK6)) ),
    inference(instantiation,[status(thm)],[c_5446])).

cnf(c_7439,plain,
    ( sK6 != u1_struct_0(sK4(X0,sK6))
    | v1_zfmisc_1(u1_struct_0(sK4(X0,sK6))) != iProver_top
    | v1_zfmisc_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7438])).

cnf(c_7441,plain,
    ( sK6 != u1_struct_0(sK4(sK5,sK6))
    | v1_zfmisc_1(u1_struct_0(sK4(sK5,sK6))) != iProver_top
    | v1_zfmisc_1(sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7439])).

cnf(c_8311,plain,
    ( v2_tex_2(sK6,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6916,c_45,c_49,c_4680,c_5453,c_5475,c_6718,c_6723,c_6808,c_6907,c_7003,c_7441])).

cnf(c_8315,plain,
    ( v1_zfmisc_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4343,c_8311])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_4366,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_319,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_320,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_319])).

cnf(c_28,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_587,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_zfmisc_1(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | X2 != X1
    | X2 = X3
    | k1_tarski(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_320,c_28])).

cnf(c_588,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(k1_tarski(X0))
    | X1 = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_587])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_592,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | X1 = k1_tarski(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_588,c_6,c_1])).

cnf(c_4335,plain,
    ( X0 = k1_tarski(X1)
    | r2_hidden(X1,X0) != iProver_top
    | v1_zfmisc_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_592])).

cnf(c_5190,plain,
    ( k1_tarski(sK0(X0)) = X0
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4366,c_4335])).

cnf(c_8379,plain,
    ( k1_tarski(sK0(sK6)) = sK6
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_8315,c_5190])).

cnf(c_8382,plain,
    ( k1_tarski(sK0(sK6)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8379,c_46])).

cnf(c_4,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_4362,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_10,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_4358,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4981,plain,
    ( m1_subset_1(X0,k1_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4362,c_4358])).

cnf(c_8388,plain,
    ( m1_subset_1(sK0(sK6),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_8382,c_4981])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_4354,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7585,plain,
    ( k6_domain_1(u1_struct_0(sK5),X0) = k1_tarski(X0)
    | m1_subset_1(X0,sK6) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7577,c_4354])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_4421,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_4519,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v1_xboole_0(u1_struct_0(sK5))
    | v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_4421])).

cnf(c_4520,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4519])).

cnf(c_8991,plain,
    ( m1_subset_1(X0,sK6) != iProver_top
    | k6_domain_1(u1_struct_0(sK5),X0) = k1_tarski(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7585,c_46,c_47,c_4520])).

cnf(c_8992,plain,
    ( k6_domain_1(u1_struct_0(sK5),X0) = k1_tarski(X0)
    | m1_subset_1(X0,sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_8991])).

cnf(c_9166,plain,
    ( k6_domain_1(u1_struct_0(sK5),sK0(sK6)) = k1_tarski(sK0(sK6)) ),
    inference(superposition,[status(thm)],[c_8388,c_8992])).

cnf(c_9167,plain,
    ( k6_domain_1(u1_struct_0(sK5),sK0(sK6)) = sK6 ),
    inference(light_normalisation,[status(thm)],[c_9166,c_8382])).

cnf(c_33,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_4345,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_9270,plain,
    ( v2_tex_2(sK6,sK5) = iProver_top
    | m1_subset_1(sK0(sK6),u1_struct_0(sK5)) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_9167,c_4345])).

cnf(c_11477,plain,
    ( m1_subset_1(sK0(sK6),u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9270,c_42,c_43,c_45,c_49,c_4680,c_5453,c_5475,c_6718,c_6723,c_6808,c_6907,c_7003,c_7441])).

cnf(c_11481,plain,
    ( m1_subset_1(sK0(sK6),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_7577,c_11477])).

cnf(c_4534,plain,
    ( m1_subset_1(X0,sK6)
    | ~ r2_hidden(X0,sK6) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4782,plain,
    ( m1_subset_1(sK0(sK6),sK6)
    | ~ r2_hidden(sK0(sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_4534])).

cnf(c_4783,plain,
    ( m1_subset_1(sK0(sK6),sK6) = iProver_top
    | r2_hidden(sK0(sK6),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4782])).

cnf(c_4422,plain,
    ( r2_hidden(sK0(sK6),sK6)
    | v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4423,plain,
    ( r2_hidden(sK0(sK6),sK6) = iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4422])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11481,c_4783,c_4423,c_46])).

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
% 0.13/0.33  % DateTime   : Tue Dec  1 10:08:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.67/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/0.99  
% 3.67/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.67/0.99  
% 3.67/0.99  ------  iProver source info
% 3.67/0.99  
% 3.67/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.67/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.67/0.99  git: non_committed_changes: false
% 3.67/0.99  git: last_make_outside_of_git: false
% 3.67/0.99  
% 3.67/0.99  ------ 
% 3.67/0.99  
% 3.67/0.99  ------ Input Options
% 3.67/0.99  
% 3.67/0.99  --out_options                           all
% 3.67/0.99  --tptp_safe_out                         true
% 3.67/0.99  --problem_path                          ""
% 3.67/0.99  --include_path                          ""
% 3.67/0.99  --clausifier                            res/vclausify_rel
% 3.67/0.99  --clausifier_options                    ""
% 3.67/0.99  --stdin                                 false
% 3.67/0.99  --stats_out                             all
% 3.67/0.99  
% 3.67/0.99  ------ General Options
% 3.67/0.99  
% 3.67/0.99  --fof                                   false
% 3.67/0.99  --time_out_real                         305.
% 3.67/0.99  --time_out_virtual                      -1.
% 3.67/0.99  --symbol_type_check                     false
% 3.67/0.99  --clausify_out                          false
% 3.67/0.99  --sig_cnt_out                           false
% 3.67/0.99  --trig_cnt_out                          false
% 3.67/0.99  --trig_cnt_out_tolerance                1.
% 3.67/0.99  --trig_cnt_out_sk_spl                   false
% 3.67/0.99  --abstr_cl_out                          false
% 3.67/0.99  
% 3.67/0.99  ------ Global Options
% 3.67/0.99  
% 3.67/0.99  --schedule                              default
% 3.67/0.99  --add_important_lit                     false
% 3.67/0.99  --prop_solver_per_cl                    1000
% 3.67/0.99  --min_unsat_core                        false
% 3.67/0.99  --soft_assumptions                      false
% 3.67/0.99  --soft_lemma_size                       3
% 3.67/0.99  --prop_impl_unit_size                   0
% 3.67/0.99  --prop_impl_unit                        []
% 3.67/0.99  --share_sel_clauses                     true
% 3.67/0.99  --reset_solvers                         false
% 3.67/0.99  --bc_imp_inh                            [conj_cone]
% 3.67/0.99  --conj_cone_tolerance                   3.
% 3.67/0.99  --extra_neg_conj                        none
% 3.67/0.99  --large_theory_mode                     true
% 3.67/0.99  --prolific_symb_bound                   200
% 3.67/0.99  --lt_threshold                          2000
% 3.67/0.99  --clause_weak_htbl                      true
% 3.67/0.99  --gc_record_bc_elim                     false
% 3.67/0.99  
% 3.67/0.99  ------ Preprocessing Options
% 3.67/0.99  
% 3.67/0.99  --preprocessing_flag                    true
% 3.67/0.99  --time_out_prep_mult                    0.1
% 3.67/0.99  --splitting_mode                        input
% 3.67/0.99  --splitting_grd                         true
% 3.67/0.99  --splitting_cvd                         false
% 3.67/0.99  --splitting_cvd_svl                     false
% 3.67/0.99  --splitting_nvd                         32
% 3.67/0.99  --sub_typing                            true
% 3.67/0.99  --prep_gs_sim                           true
% 3.67/0.99  --prep_unflatten                        true
% 3.67/0.99  --prep_res_sim                          true
% 3.67/0.99  --prep_upred                            true
% 3.67/0.99  --prep_sem_filter                       exhaustive
% 3.67/0.99  --prep_sem_filter_out                   false
% 3.67/0.99  --pred_elim                             true
% 3.67/0.99  --res_sim_input                         true
% 3.67/0.99  --eq_ax_congr_red                       true
% 3.67/0.99  --pure_diseq_elim                       true
% 3.67/0.99  --brand_transform                       false
% 3.67/0.99  --non_eq_to_eq                          false
% 3.67/0.99  --prep_def_merge                        true
% 3.67/0.99  --prep_def_merge_prop_impl              false
% 3.67/0.99  --prep_def_merge_mbd                    true
% 3.67/0.99  --prep_def_merge_tr_red                 false
% 3.67/0.99  --prep_def_merge_tr_cl                  false
% 3.67/0.99  --smt_preprocessing                     true
% 3.67/0.99  --smt_ac_axioms                         fast
% 3.67/0.99  --preprocessed_out                      false
% 3.67/0.99  --preprocessed_stats                    false
% 3.67/0.99  
% 3.67/0.99  ------ Abstraction refinement Options
% 3.67/0.99  
% 3.67/0.99  --abstr_ref                             []
% 3.67/0.99  --abstr_ref_prep                        false
% 3.67/0.99  --abstr_ref_until_sat                   false
% 3.67/0.99  --abstr_ref_sig_restrict                funpre
% 3.67/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.67/0.99  --abstr_ref_under                       []
% 3.67/0.99  
% 3.67/0.99  ------ SAT Options
% 3.67/0.99  
% 3.67/0.99  --sat_mode                              false
% 3.67/0.99  --sat_fm_restart_options                ""
% 3.67/0.99  --sat_gr_def                            false
% 3.67/0.99  --sat_epr_types                         true
% 3.67/0.99  --sat_non_cyclic_types                  false
% 3.67/0.99  --sat_finite_models                     false
% 3.67/0.99  --sat_fm_lemmas                         false
% 3.67/0.99  --sat_fm_prep                           false
% 3.67/0.99  --sat_fm_uc_incr                        true
% 3.67/0.99  --sat_out_model                         small
% 3.67/0.99  --sat_out_clauses                       false
% 3.67/0.99  
% 3.67/0.99  ------ QBF Options
% 3.67/0.99  
% 3.67/0.99  --qbf_mode                              false
% 3.67/0.99  --qbf_elim_univ                         false
% 3.67/0.99  --qbf_dom_inst                          none
% 3.67/0.99  --qbf_dom_pre_inst                      false
% 3.67/0.99  --qbf_sk_in                             false
% 3.67/0.99  --qbf_pred_elim                         true
% 3.67/0.99  --qbf_split                             512
% 3.67/0.99  
% 3.67/0.99  ------ BMC1 Options
% 3.67/0.99  
% 3.67/0.99  --bmc1_incremental                      false
% 3.67/0.99  --bmc1_axioms                           reachable_all
% 3.67/0.99  --bmc1_min_bound                        0
% 3.67/0.99  --bmc1_max_bound                        -1
% 3.67/0.99  --bmc1_max_bound_default                -1
% 3.67/0.99  --bmc1_symbol_reachability              true
% 3.67/0.99  --bmc1_property_lemmas                  false
% 3.67/0.99  --bmc1_k_induction                      false
% 3.67/0.99  --bmc1_non_equiv_states                 false
% 3.67/0.99  --bmc1_deadlock                         false
% 3.67/0.99  --bmc1_ucm                              false
% 3.67/0.99  --bmc1_add_unsat_core                   none
% 3.67/0.99  --bmc1_unsat_core_children              false
% 3.67/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.67/0.99  --bmc1_out_stat                         full
% 3.67/0.99  --bmc1_ground_init                      false
% 3.67/0.99  --bmc1_pre_inst_next_state              false
% 3.67/0.99  --bmc1_pre_inst_state                   false
% 3.67/0.99  --bmc1_pre_inst_reach_state             false
% 3.67/0.99  --bmc1_out_unsat_core                   false
% 3.67/0.99  --bmc1_aig_witness_out                  false
% 3.67/0.99  --bmc1_verbose                          false
% 3.67/0.99  --bmc1_dump_clauses_tptp                false
% 3.67/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.67/0.99  --bmc1_dump_file                        -
% 3.67/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.67/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.67/0.99  --bmc1_ucm_extend_mode                  1
% 3.67/0.99  --bmc1_ucm_init_mode                    2
% 3.67/0.99  --bmc1_ucm_cone_mode                    none
% 3.67/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.67/0.99  --bmc1_ucm_relax_model                  4
% 3.67/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.67/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.67/0.99  --bmc1_ucm_layered_model                none
% 3.67/0.99  --bmc1_ucm_max_lemma_size               10
% 3.67/0.99  
% 3.67/0.99  ------ AIG Options
% 3.67/0.99  
% 3.67/0.99  --aig_mode                              false
% 3.67/0.99  
% 3.67/0.99  ------ Instantiation Options
% 3.67/0.99  
% 3.67/0.99  --instantiation_flag                    true
% 3.67/0.99  --inst_sos_flag                         true
% 3.67/0.99  --inst_sos_phase                        true
% 3.67/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.67/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.67/0.99  --inst_lit_sel_side                     num_symb
% 3.67/0.99  --inst_solver_per_active                1400
% 3.67/0.99  --inst_solver_calls_frac                1.
% 3.67/0.99  --inst_passive_queue_type               priority_queues
% 3.67/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.67/0.99  --inst_passive_queues_freq              [25;2]
% 3.67/0.99  --inst_dismatching                      true
% 3.67/0.99  --inst_eager_unprocessed_to_passive     true
% 3.67/0.99  --inst_prop_sim_given                   true
% 3.67/0.99  --inst_prop_sim_new                     false
% 3.67/0.99  --inst_subs_new                         false
% 3.67/0.99  --inst_eq_res_simp                      false
% 3.67/0.99  --inst_subs_given                       false
% 3.67/0.99  --inst_orphan_elimination               true
% 3.67/0.99  --inst_learning_loop_flag               true
% 3.67/0.99  --inst_learning_start                   3000
% 3.67/0.99  --inst_learning_factor                  2
% 3.67/0.99  --inst_start_prop_sim_after_learn       3
% 3.67/0.99  --inst_sel_renew                        solver
% 3.67/0.99  --inst_lit_activity_flag                true
% 3.67/0.99  --inst_restr_to_given                   false
% 3.67/0.99  --inst_activity_threshold               500
% 3.67/0.99  --inst_out_proof                        true
% 3.67/0.99  
% 3.67/0.99  ------ Resolution Options
% 3.67/0.99  
% 3.67/0.99  --resolution_flag                       true
% 3.67/0.99  --res_lit_sel                           adaptive
% 3.67/0.99  --res_lit_sel_side                      none
% 3.67/0.99  --res_ordering                          kbo
% 3.67/0.99  --res_to_prop_solver                    active
% 3.67/0.99  --res_prop_simpl_new                    false
% 3.67/0.99  --res_prop_simpl_given                  true
% 3.67/0.99  --res_passive_queue_type                priority_queues
% 3.67/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.67/0.99  --res_passive_queues_freq               [15;5]
% 3.67/0.99  --res_forward_subs                      full
% 3.67/0.99  --res_backward_subs                     full
% 3.67/0.99  --res_forward_subs_resolution           true
% 3.67/0.99  --res_backward_subs_resolution          true
% 3.67/0.99  --res_orphan_elimination                true
% 3.67/0.99  --res_time_limit                        2.
% 3.67/0.99  --res_out_proof                         true
% 3.67/0.99  
% 3.67/0.99  ------ Superposition Options
% 3.67/0.99  
% 3.67/0.99  --superposition_flag                    true
% 3.67/0.99  --sup_passive_queue_type                priority_queues
% 3.67/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.67/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.67/0.99  --demod_completeness_check              fast
% 3.67/0.99  --demod_use_ground                      true
% 3.67/0.99  --sup_to_prop_solver                    passive
% 3.67/0.99  --sup_prop_simpl_new                    true
% 3.67/0.99  --sup_prop_simpl_given                  true
% 3.67/0.99  --sup_fun_splitting                     true
% 3.67/0.99  --sup_smt_interval                      50000
% 3.67/0.99  
% 3.67/0.99  ------ Superposition Simplification Setup
% 3.67/0.99  
% 3.67/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.67/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.67/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.67/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.67/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.67/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.67/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.67/0.99  --sup_immed_triv                        [TrivRules]
% 3.67/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/0.99  --sup_immed_bw_main                     []
% 3.67/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.67/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.67/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/0.99  --sup_input_bw                          []
% 3.67/0.99  
% 3.67/0.99  ------ Combination Options
% 3.67/0.99  
% 3.67/0.99  --comb_res_mult                         3
% 3.67/0.99  --comb_sup_mult                         2
% 3.67/0.99  --comb_inst_mult                        10
% 3.67/0.99  
% 3.67/0.99  ------ Debug Options
% 3.67/0.99  
% 3.67/0.99  --dbg_backtrace                         false
% 3.67/0.99  --dbg_dump_prop_clauses                 false
% 3.67/0.99  --dbg_dump_prop_clauses_file            -
% 3.67/0.99  --dbg_out_stat                          false
% 3.67/0.99  ------ Parsing...
% 3.67/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.67/0.99  
% 3.67/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.67/0.99  
% 3.67/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.67/0.99  
% 3.67/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/0.99  ------ Proving...
% 3.67/0.99  ------ Problem Properties 
% 3.67/0.99  
% 3.67/0.99  
% 3.67/0.99  clauses                                 34
% 3.67/0.99  conjectures                             8
% 3.67/0.99  EPR                                     13
% 3.67/0.99  Horn                                    17
% 3.67/0.99  unary                                   8
% 3.67/0.99  binary                                  6
% 3.67/0.99  lits                                    111
% 3.67/0.99  lits eq                                 9
% 3.67/0.99  fd_pure                                 0
% 3.67/0.99  fd_pseudo                               0
% 3.67/0.99  fd_cond                                 0
% 3.67/0.99  fd_pseudo_cond                          3
% 3.67/0.99  AC symbols                              0
% 3.67/0.99  
% 3.67/0.99  ------ Schedule dynamic 5 is on 
% 3.67/0.99  
% 3.67/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.67/0.99  
% 3.67/0.99  
% 3.67/0.99  ------ 
% 3.67/0.99  Current options:
% 3.67/0.99  ------ 
% 3.67/0.99  
% 3.67/0.99  ------ Input Options
% 3.67/0.99  
% 3.67/0.99  --out_options                           all
% 3.67/0.99  --tptp_safe_out                         true
% 3.67/0.99  --problem_path                          ""
% 3.67/0.99  --include_path                          ""
% 3.67/0.99  --clausifier                            res/vclausify_rel
% 3.67/0.99  --clausifier_options                    ""
% 3.67/0.99  --stdin                                 false
% 3.67/0.99  --stats_out                             all
% 3.67/0.99  
% 3.67/0.99  ------ General Options
% 3.67/0.99  
% 3.67/0.99  --fof                                   false
% 3.67/0.99  --time_out_real                         305.
% 3.67/0.99  --time_out_virtual                      -1.
% 3.67/0.99  --symbol_type_check                     false
% 3.67/0.99  --clausify_out                          false
% 3.67/0.99  --sig_cnt_out                           false
% 3.67/0.99  --trig_cnt_out                          false
% 3.67/0.99  --trig_cnt_out_tolerance                1.
% 3.67/0.99  --trig_cnt_out_sk_spl                   false
% 3.67/0.99  --abstr_cl_out                          false
% 3.67/0.99  
% 3.67/0.99  ------ Global Options
% 3.67/0.99  
% 3.67/0.99  --schedule                              default
% 3.67/0.99  --add_important_lit                     false
% 3.67/0.99  --prop_solver_per_cl                    1000
% 3.67/0.99  --min_unsat_core                        false
% 3.67/0.99  --soft_assumptions                      false
% 3.67/0.99  --soft_lemma_size                       3
% 3.67/0.99  --prop_impl_unit_size                   0
% 3.67/0.99  --prop_impl_unit                        []
% 3.67/0.99  --share_sel_clauses                     true
% 3.67/0.99  --reset_solvers                         false
% 3.67/0.99  --bc_imp_inh                            [conj_cone]
% 3.67/0.99  --conj_cone_tolerance                   3.
% 3.67/0.99  --extra_neg_conj                        none
% 3.67/0.99  --large_theory_mode                     true
% 3.67/0.99  --prolific_symb_bound                   200
% 3.67/0.99  --lt_threshold                          2000
% 3.67/0.99  --clause_weak_htbl                      true
% 3.67/0.99  --gc_record_bc_elim                     false
% 3.67/0.99  
% 3.67/0.99  ------ Preprocessing Options
% 3.67/0.99  
% 3.67/0.99  --preprocessing_flag                    true
% 3.67/0.99  --time_out_prep_mult                    0.1
% 3.67/0.99  --splitting_mode                        input
% 3.67/0.99  --splitting_grd                         true
% 3.67/0.99  --splitting_cvd                         false
% 3.67/0.99  --splitting_cvd_svl                     false
% 3.67/0.99  --splitting_nvd                         32
% 3.67/0.99  --sub_typing                            true
% 3.67/0.99  --prep_gs_sim                           true
% 3.67/0.99  --prep_unflatten                        true
% 3.67/0.99  --prep_res_sim                          true
% 3.67/0.99  --prep_upred                            true
% 3.67/0.99  --prep_sem_filter                       exhaustive
% 3.67/0.99  --prep_sem_filter_out                   false
% 3.67/0.99  --pred_elim                             true
% 3.67/0.99  --res_sim_input                         true
% 3.67/0.99  --eq_ax_congr_red                       true
% 3.67/0.99  --pure_diseq_elim                       true
% 3.67/0.99  --brand_transform                       false
% 3.67/0.99  --non_eq_to_eq                          false
% 3.67/0.99  --prep_def_merge                        true
% 3.67/0.99  --prep_def_merge_prop_impl              false
% 3.67/0.99  --prep_def_merge_mbd                    true
% 3.67/0.99  --prep_def_merge_tr_red                 false
% 3.67/0.99  --prep_def_merge_tr_cl                  false
% 3.67/0.99  --smt_preprocessing                     true
% 3.67/0.99  --smt_ac_axioms                         fast
% 3.67/0.99  --preprocessed_out                      false
% 3.67/0.99  --preprocessed_stats                    false
% 3.67/0.99  
% 3.67/0.99  ------ Abstraction refinement Options
% 3.67/0.99  
% 3.67/0.99  --abstr_ref                             []
% 3.67/0.99  --abstr_ref_prep                        false
% 3.67/0.99  --abstr_ref_until_sat                   false
% 3.67/0.99  --abstr_ref_sig_restrict                funpre
% 3.67/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.67/0.99  --abstr_ref_under                       []
% 3.67/0.99  
% 3.67/0.99  ------ SAT Options
% 3.67/0.99  
% 3.67/0.99  --sat_mode                              false
% 3.67/0.99  --sat_fm_restart_options                ""
% 3.67/0.99  --sat_gr_def                            false
% 3.67/0.99  --sat_epr_types                         true
% 3.67/0.99  --sat_non_cyclic_types                  false
% 3.67/0.99  --sat_finite_models                     false
% 3.67/0.99  --sat_fm_lemmas                         false
% 3.67/0.99  --sat_fm_prep                           false
% 3.67/0.99  --sat_fm_uc_incr                        true
% 3.67/0.99  --sat_out_model                         small
% 3.67/0.99  --sat_out_clauses                       false
% 3.67/0.99  
% 3.67/0.99  ------ QBF Options
% 3.67/0.99  
% 3.67/0.99  --qbf_mode                              false
% 3.67/0.99  --qbf_elim_univ                         false
% 3.67/0.99  --qbf_dom_inst                          none
% 3.67/0.99  --qbf_dom_pre_inst                      false
% 3.67/0.99  --qbf_sk_in                             false
% 3.67/0.99  --qbf_pred_elim                         true
% 3.67/0.99  --qbf_split                             512
% 3.67/0.99  
% 3.67/0.99  ------ BMC1 Options
% 3.67/0.99  
% 3.67/0.99  --bmc1_incremental                      false
% 3.67/0.99  --bmc1_axioms                           reachable_all
% 3.67/0.99  --bmc1_min_bound                        0
% 3.67/0.99  --bmc1_max_bound                        -1
% 3.67/0.99  --bmc1_max_bound_default                -1
% 3.67/0.99  --bmc1_symbol_reachability              true
% 3.67/0.99  --bmc1_property_lemmas                  false
% 3.67/0.99  --bmc1_k_induction                      false
% 3.67/0.99  --bmc1_non_equiv_states                 false
% 3.67/0.99  --bmc1_deadlock                         false
% 3.67/0.99  --bmc1_ucm                              false
% 3.67/0.99  --bmc1_add_unsat_core                   none
% 3.67/0.99  --bmc1_unsat_core_children              false
% 3.67/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.67/0.99  --bmc1_out_stat                         full
% 3.67/0.99  --bmc1_ground_init                      false
% 3.67/0.99  --bmc1_pre_inst_next_state              false
% 3.67/0.99  --bmc1_pre_inst_state                   false
% 3.67/0.99  --bmc1_pre_inst_reach_state             false
% 3.67/0.99  --bmc1_out_unsat_core                   false
% 3.67/0.99  --bmc1_aig_witness_out                  false
% 3.67/0.99  --bmc1_verbose                          false
% 3.67/0.99  --bmc1_dump_clauses_tptp                false
% 3.67/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.67/0.99  --bmc1_dump_file                        -
% 3.67/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.67/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.67/0.99  --bmc1_ucm_extend_mode                  1
% 3.67/0.99  --bmc1_ucm_init_mode                    2
% 3.67/0.99  --bmc1_ucm_cone_mode                    none
% 3.67/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.67/0.99  --bmc1_ucm_relax_model                  4
% 3.67/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.67/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.67/0.99  --bmc1_ucm_layered_model                none
% 3.67/0.99  --bmc1_ucm_max_lemma_size               10
% 3.67/0.99  
% 3.67/0.99  ------ AIG Options
% 3.67/0.99  
% 3.67/0.99  --aig_mode                              false
% 3.67/0.99  
% 3.67/0.99  ------ Instantiation Options
% 3.67/0.99  
% 3.67/0.99  --instantiation_flag                    true
% 3.67/0.99  --inst_sos_flag                         true
% 3.67/0.99  --inst_sos_phase                        true
% 3.67/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.67/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.67/0.99  --inst_lit_sel_side                     none
% 3.67/0.99  --inst_solver_per_active                1400
% 3.67/0.99  --inst_solver_calls_frac                1.
% 3.67/0.99  --inst_passive_queue_type               priority_queues
% 3.67/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.67/0.99  --inst_passive_queues_freq              [25;2]
% 3.67/0.99  --inst_dismatching                      true
% 3.67/0.99  --inst_eager_unprocessed_to_passive     true
% 3.67/0.99  --inst_prop_sim_given                   true
% 3.67/0.99  --inst_prop_sim_new                     false
% 3.67/0.99  --inst_subs_new                         false
% 3.67/0.99  --inst_eq_res_simp                      false
% 3.67/0.99  --inst_subs_given                       false
% 3.67/0.99  --inst_orphan_elimination               true
% 3.67/0.99  --inst_learning_loop_flag               true
% 3.67/0.99  --inst_learning_start                   3000
% 3.67/0.99  --inst_learning_factor                  2
% 3.67/0.99  --inst_start_prop_sim_after_learn       3
% 3.67/0.99  --inst_sel_renew                        solver
% 3.67/0.99  --inst_lit_activity_flag                true
% 3.67/0.99  --inst_restr_to_given                   false
% 3.67/0.99  --inst_activity_threshold               500
% 3.67/0.99  --inst_out_proof                        true
% 3.67/0.99  
% 3.67/0.99  ------ Resolution Options
% 3.67/0.99  
% 3.67/0.99  --resolution_flag                       false
% 3.67/0.99  --res_lit_sel                           adaptive
% 3.67/0.99  --res_lit_sel_side                      none
% 3.67/0.99  --res_ordering                          kbo
% 3.67/0.99  --res_to_prop_solver                    active
% 3.67/0.99  --res_prop_simpl_new                    false
% 3.67/0.99  --res_prop_simpl_given                  true
% 3.67/0.99  --res_passive_queue_type                priority_queues
% 3.67/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.67/0.99  --res_passive_queues_freq               [15;5]
% 3.67/0.99  --res_forward_subs                      full
% 3.67/0.99  --res_backward_subs                     full
% 3.67/0.99  --res_forward_subs_resolution           true
% 3.67/0.99  --res_backward_subs_resolution          true
% 3.67/0.99  --res_orphan_elimination                true
% 3.67/0.99  --res_time_limit                        2.
% 3.67/0.99  --res_out_proof                         true
% 3.67/0.99  
% 3.67/0.99  ------ Superposition Options
% 3.67/0.99  
% 3.67/0.99  --superposition_flag                    true
% 3.67/0.99  --sup_passive_queue_type                priority_queues
% 3.67/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.67/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.67/0.99  --demod_completeness_check              fast
% 3.67/0.99  --demod_use_ground                      true
% 3.67/0.99  --sup_to_prop_solver                    passive
% 3.67/0.99  --sup_prop_simpl_new                    true
% 3.67/0.99  --sup_prop_simpl_given                  true
% 3.67/0.99  --sup_fun_splitting                     true
% 3.67/0.99  --sup_smt_interval                      50000
% 3.67/0.99  
% 3.67/0.99  ------ Superposition Simplification Setup
% 3.67/0.99  
% 3.67/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.67/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.67/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.67/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.67/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.67/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.67/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.67/0.99  --sup_immed_triv                        [TrivRules]
% 3.67/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/0.99  --sup_immed_bw_main                     []
% 3.67/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.67/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.67/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/0.99  --sup_input_bw                          []
% 3.67/0.99  
% 3.67/0.99  ------ Combination Options
% 3.67/0.99  
% 3.67/0.99  --comb_res_mult                         3
% 3.67/0.99  --comb_sup_mult                         2
% 3.67/0.99  --comb_inst_mult                        10
% 3.67/0.99  
% 3.67/0.99  ------ Debug Options
% 3.67/0.99  
% 3.67/0.99  --dbg_backtrace                         false
% 3.67/0.99  --dbg_dump_prop_clauses                 false
% 3.67/0.99  --dbg_dump_prop_clauses_file            -
% 3.67/0.99  --dbg_out_stat                          false
% 3.67/0.99  
% 3.67/0.99  
% 3.67/0.99  
% 3.67/0.99  
% 3.67/0.99  ------ Proving...
% 3.67/0.99  
% 3.67/0.99  
% 3.67/0.99  % SZS status Theorem for theBenchmark.p
% 3.67/0.99  
% 3.67/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.67/0.99  
% 3.67/0.99  fof(f22,conjecture,(
% 3.67/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f23,negated_conjecture,(
% 3.67/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.67/0.99    inference(negated_conjecture,[],[f22])).
% 3.67/0.99  
% 3.67/0.99  fof(f56,plain,(
% 3.67/0.99    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.67/0.99    inference(ennf_transformation,[],[f23])).
% 3.67/0.99  
% 3.67/0.99  fof(f57,plain,(
% 3.67/0.99    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.67/0.99    inference(flattening,[],[f56])).
% 3.67/0.99  
% 3.67/0.99  fof(f74,plain,(
% 3.67/0.99    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.67/0.99    inference(nnf_transformation,[],[f57])).
% 3.67/0.99  
% 3.67/0.99  fof(f75,plain,(
% 3.67/0.99    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.67/0.99    inference(flattening,[],[f74])).
% 3.67/0.99  
% 3.67/0.99  fof(f77,plain,(
% 3.67/0.99    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK6) | ~v2_tex_2(sK6,X0)) & (v1_zfmisc_1(sK6) | v2_tex_2(sK6,X0)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK6))) )),
% 3.67/0.99    introduced(choice_axiom,[])).
% 3.67/0.99  
% 3.67/0.99  fof(f76,plain,(
% 3.67/0.99    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK5)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK5)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK5) & v2_tdlat_3(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 3.67/0.99    introduced(choice_axiom,[])).
% 3.67/0.99  
% 3.67/0.99  fof(f78,plain,(
% 3.67/0.99    ((~v1_zfmisc_1(sK6) | ~v2_tex_2(sK6,sK5)) & (v1_zfmisc_1(sK6) | v2_tex_2(sK6,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) & ~v1_xboole_0(sK6)) & l1_pre_topc(sK5) & v2_tdlat_3(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)),
% 3.67/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f75,f77,f76])).
% 3.67/0.99  
% 3.67/0.99  fof(f118,plain,(
% 3.67/0.99    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))),
% 3.67/0.99    inference(cnf_transformation,[],[f78])).
% 3.67/0.99  
% 3.67/0.99  fof(f18,axiom,(
% 3.67/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f25,plain,(
% 3.67/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 3.67/0.99    inference(pure_predicate_removal,[],[f18])).
% 3.67/0.99  
% 3.67/0.99  fof(f48,plain,(
% 3.67/0.99    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.67/0.99    inference(ennf_transformation,[],[f25])).
% 3.67/0.99  
% 3.67/0.99  fof(f49,plain,(
% 3.67/0.99    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/0.99    inference(flattening,[],[f48])).
% 3.67/0.99  
% 3.67/0.99  fof(f70,plain,(
% 3.67/0.99    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(sK3(X0,X1)) = X1 & m1_pre_topc(sK3(X0,X1),X0) & ~v2_struct_0(sK3(X0,X1))))),
% 3.67/0.99    introduced(choice_axiom,[])).
% 3.67/0.99  
% 3.67/0.99  fof(f71,plain,(
% 3.67/0.99    ! [X0] : (! [X1] : ((u1_struct_0(sK3(X0,X1)) = X1 & m1_pre_topc(sK3(X0,X1),X0) & ~v2_struct_0(sK3(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f70])).
% 3.67/0.99  
% 3.67/0.99  fof(f105,plain,(
% 3.67/0.99    ( ! [X0,X1] : (m1_pre_topc(sK3(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f71])).
% 3.67/0.99  
% 3.67/0.99  fof(f113,plain,(
% 3.67/0.99    ~v2_struct_0(sK5)),
% 3.67/0.99    inference(cnf_transformation,[],[f78])).
% 3.67/0.99  
% 3.67/0.99  fof(f116,plain,(
% 3.67/0.99    l1_pre_topc(sK5)),
% 3.67/0.99    inference(cnf_transformation,[],[f78])).
% 3.67/0.99  
% 3.67/0.99  fof(f117,plain,(
% 3.67/0.99    ~v1_xboole_0(sK6)),
% 3.67/0.99    inference(cnf_transformation,[],[f78])).
% 3.67/0.99  
% 3.67/0.99  fof(f106,plain,(
% 3.67/0.99    ( ! [X0,X1] : (u1_struct_0(sK3(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f71])).
% 3.67/0.99  
% 3.67/0.99  fof(f13,axiom,(
% 3.67/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f38,plain,(
% 3.67/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.67/0.99    inference(ennf_transformation,[],[f13])).
% 3.67/0.99  
% 3.67/0.99  fof(f39,plain,(
% 3.67/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/0.99    inference(flattening,[],[f38])).
% 3.67/0.99  
% 3.67/0.99  fof(f97,plain,(
% 3.67/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f39])).
% 3.67/0.99  
% 3.67/0.99  fof(f104,plain,(
% 3.67/0.99    ( ! [X0,X1] : (~v2_struct_0(sK3(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f71])).
% 3.67/0.99  
% 3.67/0.99  fof(f119,plain,(
% 3.67/0.99    v1_zfmisc_1(sK6) | v2_tex_2(sK6,sK5)),
% 3.67/0.99    inference(cnf_transformation,[],[f78])).
% 3.67/0.99  
% 3.67/0.99  fof(f20,axiom,(
% 3.67/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f24,plain,(
% 3.67/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 3.67/0.99    inference(pure_predicate_removal,[],[f20])).
% 3.67/0.99  
% 3.67/0.99  fof(f52,plain,(
% 3.67/0.99    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.67/0.99    inference(ennf_transformation,[],[f24])).
% 3.67/0.99  
% 3.67/0.99  fof(f53,plain,(
% 3.67/0.99    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/0.99    inference(flattening,[],[f52])).
% 3.67/0.99  
% 3.67/0.99  fof(f72,plain,(
% 3.67/0.99    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK4(X0,X1)) = X1 & m1_pre_topc(sK4(X0,X1),X0) & v1_tdlat_3(sK4(X0,X1)) & ~v2_struct_0(sK4(X0,X1))))),
% 3.67/0.99    introduced(choice_axiom,[])).
% 3.67/0.99  
% 3.67/0.99  fof(f73,plain,(
% 3.67/0.99    ! [X0] : (! [X1] : ((u1_struct_0(sK4(X0,X1)) = X1 & m1_pre_topc(sK4(X0,X1),X0) & v1_tdlat_3(sK4(X0,X1)) & ~v2_struct_0(sK4(X0,X1))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f53,f72])).
% 3.67/0.99  
% 3.67/0.99  fof(f110,plain,(
% 3.67/0.99    ( ! [X0,X1] : (m1_pre_topc(sK4(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f73])).
% 3.67/0.99  
% 3.67/0.99  fof(f114,plain,(
% 3.67/0.99    v2_pre_topc(sK5)),
% 3.67/0.99    inference(cnf_transformation,[],[f78])).
% 3.67/0.99  
% 3.67/0.99  fof(f11,axiom,(
% 3.67/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f35,plain,(
% 3.67/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.67/0.99    inference(ennf_transformation,[],[f11])).
% 3.67/0.99  
% 3.67/0.99  fof(f95,plain,(
% 3.67/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f35])).
% 3.67/0.99  
% 3.67/0.99  fof(f15,axiom,(
% 3.67/0.99    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f42,plain,(
% 3.67/0.99    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 3.67/0.99    inference(ennf_transformation,[],[f15])).
% 3.67/0.99  
% 3.67/0.99  fof(f43,plain,(
% 3.67/0.99    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 3.67/0.99    inference(flattening,[],[f42])).
% 3.67/0.99  
% 3.67/0.99  fof(f99,plain,(
% 3.67/0.99    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f43])).
% 3.67/0.99  
% 3.67/0.99  fof(f120,plain,(
% 3.67/0.99    ~v1_zfmisc_1(sK6) | ~v2_tex_2(sK6,sK5)),
% 3.67/0.99    inference(cnf_transformation,[],[f78])).
% 3.67/0.99  
% 3.67/0.99  fof(f16,axiom,(
% 3.67/0.99    ! [X0] : (l1_pre_topc(X0) => ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0))))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f44,plain,(
% 3.67/0.99    ! [X0] : (((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | (~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.67/0.99    inference(ennf_transformation,[],[f16])).
% 3.67/0.99  
% 3.67/0.99  fof(f45,plain,(
% 3.67/0.99    ! [X0] : ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.67/0.99    inference(flattening,[],[f44])).
% 3.67/0.99  
% 3.67/0.99  fof(f101,plain,(
% 3.67/0.99    ( ! [X0] : (v7_struct_0(X0) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f45])).
% 3.67/0.99  
% 3.67/0.99  fof(f10,axiom,(
% 3.67/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f34,plain,(
% 3.67/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.67/0.99    inference(ennf_transformation,[],[f10])).
% 3.67/0.99  
% 3.67/0.99  fof(f94,plain,(
% 3.67/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f34])).
% 3.67/0.99  
% 3.67/0.99  fof(f12,axiom,(
% 3.67/0.99    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f36,plain,(
% 3.67/0.99    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 3.67/0.99    inference(ennf_transformation,[],[f12])).
% 3.67/0.99  
% 3.67/0.99  fof(f37,plain,(
% 3.67/0.99    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 3.67/0.99    inference(flattening,[],[f36])).
% 3.67/0.99  
% 3.67/0.99  fof(f96,plain,(
% 3.67/0.99    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f37])).
% 3.67/0.99  
% 3.67/0.99  fof(f109,plain,(
% 3.67/0.99    ( ! [X0,X1] : (v1_tdlat_3(sK4(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f73])).
% 3.67/0.99  
% 3.67/0.99  fof(f111,plain,(
% 3.67/0.99    ( ! [X0,X1] : (u1_struct_0(sK4(X0,X1)) = X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f73])).
% 3.67/0.99  
% 3.67/0.99  fof(f108,plain,(
% 3.67/0.99    ( ! [X0,X1] : (~v2_struct_0(sK4(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f73])).
% 3.67/0.99  
% 3.67/0.99  fof(f17,axiom,(
% 3.67/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f46,plain,(
% 3.67/0.99    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.67/0.99    inference(ennf_transformation,[],[f17])).
% 3.67/0.99  
% 3.67/0.99  fof(f47,plain,(
% 3.67/0.99    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/0.99    inference(flattening,[],[f46])).
% 3.67/0.99  
% 3.67/0.99  fof(f103,plain,(
% 3.67/0.99    ( ! [X0,X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f47])).
% 3.67/0.99  
% 3.67/0.99  fof(f115,plain,(
% 3.67/0.99    v2_tdlat_3(sK5)),
% 3.67/0.99    inference(cnf_transformation,[],[f78])).
% 3.67/0.99  
% 3.67/0.99  fof(f1,axiom,(
% 3.67/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f58,plain,(
% 3.67/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.67/0.99    inference(nnf_transformation,[],[f1])).
% 3.67/0.99  
% 3.67/0.99  fof(f59,plain,(
% 3.67/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.67/0.99    inference(rectify,[],[f58])).
% 3.67/0.99  
% 3.67/0.99  fof(f60,plain,(
% 3.67/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.67/0.99    introduced(choice_axiom,[])).
% 3.67/0.99  
% 3.67/0.99  fof(f61,plain,(
% 3.67/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.67/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f59,f60])).
% 3.67/0.99  
% 3.67/0.99  fof(f80,plain,(
% 3.67/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f61])).
% 3.67/0.99  
% 3.67/0.99  fof(f4,axiom,(
% 3.67/0.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f66,plain,(
% 3.67/0.99    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 3.67/0.99    inference(nnf_transformation,[],[f4])).
% 3.67/0.99  
% 3.67/0.99  fof(f87,plain,(
% 3.67/0.99    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f66])).
% 3.67/0.99  
% 3.67/0.99  fof(f19,axiom,(
% 3.67/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f50,plain,(
% 3.67/0.99    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 3.67/0.99    inference(ennf_transformation,[],[f19])).
% 3.67/0.99  
% 3.67/0.99  fof(f51,plain,(
% 3.67/0.99    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.67/0.99    inference(flattening,[],[f50])).
% 3.67/0.99  
% 3.67/0.99  fof(f107,plain,(
% 3.67/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f51])).
% 3.67/0.99  
% 3.67/0.99  fof(f3,axiom,(
% 3.67/0.99    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f85,plain,(
% 3.67/0.99    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 3.67/0.99    inference(cnf_transformation,[],[f3])).
% 3.67/0.99  
% 3.67/0.99  fof(f79,plain,(
% 3.67/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f61])).
% 3.67/0.99  
% 3.67/0.99  fof(f2,axiom,(
% 3.67/0.99    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f62,plain,(
% 3.67/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.67/0.99    inference(nnf_transformation,[],[f2])).
% 3.67/0.99  
% 3.67/0.99  fof(f63,plain,(
% 3.67/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.67/0.99    inference(rectify,[],[f62])).
% 3.67/0.99  
% 3.67/0.99  fof(f64,plain,(
% 3.67/0.99    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 3.67/0.99    introduced(choice_axiom,[])).
% 3.67/0.99  
% 3.67/0.99  fof(f65,plain,(
% 3.67/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.67/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f63,f64])).
% 3.67/0.99  
% 3.67/0.99  fof(f82,plain,(
% 3.67/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.67/0.99    inference(cnf_transformation,[],[f65])).
% 3.67/0.99  
% 3.67/0.99  fof(f121,plain,(
% 3.67/0.99    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 3.67/0.99    inference(equality_resolution,[],[f82])).
% 3.67/0.99  
% 3.67/0.99  fof(f122,plain,(
% 3.67/0.99    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 3.67/0.99    inference(equality_resolution,[],[f121])).
% 3.67/0.99  
% 3.67/0.99  fof(f6,axiom,(
% 3.67/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f27,plain,(
% 3.67/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.67/0.99    inference(ennf_transformation,[],[f6])).
% 3.67/0.99  
% 3.67/0.99  fof(f89,plain,(
% 3.67/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f27])).
% 3.67/0.99  
% 3.67/0.99  fof(f14,axiom,(
% 3.67/0.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f40,plain,(
% 3.67/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.67/0.99    inference(ennf_transformation,[],[f14])).
% 3.67/0.99  
% 3.67/0.99  fof(f41,plain,(
% 3.67/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.67/0.99    inference(flattening,[],[f40])).
% 3.67/0.99  
% 3.67/0.99  fof(f98,plain,(
% 3.67/0.99    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f41])).
% 3.67/0.99  
% 3.67/0.99  fof(f5,axiom,(
% 3.67/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f26,plain,(
% 3.67/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.67/0.99    inference(ennf_transformation,[],[f5])).
% 3.67/0.99  
% 3.67/0.99  fof(f88,plain,(
% 3.67/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f26])).
% 3.67/0.99  
% 3.67/0.99  fof(f21,axiom,(
% 3.67/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f54,plain,(
% 3.67/0.99    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.67/0.99    inference(ennf_transformation,[],[f21])).
% 3.67/0.99  
% 3.67/0.99  fof(f55,plain,(
% 3.67/0.99    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/0.99    inference(flattening,[],[f54])).
% 3.67/0.99  
% 3.67/0.99  fof(f112,plain,(
% 3.67/0.99    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f55])).
% 3.67/0.99  
% 3.67/0.99  cnf(c_36,negated_conjecture,
% 3.67/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 3.67/0.99      inference(cnf_transformation,[],[f118]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4342,plain,
% 3.67/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_26,plain,
% 3.67/0.99      ( m1_pre_topc(sK3(X0,X1),X0)
% 3.67/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.67/0.99      | v2_struct_0(X0)
% 3.67/0.99      | ~ l1_pre_topc(X0)
% 3.67/0.99      | v1_xboole_0(X1) ),
% 3.67/0.99      inference(cnf_transformation,[],[f105]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4351,plain,
% 3.67/0.99      ( m1_pre_topc(sK3(X0,X1),X0) = iProver_top
% 3.67/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.67/0.99      | v2_struct_0(X0) = iProver_top
% 3.67/0.99      | l1_pre_topc(X0) != iProver_top
% 3.67/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_5937,plain,
% 3.67/0.99      ( m1_pre_topc(sK3(sK5,sK6),sK5) = iProver_top
% 3.67/0.99      | v2_struct_0(sK5) = iProver_top
% 3.67/0.99      | l1_pre_topc(sK5) != iProver_top
% 3.67/0.99      | v1_xboole_0(sK6) = iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_4342,c_4351]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_41,negated_conjecture,
% 3.67/0.99      ( ~ v2_struct_0(sK5) ),
% 3.67/0.99      inference(cnf_transformation,[],[f113]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_42,plain,
% 3.67/0.99      ( v2_struct_0(sK5) != iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_38,negated_conjecture,
% 3.67/0.99      ( l1_pre_topc(sK5) ),
% 3.67/0.99      inference(cnf_transformation,[],[f116]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_45,plain,
% 3.67/0.99      ( l1_pre_topc(sK5) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_37,negated_conjecture,
% 3.67/0.99      ( ~ v1_xboole_0(sK6) ),
% 3.67/0.99      inference(cnf_transformation,[],[f117]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_46,plain,
% 3.67/0.99      ( v1_xboole_0(sK6) != iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_47,plain,
% 3.67/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4457,plain,
% 3.67/0.99      ( m1_pre_topc(sK3(X0,sK6),X0)
% 3.67/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
% 3.67/0.99      | v2_struct_0(X0)
% 3.67/0.99      | ~ l1_pre_topc(X0)
% 3.67/0.99      | v1_xboole_0(sK6) ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_26]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4473,plain,
% 3.67/0.99      ( m1_pre_topc(sK3(X0,sK6),X0) = iProver_top
% 3.67/0.99      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.67/0.99      | v2_struct_0(X0) = iProver_top
% 3.67/0.99      | l1_pre_topc(X0) != iProver_top
% 3.67/0.99      | v1_xboole_0(sK6) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_4457]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4475,plain,
% 3.67/0.99      ( m1_pre_topc(sK3(sK5,sK6),sK5) = iProver_top
% 3.67/0.99      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.67/0.99      | v2_struct_0(sK5) = iProver_top
% 3.67/0.99      | l1_pre_topc(sK5) != iProver_top
% 3.67/0.99      | v1_xboole_0(sK6) = iProver_top ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_4473]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_6213,plain,
% 3.67/0.99      ( m1_pre_topc(sK3(sK5,sK6),sK5) = iProver_top ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_5937,c_42,c_45,c_46,c_47,c_4475]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_25,plain,
% 3.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.67/0.99      | v2_struct_0(X1)
% 3.67/0.99      | ~ l1_pre_topc(X1)
% 3.67/0.99      | v1_xboole_0(X0)
% 3.67/0.99      | u1_struct_0(sK3(X1,X0)) = X0 ),
% 3.67/0.99      inference(cnf_transformation,[],[f106]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4352,plain,
% 3.67/0.99      ( u1_struct_0(sK3(X0,X1)) = X1
% 3.67/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.67/0.99      | v2_struct_0(X0) = iProver_top
% 3.67/0.99      | l1_pre_topc(X0) != iProver_top
% 3.67/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_5824,plain,
% 3.67/0.99      ( u1_struct_0(sK3(sK5,sK6)) = sK6
% 3.67/0.99      | v2_struct_0(sK5) = iProver_top
% 3.67/0.99      | l1_pre_topc(sK5) != iProver_top
% 3.67/0.99      | v1_xboole_0(sK6) = iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_4342,c_4352]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4418,plain,
% 3.67/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
% 3.67/0.99      | v2_struct_0(X0)
% 3.67/0.99      | ~ l1_pre_topc(X0)
% 3.67/0.99      | v1_xboole_0(sK6)
% 3.67/0.99      | u1_struct_0(sK3(X0,sK6)) = sK6 ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_25]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4438,plain,
% 3.67/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.67/0.99      | v2_struct_0(sK5)
% 3.67/0.99      | ~ l1_pre_topc(sK5)
% 3.67/0.99      | v1_xboole_0(sK6)
% 3.67/0.99      | u1_struct_0(sK3(sK5,sK6)) = sK6 ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_4418]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_6068,plain,
% 3.67/0.99      ( u1_struct_0(sK3(sK5,sK6)) = sK6 ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_5824,c_41,c_38,c_37,c_36,c_4438]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_18,plain,
% 3.67/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.67/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.67/0.99      | m1_subset_1(X2,u1_struct_0(X1))
% 3.67/0.99      | v2_struct_0(X1)
% 3.67/0.99      | v2_struct_0(X0)
% 3.67/0.99      | ~ l1_pre_topc(X1) ),
% 3.67/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4355,plain,
% 3.67/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.67/0.99      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.67/0.99      | m1_subset_1(X2,u1_struct_0(X1)) = iProver_top
% 3.67/0.99      | v2_struct_0(X0) = iProver_top
% 3.67/0.99      | v2_struct_0(X1) = iProver_top
% 3.67/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_6542,plain,
% 3.67/0.99      ( m1_pre_topc(sK3(sK5,sK6),X0) != iProver_top
% 3.67/0.99      | m1_subset_1(X1,u1_struct_0(X0)) = iProver_top
% 3.67/0.99      | m1_subset_1(X1,sK6) != iProver_top
% 3.67/0.99      | v2_struct_0(X0) = iProver_top
% 3.67/0.99      | v2_struct_0(sK3(sK5,sK6)) = iProver_top
% 3.67/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_6068,c_4355]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_27,plain,
% 3.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.67/0.99      | v2_struct_0(X1)
% 3.67/0.99      | ~ v2_struct_0(sK3(X1,X0))
% 3.67/0.99      | ~ l1_pre_topc(X1)
% 3.67/0.99      | v1_xboole_0(X0) ),
% 3.67/0.99      inference(cnf_transformation,[],[f104]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4419,plain,
% 3.67/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
% 3.67/0.99      | v2_struct_0(X0)
% 3.67/0.99      | ~ v2_struct_0(sK3(X0,sK6))
% 3.67/0.99      | ~ l1_pre_topc(X0)
% 3.67/0.99      | v1_xboole_0(sK6) ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_27]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4433,plain,
% 3.67/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.67/0.99      | v2_struct_0(X0) = iProver_top
% 3.67/0.99      | v2_struct_0(sK3(X0,sK6)) != iProver_top
% 3.67/0.99      | l1_pre_topc(X0) != iProver_top
% 3.67/0.99      | v1_xboole_0(sK6) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_4419]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4435,plain,
% 3.67/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.67/0.99      | v2_struct_0(sK3(sK5,sK6)) != iProver_top
% 3.67/0.99      | v2_struct_0(sK5) = iProver_top
% 3.67/0.99      | l1_pre_topc(sK5) != iProver_top
% 3.67/0.99      | v1_xboole_0(sK6) = iProver_top ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_4433]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_7566,plain,
% 3.67/0.99      ( v2_struct_0(X0) = iProver_top
% 3.67/0.99      | m1_subset_1(X1,sK6) != iProver_top
% 3.67/0.99      | m1_subset_1(X1,u1_struct_0(X0)) = iProver_top
% 3.67/0.99      | m1_pre_topc(sK3(sK5,sK6),X0) != iProver_top
% 3.67/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_6542,c_42,c_45,c_46,c_47,c_4435]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_7567,plain,
% 3.67/0.99      ( m1_pre_topc(sK3(sK5,sK6),X0) != iProver_top
% 3.67/0.99      | m1_subset_1(X1,u1_struct_0(X0)) = iProver_top
% 3.67/0.99      | m1_subset_1(X1,sK6) != iProver_top
% 3.67/0.99      | v2_struct_0(X0) = iProver_top
% 3.67/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.67/0.99      inference(renaming,[status(thm)],[c_7566]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_7572,plain,
% 3.67/0.99      ( m1_subset_1(X0,u1_struct_0(sK5)) = iProver_top
% 3.67/0.99      | m1_subset_1(X0,sK6) != iProver_top
% 3.67/0.99      | v2_struct_0(sK5) = iProver_top
% 3.67/0.99      | l1_pre_topc(sK5) != iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_6213,c_7567]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_7577,plain,
% 3.67/0.99      ( m1_subset_1(X0,u1_struct_0(sK5)) = iProver_top
% 3.67/0.99      | m1_subset_1(X0,sK6) != iProver_top ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_7572,c_42,c_45]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_35,negated_conjecture,
% 3.67/0.99      ( v2_tex_2(sK6,sK5) | v1_zfmisc_1(sK6) ),
% 3.67/0.99      inference(cnf_transformation,[],[f119]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4343,plain,
% 3.67/0.99      ( v2_tex_2(sK6,sK5) = iProver_top
% 3.67/0.99      | v1_zfmisc_1(sK6) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_30,plain,
% 3.67/0.99      ( ~ v2_tex_2(X0,X1)
% 3.67/0.99      | m1_pre_topc(sK4(X1,X0),X1)
% 3.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.67/0.99      | ~ v2_pre_topc(X1)
% 3.67/0.99      | v2_struct_0(X1)
% 3.67/0.99      | ~ l1_pre_topc(X1)
% 3.67/0.99      | v1_xboole_0(X0) ),
% 3.67/0.99      inference(cnf_transformation,[],[f110]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4348,plain,
% 3.67/0.99      ( v2_tex_2(X0,X1) != iProver_top
% 3.67/0.99      | m1_pre_topc(sK4(X1,X0),X1) = iProver_top
% 3.67/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.67/0.99      | v2_pre_topc(X1) != iProver_top
% 3.67/0.99      | v2_struct_0(X1) = iProver_top
% 3.67/0.99      | l1_pre_topc(X1) != iProver_top
% 3.67/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_6654,plain,
% 3.67/0.99      ( v2_tex_2(sK6,sK5) != iProver_top
% 3.67/0.99      | m1_pre_topc(sK4(sK5,sK6),sK5) = iProver_top
% 3.67/0.99      | v2_pre_topc(sK5) != iProver_top
% 3.67/0.99      | v2_struct_0(sK5) = iProver_top
% 3.67/0.99      | l1_pre_topc(sK5) != iProver_top
% 3.67/0.99      | v1_xboole_0(sK6) = iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_4342,c_4348]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_40,negated_conjecture,
% 3.67/0.99      ( v2_pre_topc(sK5) ),
% 3.67/0.99      inference(cnf_transformation,[],[f114]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_43,plain,
% 3.67/0.99      ( v2_pre_topc(sK5) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_6903,plain,
% 3.67/0.99      ( v2_tex_2(sK6,sK5) != iProver_top
% 3.67/0.99      | m1_pre_topc(sK4(sK5,sK6),sK5) = iProver_top ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_6654,c_42,c_43,c_45,c_46]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_16,plain,
% 3.67/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.67/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4356,plain,
% 3.67/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.67/0.99      | l1_pre_topc(X1) != iProver_top
% 3.67/0.99      | l1_pre_topc(X0) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_6907,plain,
% 3.67/0.99      ( v2_tex_2(sK6,sK5) != iProver_top
% 3.67/0.99      | l1_pre_topc(sK4(sK5,sK6)) = iProver_top
% 3.67/0.99      | l1_pre_topc(sK5) != iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_6903,c_4356]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_6912,plain,
% 3.67/0.99      ( l1_pre_topc(sK4(sK5,sK6)) = iProver_top
% 3.67/0.99      | v2_tex_2(sK6,sK5) != iProver_top ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_6907,c_45]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_6913,plain,
% 3.67/0.99      ( v2_tex_2(sK6,sK5) != iProver_top
% 3.67/0.99      | l1_pre_topc(sK4(sK5,sK6)) = iProver_top ),
% 3.67/0.99      inference(renaming,[status(thm)],[c_6912]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_20,plain,
% 3.67/0.99      ( ~ v2_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 3.67/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4353,plain,
% 3.67/0.99      ( v2_tdlat_3(X0) != iProver_top
% 3.67/0.99      | v2_pre_topc(X0) = iProver_top
% 3.67/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_6916,plain,
% 3.67/0.99      ( v2_tex_2(sK6,sK5) != iProver_top
% 3.67/0.99      | v2_tdlat_3(sK4(sK5,sK6)) != iProver_top
% 3.67/0.99      | v2_pre_topc(sK4(sK5,sK6)) = iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_6913,c_4353]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_34,negated_conjecture,
% 3.67/0.99      ( ~ v2_tex_2(sK6,sK5) | ~ v1_zfmisc_1(sK6) ),
% 3.67/0.99      inference(cnf_transformation,[],[f120]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_49,plain,
% 3.67/0.99      ( v2_tex_2(sK6,sK5) != iProver_top
% 3.67/0.99      | v1_zfmisc_1(sK6) != iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_3530,plain,( X0 = X0 ),theory(equality) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4680,plain,
% 3.67/0.99      ( sK6 = sK6 ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_3530]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_3531,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4529,plain,
% 3.67/0.99      ( X0 != X1 | sK6 != X1 | sK6 = X0 ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_3531]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4830,plain,
% 3.67/0.99      ( X0 != sK6 | sK6 = X0 | sK6 != sK6 ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_4529]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_5452,plain,
% 3.67/0.99      ( u1_struct_0(sK4(X0,sK6)) != sK6
% 3.67/0.99      | sK6 = u1_struct_0(sK4(X0,sK6))
% 3.67/0.99      | sK6 != sK6 ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_4830]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_5453,plain,
% 3.67/0.99      ( u1_struct_0(sK4(sK5,sK6)) != sK6
% 3.67/0.99      | sK6 = u1_struct_0(sK4(sK5,sK6))
% 3.67/0.99      | sK6 != sK6 ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_5452]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_22,plain,
% 3.67/0.99      ( ~ v1_tdlat_3(X0)
% 3.67/0.99      | ~ v2_tdlat_3(X0)
% 3.67/0.99      | ~ v2_pre_topc(X0)
% 3.67/0.99      | v2_struct_0(X0)
% 3.67/0.99      | v7_struct_0(X0)
% 3.67/0.99      | ~ l1_pre_topc(X0) ),
% 3.67/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_241,plain,
% 3.67/0.99      ( ~ v2_tdlat_3(X0)
% 3.67/0.99      | ~ v1_tdlat_3(X0)
% 3.67/0.99      | v2_struct_0(X0)
% 3.67/0.99      | v7_struct_0(X0)
% 3.67/0.99      | ~ l1_pre_topc(X0) ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_22,c_20]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_242,plain,
% 3.67/0.99      ( ~ v1_tdlat_3(X0)
% 3.67/0.99      | ~ v2_tdlat_3(X0)
% 3.67/0.99      | v2_struct_0(X0)
% 3.67/0.99      | v7_struct_0(X0)
% 3.67/0.99      | ~ l1_pre_topc(X0) ),
% 3.67/0.99      inference(renaming,[status(thm)],[c_241]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_15,plain,
% 3.67/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.67/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_17,plain,
% 3.67/0.99      ( ~ v7_struct_0(X0)
% 3.67/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 3.67/0.99      | ~ l1_struct_0(X0) ),
% 3.67/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_542,plain,
% 3.67/0.99      ( ~ v7_struct_0(X0)
% 3.67/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 3.67/0.99      | ~ l1_pre_topc(X0) ),
% 3.67/0.99      inference(resolution,[status(thm)],[c_15,c_17]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_560,plain,
% 3.67/0.99      ( ~ v1_tdlat_3(X0)
% 3.67/0.99      | ~ v2_tdlat_3(X0)
% 3.67/0.99      | v2_struct_0(X0)
% 3.67/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 3.67/0.99      | ~ l1_pre_topc(X0) ),
% 3.67/0.99      inference(resolution,[status(thm)],[c_242,c_542]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_5464,plain,
% 3.67/0.99      ( ~ v1_tdlat_3(sK4(X0,sK6))
% 3.67/0.99      | ~ v2_tdlat_3(sK4(X0,sK6))
% 3.67/0.99      | v2_struct_0(sK4(X0,sK6))
% 3.67/0.99      | v1_zfmisc_1(u1_struct_0(sK4(X0,sK6)))
% 3.67/0.99      | ~ l1_pre_topc(sK4(X0,sK6)) ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_560]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_5473,plain,
% 3.67/0.99      ( v1_tdlat_3(sK4(X0,sK6)) != iProver_top
% 3.67/0.99      | v2_tdlat_3(sK4(X0,sK6)) != iProver_top
% 3.67/0.99      | v2_struct_0(sK4(X0,sK6)) = iProver_top
% 3.67/0.99      | v1_zfmisc_1(u1_struct_0(sK4(X0,sK6))) = iProver_top
% 3.67/0.99      | l1_pre_topc(sK4(X0,sK6)) != iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_5464]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_5475,plain,
% 3.67/0.99      ( v1_tdlat_3(sK4(sK5,sK6)) != iProver_top
% 3.67/0.99      | v2_tdlat_3(sK4(sK5,sK6)) != iProver_top
% 3.67/0.99      | v2_struct_0(sK4(sK5,sK6)) = iProver_top
% 3.67/0.99      | v1_zfmisc_1(u1_struct_0(sK4(sK5,sK6))) = iProver_top
% 3.67/0.99      | l1_pre_topc(sK4(sK5,sK6)) != iProver_top ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_5473]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_31,plain,
% 3.67/0.99      ( ~ v2_tex_2(X0,X1)
% 3.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.67/0.99      | v1_tdlat_3(sK4(X1,X0))
% 3.67/0.99      | ~ v2_pre_topc(X1)
% 3.67/0.99      | v2_struct_0(X1)
% 3.67/0.99      | ~ l1_pre_topc(X1)
% 3.67/0.99      | v1_xboole_0(X0) ),
% 3.67/0.99      inference(cnf_transformation,[],[f109]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4347,plain,
% 3.67/0.99      ( v2_tex_2(X0,X1) != iProver_top
% 3.67/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.67/0.99      | v1_tdlat_3(sK4(X1,X0)) = iProver_top
% 3.67/0.99      | v2_pre_topc(X1) != iProver_top
% 3.67/0.99      | v2_struct_0(X1) = iProver_top
% 3.67/0.99      | l1_pre_topc(X1) != iProver_top
% 3.67/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_6551,plain,
% 3.67/0.99      ( v2_tex_2(sK6,sK5) != iProver_top
% 3.67/0.99      | v1_tdlat_3(sK4(sK5,sK6)) = iProver_top
% 3.67/0.99      | v2_pre_topc(sK5) != iProver_top
% 3.67/0.99      | v2_struct_0(sK5) = iProver_top
% 3.67/0.99      | l1_pre_topc(sK5) != iProver_top
% 3.67/0.99      | v1_xboole_0(sK6) = iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_4342,c_4347]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_6718,plain,
% 3.67/0.99      ( v2_tex_2(sK6,sK5) != iProver_top
% 3.67/0.99      | v1_tdlat_3(sK4(sK5,sK6)) = iProver_top ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_6551,c_42,c_43,c_45,c_46]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_29,plain,
% 3.67/0.99      ( ~ v2_tex_2(X0,X1)
% 3.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.67/0.99      | ~ v2_pre_topc(X1)
% 3.67/0.99      | v2_struct_0(X1)
% 3.67/0.99      | ~ l1_pre_topc(X1)
% 3.67/0.99      | v1_xboole_0(X0)
% 3.67/0.99      | u1_struct_0(sK4(X1,X0)) = X0 ),
% 3.67/0.99      inference(cnf_transformation,[],[f111]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4349,plain,
% 3.67/0.99      ( u1_struct_0(sK4(X0,X1)) = X1
% 3.67/0.99      | v2_tex_2(X1,X0) != iProver_top
% 3.67/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.67/0.99      | v2_pre_topc(X0) != iProver_top
% 3.67/0.99      | v2_struct_0(X0) = iProver_top
% 3.67/0.99      | l1_pre_topc(X0) != iProver_top
% 3.67/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_6639,plain,
% 3.67/0.99      ( u1_struct_0(sK4(sK5,sK6)) = sK6
% 3.67/0.99      | v2_tex_2(sK6,sK5) != iProver_top
% 3.67/0.99      | v2_pre_topc(sK5) != iProver_top
% 3.67/0.99      | v2_struct_0(sK5) = iProver_top
% 3.67/0.99      | l1_pre_topc(sK5) != iProver_top
% 3.67/0.99      | v1_xboole_0(sK6) = iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_4342,c_4349]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_6723,plain,
% 3.67/0.99      ( u1_struct_0(sK4(sK5,sK6)) = sK6
% 3.67/0.99      | v2_tex_2(sK6,sK5) != iProver_top ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_6639,c_42,c_43,c_45,c_46]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_32,plain,
% 3.67/0.99      ( ~ v2_tex_2(X0,X1)
% 3.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.67/0.99      | ~ v2_pre_topc(X1)
% 3.67/0.99      | v2_struct_0(X1)
% 3.67/0.99      | ~ v2_struct_0(sK4(X1,X0))
% 3.67/0.99      | ~ l1_pre_topc(X1)
% 3.67/0.99      | v1_xboole_0(X0) ),
% 3.67/0.99      inference(cnf_transformation,[],[f108]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4346,plain,
% 3.67/0.99      ( v2_tex_2(X0,X1) != iProver_top
% 3.67/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.67/0.99      | v2_pre_topc(X1) != iProver_top
% 3.67/0.99      | v2_struct_0(X1) = iProver_top
% 3.67/0.99      | v2_struct_0(sK4(X1,X0)) != iProver_top
% 3.67/0.99      | l1_pre_topc(X1) != iProver_top
% 3.67/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_6440,plain,
% 3.67/0.99      ( v2_tex_2(sK6,sK5) != iProver_top
% 3.67/0.99      | v2_pre_topc(sK5) != iProver_top
% 3.67/0.99      | v2_struct_0(sK4(sK5,sK6)) != iProver_top
% 3.67/0.99      | v2_struct_0(sK5) = iProver_top
% 3.67/0.99      | l1_pre_topc(sK5) != iProver_top
% 3.67/0.99      | v1_xboole_0(sK6) = iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_4342,c_4346]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_6807,plain,
% 3.67/0.99      ( v2_struct_0(sK4(sK5,sK6)) != iProver_top
% 3.67/0.99      | v2_tex_2(sK6,sK5) != iProver_top ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_6440,c_42,c_43,c_45,c_46]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_6808,plain,
% 3.67/0.99      ( v2_tex_2(sK6,sK5) != iProver_top
% 3.67/0.99      | v2_struct_0(sK4(sK5,sK6)) != iProver_top ),
% 3.67/0.99      inference(renaming,[status(thm)],[c_6807]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_24,plain,
% 3.67/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.67/0.99      | ~ v2_tdlat_3(X1)
% 3.67/0.99      | v2_tdlat_3(X0)
% 3.67/0.99      | ~ v2_pre_topc(X1)
% 3.67/0.99      | v2_struct_0(X1)
% 3.67/0.99      | ~ l1_pre_topc(X1) ),
% 3.67/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1574,plain,
% 3.67/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.67/0.99      | ~ v2_tdlat_3(X2)
% 3.67/0.99      | ~ v2_tdlat_3(X1)
% 3.67/0.99      | v2_tdlat_3(X0)
% 3.67/0.99      | v2_struct_0(X1)
% 3.67/0.99      | ~ l1_pre_topc(X2)
% 3.67/0.99      | ~ l1_pre_topc(X1)
% 3.67/0.99      | X1 != X2 ),
% 3.67/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_24]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1575,plain,
% 3.67/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.67/0.99      | ~ v2_tdlat_3(X1)
% 3.67/0.99      | v2_tdlat_3(X0)
% 3.67/0.99      | v2_struct_0(X1)
% 3.67/0.99      | ~ l1_pre_topc(X1) ),
% 3.67/0.99      inference(unflattening,[status(thm)],[c_1574]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4333,plain,
% 3.67/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.67/0.99      | v2_tdlat_3(X1) != iProver_top
% 3.67/0.99      | v2_tdlat_3(X0) = iProver_top
% 3.67/0.99      | v2_struct_0(X1) = iProver_top
% 3.67/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_1575]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_6908,plain,
% 3.67/0.99      ( v2_tex_2(sK6,sK5) != iProver_top
% 3.67/0.99      | v2_tdlat_3(sK4(sK5,sK6)) = iProver_top
% 3.67/0.99      | v2_tdlat_3(sK5) != iProver_top
% 3.67/0.99      | v2_struct_0(sK5) = iProver_top
% 3.67/0.99      | l1_pre_topc(sK5) != iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_6903,c_4333]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_39,negated_conjecture,
% 3.67/0.99      ( v2_tdlat_3(sK5) ),
% 3.67/0.99      inference(cnf_transformation,[],[f115]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_44,plain,
% 3.67/0.99      ( v2_tdlat_3(sK5) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_7002,plain,
% 3.67/0.99      ( v2_tdlat_3(sK4(sK5,sK6)) = iProver_top
% 3.67/0.99      | v2_tex_2(sK6,sK5) != iProver_top ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_6908,c_42,c_44,c_45]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_7003,plain,
% 3.67/0.99      ( v2_tex_2(sK6,sK5) != iProver_top
% 3.67/0.99      | v2_tdlat_3(sK4(sK5,sK6)) = iProver_top ),
% 3.67/0.99      inference(renaming,[status(thm)],[c_7002]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_3539,plain,
% 3.67/0.99      ( ~ v1_zfmisc_1(X0) | v1_zfmisc_1(X1) | X1 != X0 ),
% 3.67/0.99      theory(equality) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_5446,plain,
% 3.67/0.99      ( ~ v1_zfmisc_1(X0) | v1_zfmisc_1(sK6) | sK6 != X0 ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_3539]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_7438,plain,
% 3.67/0.99      ( ~ v1_zfmisc_1(u1_struct_0(sK4(X0,sK6)))
% 3.67/0.99      | v1_zfmisc_1(sK6)
% 3.67/0.99      | sK6 != u1_struct_0(sK4(X0,sK6)) ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_5446]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_7439,plain,
% 3.67/0.99      ( sK6 != u1_struct_0(sK4(X0,sK6))
% 3.67/0.99      | v1_zfmisc_1(u1_struct_0(sK4(X0,sK6))) != iProver_top
% 3.67/0.99      | v1_zfmisc_1(sK6) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_7438]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_7441,plain,
% 3.67/0.99      ( sK6 != u1_struct_0(sK4(sK5,sK6))
% 3.67/0.99      | v1_zfmisc_1(u1_struct_0(sK4(sK5,sK6))) != iProver_top
% 3.67/0.99      | v1_zfmisc_1(sK6) = iProver_top ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_7439]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_8311,plain,
% 3.67/0.99      ( v2_tex_2(sK6,sK5) != iProver_top ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_6916,c_45,c_49,c_4680,c_5453,c_5475,c_6718,c_6723,
% 3.67/0.99                 c_6808,c_6907,c_7003,c_7441]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_8315,plain,
% 3.67/0.99      ( v1_zfmisc_1(sK6) = iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_4343,c_8311]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_0,plain,
% 3.67/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.67/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4366,plain,
% 3.67/0.99      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.67/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_7,plain,
% 3.67/0.99      ( r1_tarski(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 3.67/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_319,plain,
% 3.67/0.99      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1) ),
% 3.67/0.99      inference(prop_impl,[status(thm)],[c_7]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_320,plain,
% 3.67/0.99      ( r1_tarski(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 3.67/0.99      inference(renaming,[status(thm)],[c_319]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_28,plain,
% 3.67/0.99      ( ~ r1_tarski(X0,X1)
% 3.67/0.99      | ~ v1_zfmisc_1(X1)
% 3.67/0.99      | v1_xboole_0(X0)
% 3.67/0.99      | v1_xboole_0(X1)
% 3.67/0.99      | X1 = X0 ),
% 3.67/0.99      inference(cnf_transformation,[],[f107]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_587,plain,
% 3.67/0.99      ( ~ r2_hidden(X0,X1)
% 3.67/0.99      | ~ v1_zfmisc_1(X2)
% 3.67/0.99      | v1_xboole_0(X3)
% 3.67/0.99      | v1_xboole_0(X2)
% 3.67/0.99      | X2 != X1
% 3.67/0.99      | X2 = X3
% 3.67/0.99      | k1_tarski(X0) != X3 ),
% 3.67/0.99      inference(resolution_lifted,[status(thm)],[c_320,c_28]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_588,plain,
% 3.67/0.99      ( ~ r2_hidden(X0,X1)
% 3.67/0.99      | ~ v1_zfmisc_1(X1)
% 3.67/0.99      | v1_xboole_0(X1)
% 3.67/0.99      | v1_xboole_0(k1_tarski(X0))
% 3.67/0.99      | X1 = k1_tarski(X0) ),
% 3.67/0.99      inference(unflattening,[status(thm)],[c_587]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_6,plain,
% 3.67/0.99      ( ~ v1_xboole_0(k1_tarski(X0)) ),
% 3.67/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1,plain,
% 3.67/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.67/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_592,plain,
% 3.67/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_zfmisc_1(X1) | X1 = k1_tarski(X0) ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_588,c_6,c_1]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4335,plain,
% 3.67/0.99      ( X0 = k1_tarski(X1)
% 3.67/0.99      | r2_hidden(X1,X0) != iProver_top
% 3.67/0.99      | v1_zfmisc_1(X0) != iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_592]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_5190,plain,
% 3.67/0.99      ( k1_tarski(sK0(X0)) = X0
% 3.67/0.99      | v1_zfmisc_1(X0) != iProver_top
% 3.67/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_4366,c_4335]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_8379,plain,
% 3.67/0.99      ( k1_tarski(sK0(sK6)) = sK6 | v1_xboole_0(sK6) = iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_8315,c_5190]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_8382,plain,
% 3.67/0.99      ( k1_tarski(sK0(sK6)) = sK6 ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_8379,c_46]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4,plain,
% 3.67/0.99      ( r2_hidden(X0,k1_tarski(X0)) ),
% 3.67/0.99      inference(cnf_transformation,[],[f122]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4362,plain,
% 3.67/0.99      ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_10,plain,
% 3.67/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.67/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4358,plain,
% 3.67/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 3.67/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4981,plain,
% 3.67/0.99      ( m1_subset_1(X0,k1_tarski(X0)) = iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_4362,c_4358]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_8388,plain,
% 3.67/0.99      ( m1_subset_1(sK0(sK6),sK6) = iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_8382,c_4981]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_19,plain,
% 3.67/0.99      ( ~ m1_subset_1(X0,X1)
% 3.67/0.99      | v1_xboole_0(X1)
% 3.67/0.99      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 3.67/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4354,plain,
% 3.67/0.99      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 3.67/0.99      | m1_subset_1(X1,X0) != iProver_top
% 3.67/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_7585,plain,
% 3.67/0.99      ( k6_domain_1(u1_struct_0(sK5),X0) = k1_tarski(X0)
% 3.67/0.99      | m1_subset_1(X0,sK6) != iProver_top
% 3.67/0.99      | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_7577,c_4354]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_9,plain,
% 3.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.67/0.99      | ~ v1_xboole_0(X1)
% 3.67/0.99      | v1_xboole_0(X0) ),
% 3.67/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4421,plain,
% 3.67/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
% 3.67/0.99      | ~ v1_xboole_0(X0)
% 3.67/0.99      | v1_xboole_0(sK6) ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4519,plain,
% 3.67/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.67/0.99      | ~ v1_xboole_0(u1_struct_0(sK5))
% 3.67/0.99      | v1_xboole_0(sK6) ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_4421]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4520,plain,
% 3.67/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.67/0.99      | v1_xboole_0(u1_struct_0(sK5)) != iProver_top
% 3.67/0.99      | v1_xboole_0(sK6) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_4519]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_8991,plain,
% 3.67/0.99      ( m1_subset_1(X0,sK6) != iProver_top
% 3.67/0.99      | k6_domain_1(u1_struct_0(sK5),X0) = k1_tarski(X0) ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_7585,c_46,c_47,c_4520]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_8992,plain,
% 3.67/0.99      ( k6_domain_1(u1_struct_0(sK5),X0) = k1_tarski(X0)
% 3.67/0.99      | m1_subset_1(X0,sK6) != iProver_top ),
% 3.67/0.99      inference(renaming,[status(thm)],[c_8991]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_9166,plain,
% 3.67/0.99      ( k6_domain_1(u1_struct_0(sK5),sK0(sK6)) = k1_tarski(sK0(sK6)) ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_8388,c_8992]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_9167,plain,
% 3.67/0.99      ( k6_domain_1(u1_struct_0(sK5),sK0(sK6)) = sK6 ),
% 3.67/0.99      inference(light_normalisation,[status(thm)],[c_9166,c_8382]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_33,plain,
% 3.67/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 3.67/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.67/0.99      | ~ v2_pre_topc(X0)
% 3.67/0.99      | v2_struct_0(X0)
% 3.67/0.99      | ~ l1_pre_topc(X0) ),
% 3.67/0.99      inference(cnf_transformation,[],[f112]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4345,plain,
% 3.67/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) = iProver_top
% 3.67/0.99      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.67/0.99      | v2_pre_topc(X0) != iProver_top
% 3.67/0.99      | v2_struct_0(X0) = iProver_top
% 3.67/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_9270,plain,
% 3.67/0.99      ( v2_tex_2(sK6,sK5) = iProver_top
% 3.67/0.99      | m1_subset_1(sK0(sK6),u1_struct_0(sK5)) != iProver_top
% 3.67/0.99      | v2_pre_topc(sK5) != iProver_top
% 3.67/0.99      | v2_struct_0(sK5) = iProver_top
% 3.67/0.99      | l1_pre_topc(sK5) != iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_9167,c_4345]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_11477,plain,
% 3.67/0.99      ( m1_subset_1(sK0(sK6),u1_struct_0(sK5)) != iProver_top ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_9270,c_42,c_43,c_45,c_49,c_4680,c_5453,c_5475,c_6718,
% 3.67/0.99                 c_6723,c_6808,c_6907,c_7003,c_7441]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_11481,plain,
% 3.67/0.99      ( m1_subset_1(sK0(sK6),sK6) != iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_7577,c_11477]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4534,plain,
% 3.67/0.99      ( m1_subset_1(X0,sK6) | ~ r2_hidden(X0,sK6) ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4782,plain,
% 3.67/0.99      ( m1_subset_1(sK0(sK6),sK6) | ~ r2_hidden(sK0(sK6),sK6) ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_4534]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4783,plain,
% 3.67/0.99      ( m1_subset_1(sK0(sK6),sK6) = iProver_top
% 3.67/0.99      | r2_hidden(sK0(sK6),sK6) != iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_4782]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4422,plain,
% 3.67/0.99      ( r2_hidden(sK0(sK6),sK6) | v1_xboole_0(sK6) ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4423,plain,
% 3.67/0.99      ( r2_hidden(sK0(sK6),sK6) = iProver_top
% 3.67/0.99      | v1_xboole_0(sK6) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_4422]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(contradiction,plain,
% 3.67/0.99      ( $false ),
% 3.67/0.99      inference(minisat,[status(thm)],[c_11481,c_4783,c_4423,c_46]) ).
% 3.67/0.99  
% 3.67/0.99  
% 3.67/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.67/0.99  
% 3.67/0.99  ------                               Statistics
% 3.67/0.99  
% 3.67/0.99  ------ General
% 3.67/0.99  
% 3.67/0.99  abstr_ref_over_cycles:                  0
% 3.67/0.99  abstr_ref_under_cycles:                 0
% 3.67/0.99  gc_basic_clause_elim:                   0
% 3.67/0.99  forced_gc_time:                         0
% 3.67/0.99  parsing_time:                           0.007
% 3.67/0.99  unif_index_cands_time:                  0.
% 3.67/0.99  unif_index_add_time:                    0.
% 3.67/0.99  orderings_time:                         0.
% 3.67/0.99  out_proof_time:                         0.014
% 3.67/0.99  total_time:                             0.255
% 3.67/0.99  num_of_symbols:                         57
% 3.67/0.99  num_of_terms:                           8082
% 3.67/0.99  
% 3.67/0.99  ------ Preprocessing
% 3.67/0.99  
% 3.67/0.99  num_of_splits:                          0
% 3.67/0.99  num_of_split_atoms:                     0
% 3.67/0.99  num_of_reused_defs:                     0
% 3.67/0.99  num_eq_ax_congr_red:                    41
% 3.67/0.99  num_of_sem_filtered_clauses:            1
% 3.67/0.99  num_of_subtypes:                        0
% 3.67/0.99  monotx_restored_types:                  0
% 3.67/0.99  sat_num_of_epr_types:                   0
% 3.67/0.99  sat_num_of_non_cyclic_types:            0
% 3.67/0.99  sat_guarded_non_collapsed_types:        0
% 3.67/0.99  num_pure_diseq_elim:                    0
% 3.67/0.99  simp_replaced_by:                       0
% 3.67/0.99  res_preprocessed:                       175
% 3.67/0.99  prep_upred:                             0
% 3.67/0.99  prep_unflattend:                        168
% 3.67/0.99  smt_new_axioms:                         0
% 3.67/0.99  pred_elim_cands:                        11
% 3.67/0.99  pred_elim:                              4
% 3.67/0.99  pred_elim_cl:                           6
% 3.67/0.99  pred_elim_cycles:                       18
% 3.67/0.99  merged_defs:                            10
% 3.67/0.99  merged_defs_ncl:                        0
% 3.67/0.99  bin_hyper_res:                          10
% 3.67/0.99  prep_cycles:                            4
% 3.67/0.99  pred_elim_time:                         0.029
% 3.67/0.99  splitting_time:                         0.
% 3.67/0.99  sem_filter_time:                        0.
% 3.67/0.99  monotx_time:                            0.
% 3.67/0.99  subtype_inf_time:                       0.
% 3.67/0.99  
% 3.67/0.99  ------ Problem properties
% 3.67/0.99  
% 3.67/0.99  clauses:                                34
% 3.67/0.99  conjectures:                            8
% 3.67/0.99  epr:                                    13
% 3.67/0.99  horn:                                   17
% 3.67/0.99  ground:                                 8
% 3.67/0.99  unary:                                  8
% 3.67/0.99  binary:                                 6
% 3.67/0.99  lits:                                   111
% 3.67/0.99  lits_eq:                                9
% 3.67/0.99  fd_pure:                                0
% 3.67/0.99  fd_pseudo:                              0
% 3.67/0.99  fd_cond:                                0
% 3.67/0.99  fd_pseudo_cond:                         3
% 3.67/0.99  ac_symbols:                             0
% 3.67/0.99  
% 3.67/0.99  ------ Propositional Solver
% 3.67/0.99  
% 3.67/0.99  prop_solver_calls:                      32
% 3.67/0.99  prop_fast_solver_calls:                 2344
% 3.67/0.99  smt_solver_calls:                       0
% 3.67/0.99  smt_fast_solver_calls:                  0
% 3.67/0.99  prop_num_of_clauses:                    4152
% 3.67/0.99  prop_preprocess_simplified:             11940
% 3.67/0.99  prop_fo_subsumed:                       182
% 3.67/0.99  prop_solver_time:                       0.
% 3.67/0.99  smt_solver_time:                        0.
% 3.67/0.99  smt_fast_solver_time:                   0.
% 3.67/0.99  prop_fast_solver_time:                  0.
% 3.67/0.99  prop_unsat_core_time:                   0.
% 3.67/0.99  
% 3.67/0.99  ------ QBF
% 3.67/0.99  
% 3.67/0.99  qbf_q_res:                              0
% 3.67/0.99  qbf_num_tautologies:                    0
% 3.67/0.99  qbf_prep_cycles:                        0
% 3.67/0.99  
% 3.67/0.99  ------ BMC1
% 3.67/0.99  
% 3.67/0.99  bmc1_current_bound:                     -1
% 3.67/0.99  bmc1_last_solved_bound:                 -1
% 3.67/0.99  bmc1_unsat_core_size:                   -1
% 3.67/0.99  bmc1_unsat_core_parents_size:           -1
% 3.67/0.99  bmc1_merge_next_fun:                    0
% 3.67/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.67/0.99  
% 3.67/0.99  ------ Instantiation
% 3.67/0.99  
% 3.67/0.99  inst_num_of_clauses:                    1152
% 3.67/0.99  inst_num_in_passive:                    501
% 3.67/0.99  inst_num_in_active:                     455
% 3.67/0.99  inst_num_in_unprocessed:                197
% 3.67/0.99  inst_num_of_loops:                      560
% 3.67/0.99  inst_num_of_learning_restarts:          0
% 3.67/0.99  inst_num_moves_active_passive:          101
% 3.67/0.99  inst_lit_activity:                      0
% 3.67/0.99  inst_lit_activity_moves:                0
% 3.67/0.99  inst_num_tautologies:                   0
% 3.67/0.99  inst_num_prop_implied:                  0
% 3.67/0.99  inst_num_existing_simplified:           0
% 3.67/0.99  inst_num_eq_res_simplified:             0
% 3.67/0.99  inst_num_child_elim:                    0
% 3.67/0.99  inst_num_of_dismatching_blockings:      467
% 3.67/0.99  inst_num_of_non_proper_insts:           1106
% 3.67/0.99  inst_num_of_duplicates:                 0
% 3.67/0.99  inst_inst_num_from_inst_to_res:         0
% 3.67/0.99  inst_dismatching_checking_time:         0.
% 3.67/0.99  
% 3.67/0.99  ------ Resolution
% 3.67/0.99  
% 3.67/0.99  res_num_of_clauses:                     0
% 3.67/0.99  res_num_in_passive:                     0
% 3.67/0.99  res_num_in_active:                      0
% 3.67/0.99  res_num_of_loops:                       179
% 3.67/0.99  res_forward_subset_subsumed:            54
% 3.67/0.99  res_backward_subset_subsumed:           14
% 3.67/0.99  res_forward_subsumed:                   0
% 3.67/0.99  res_backward_subsumed:                  1
% 3.67/0.99  res_forward_subsumption_resolution:     4
% 3.67/0.99  res_backward_subsumption_resolution:    0
% 3.67/0.99  res_clause_to_clause_subsumption:       414
% 3.67/0.99  res_orphan_elimination:                 0
% 3.67/0.99  res_tautology_del:                      113
% 3.67/0.99  res_num_eq_res_simplified:              0
% 3.67/0.99  res_num_sel_changes:                    0
% 3.67/0.99  res_moves_from_active_to_pass:          0
% 3.67/0.99  
% 3.67/0.99  ------ Superposition
% 3.67/0.99  
% 3.67/0.99  sup_time_total:                         0.
% 3.67/0.99  sup_time_generating:                    0.
% 3.67/0.99  sup_time_sim_full:                      0.
% 3.67/0.99  sup_time_sim_immed:                     0.
% 3.67/0.99  
% 3.67/0.99  sup_num_of_clauses:                     169
% 3.67/0.99  sup_num_in_active:                      98
% 3.67/0.99  sup_num_in_passive:                     71
% 3.67/0.99  sup_num_of_loops:                       111
% 3.67/0.99  sup_fw_superposition:                   122
% 3.67/0.99  sup_bw_superposition:                   159
% 3.67/0.99  sup_immediate_simplified:               67
% 3.67/0.99  sup_given_eliminated:                   0
% 3.67/0.99  comparisons_done:                       0
% 3.67/0.99  comparisons_avoided:                    64
% 3.67/0.99  
% 3.67/0.99  ------ Simplifications
% 3.67/0.99  
% 3.67/0.99  
% 3.67/0.99  sim_fw_subset_subsumed:                 33
% 3.67/0.99  sim_bw_subset_subsumed:                 15
% 3.67/0.99  sim_fw_subsumed:                        22
% 3.67/0.99  sim_bw_subsumed:                        6
% 3.67/0.99  sim_fw_subsumption_res:                 0
% 3.67/0.99  sim_bw_subsumption_res:                 0
% 3.67/0.99  sim_tautology_del:                      7
% 3.67/0.99  sim_eq_tautology_del:                   8
% 3.67/0.99  sim_eq_res_simp:                        0
% 3.67/0.99  sim_fw_demodulated:                     3
% 3.67/0.99  sim_bw_demodulated:                     2
% 3.67/0.99  sim_light_normalised:                   10
% 3.67/0.99  sim_joinable_taut:                      0
% 3.67/0.99  sim_joinable_simp:                      0
% 3.67/0.99  sim_ac_normalised:                      0
% 3.67/0.99  sim_smt_subsumption:                    0
% 3.67/0.99  
%------------------------------------------------------------------------------
