%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:51 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :  216 (1028 expanded)
%              Number of clauses        :  133 ( 338 expanded)
%              Number of leaves         :   24 ( 212 expanded)
%              Depth                    :   26
%              Number of atoms          :  836 (6013 expanded)
%              Number of equality atoms :  154 ( 379 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

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
    inference(nnf_transformation,[],[f45])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ( ~ v1_zfmisc_1(sK3)
          | ~ v2_tex_2(sK3,X0) )
        & ( v1_zfmisc_1(sK3)
          | v2_tex_2(sK3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
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
            | ~ v2_tex_2(X1,sK2) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK2)
      & v2_tdlat_3(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ( ~ v1_zfmisc_1(sK3)
      | ~ v2_tex_2(sK3,sK2) )
    & ( v1_zfmisc_1(sK3)
      | v2_tex_2(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & ~ v1_xboole_0(sK3)
    & l1_pre_topc(sK2)
    & v2_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f53,f55,f54])).

fof(f84,plain,
    ( v1_zfmisc_1(sK3)
    | v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f83,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f56])).

fof(f15,axiom,(
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
    inference(pure_predicate_removal,[],[f15])).

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK1(X0,X1)) = X1
        & m1_pre_topc(sK1(X0,X1),X0)
        & v1_tdlat_3(sK1(X0,X1))
        & ~ v2_struct_0(sK1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK1(X0,X1)) = X1
            & m1_pre_topc(sK1(X0,X1),X0)
            & v1_tdlat_3(sK1(X0,X1))
            & ~ v2_struct_0(sK1(X0,X1)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f50])).

fof(f76,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK1(X0,X1)) = X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f79,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f78,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f81,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f82,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).

fof(f58,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f72,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f85,plain,
    ( ~ v1_zfmisc_1(sK3)
    | ~ v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK1(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK1(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK1(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f13,axiom,(
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

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X1)
      | v7_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f64,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f66,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f69,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f80,plain,(
    v2_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_22,negated_conjecture,
    ( v2_tex_2(sK3,sK2)
    | v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1471,negated_conjecture,
    ( v2_tex_2(sK3,sK2)
    | v1_zfmisc_1(sK3) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1878,plain,
    ( v2_tex_2(sK3,sK2) = iProver_top
    | v1_zfmisc_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1471])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1470,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1879,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1470])).

cnf(c_16,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_943,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK1(X1,X0)) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_944,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | v1_xboole_0(X0)
    | u1_struct_0(sK1(sK2,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_943])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_948,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | u1_struct_0(sK1(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_944,c_28,c_25])).

cnf(c_1464,plain,
    ( ~ v2_tex_2(X0_50,sK2)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0_50)
    | u1_struct_0(sK1(sK2,X0_50)) = X0_50 ),
    inference(subtyping,[status(esa)],[c_948])).

cnf(c_1885,plain,
    ( u1_struct_0(sK1(sK2,X0_50)) = X0_50
    | v2_tex_2(X0_50,sK2) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1464])).

cnf(c_2094,plain,
    ( u1_struct_0(sK1(sK2,sK3)) = sK3
    | v2_tex_2(sK3,sK2) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1879,c_1885])).

cnf(c_24,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_33,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2198,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | u1_struct_0(sK1(sK2,sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2094,c_33])).

cnf(c_2199,plain,
    ( u1_struct_0(sK1(sK2,sK3)) = sK3
    | v2_tex_2(sK3,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2198])).

cnf(c_2204,plain,
    ( u1_struct_0(sK1(sK2,sK3)) = sK3
    | v1_zfmisc_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1878,c_2199])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_4,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_416,plain,
    ( m1_subset_1(X0,X1)
    | v1_xboole_0(X2)
    | X1 != X2
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_417,plain,
    ( m1_subset_1(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_1467,plain,
    ( m1_subset_1(sK0(X0_50),X0_50)
    | v1_xboole_0(X0_50) ),
    inference(subtyping,[status(esa)],[c_417])).

cnf(c_1882,plain,
    ( m1_subset_1(sK0(X0_50),X0_50) = iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1467])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1473,plain,
    ( ~ m1_subset_1(X0_50,X1_50)
    | v1_xboole_0(X1_50)
    | k6_domain_1(X1_50,X0_50) = k1_tarski(X0_50) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1876,plain,
    ( k6_domain_1(X0_50,X1_50) = k1_tarski(X1_50)
    | m1_subset_1(X1_50,X0_50) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1473])).

cnf(c_2721,plain,
    ( k6_domain_1(X0_50,sK0(X0_50)) = k1_tarski(sK0(X0_50))
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(superposition,[status(thm)],[c_1882,c_1876])).

cnf(c_1469,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1880,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1469])).

cnf(c_2897,plain,
    ( k6_domain_1(sK3,sK0(sK3)) = k1_tarski(sK0(sK3)) ),
    inference(superposition,[status(thm)],[c_2721,c_1880])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1474,plain,
    ( ~ m1_subset_1(X0_50,X1_50)
    | m1_subset_1(k6_domain_1(X1_50,X0_50),k1_zfmisc_1(X1_50))
    | v1_xboole_0(X1_50) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1875,plain,
    ( m1_subset_1(X0_50,X1_50) != iProver_top
    | m1_subset_1(k6_domain_1(X1_50,X0_50),k1_zfmisc_1(X1_50)) = iProver_top
    | v1_xboole_0(X1_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1474])).

cnf(c_3003,plain,
    ( m1_subset_1(k1_tarski(sK0(sK3)),k1_zfmisc_1(sK3)) = iProver_top
    | m1_subset_1(sK0(sK3),sK3) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2897,c_1875])).

cnf(c_1515,plain,
    ( m1_subset_1(sK0(X0_50),X0_50) = iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1467])).

cnf(c_1517,plain,
    ( m1_subset_1(sK0(sK3),sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1515])).

cnf(c_3175,plain,
    ( m1_subset_1(k1_tarski(sK0(sK3)),k1_zfmisc_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3003,c_33,c_1517])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_5,c_15])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_394,plain,
    ( v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_390,c_3])).

cnf(c_395,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | X1 = X0 ),
    inference(renaming,[status(thm)],[c_394])).

cnf(c_1468,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
    | ~ v1_zfmisc_1(X1_50)
    | v1_xboole_0(X0_50)
    | X1_50 = X0_50 ),
    inference(subtyping,[status(esa)],[c_395])).

cnf(c_1881,plain,
    ( X0_50 = X1_50
    | m1_subset_1(X1_50,k1_zfmisc_1(X0_50)) != iProver_top
    | v1_zfmisc_1(X0_50) != iProver_top
    | v1_xboole_0(X1_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1468])).

cnf(c_3182,plain,
    ( k1_tarski(sK0(sK3)) = sK3
    | v1_zfmisc_1(sK3) != iProver_top
    | v1_xboole_0(k1_tarski(sK0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3175,c_1881])).

cnf(c_34,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,negated_conjecture,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_36,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | v1_zfmisc_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1479,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_1499,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1479])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_430,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | v1_xboole_0(X3)
    | X2 != X3
    | sK0(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_6])).

cnf(c_431,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X0),X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_1466,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
    | m1_subset_1(sK0(X0_50),X1_50)
    | v1_xboole_0(X0_50) ),
    inference(subtyping,[status(esa)],[c_431])).

cnf(c_1999,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK0(X0_50),u1_struct_0(sK2))
    | v1_xboole_0(X0_50) ),
    inference(instantiation,[status(thm)],[c_1466])).

cnf(c_2002,plain,
    ( m1_subset_1(sK0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1999])).

cnf(c_2001,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK0(X0_50),u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1999])).

cnf(c_2003,plain,
    ( m1_subset_1(sK0(sK3),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2001])).

cnf(c_20,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_853,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_854,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_853])).

cnf(c_858,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_854,c_28,c_25])).

cnf(c_1465,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0_50),sK2)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_858])).

cnf(c_2000,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),sK0(X0_50)),sK2)
    | ~ m1_subset_1(sK0(X0_50),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1465])).

cnf(c_2005,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),sK0(X0_50)),sK2) = iProver_top
    | m1_subset_1(sK0(X0_50),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2000])).

cnf(c_2007,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),sK0(sK3)),sK2) = iProver_top
    | m1_subset_1(sK0(sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2005])).

cnf(c_1475,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
    | ~ v1_xboole_0(X1_50)
    | v1_xboole_0(X0_50) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2076,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0_50)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1475])).

cnf(c_2078,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2076])).

cnf(c_1488,plain,
    ( ~ v2_tex_2(X0_50,X0_51)
    | v2_tex_2(X1_50,X1_51)
    | X1_51 != X0_51
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_2108,plain,
    ( v2_tex_2(X0_50,X0_51)
    | ~ v2_tex_2(k6_domain_1(u1_struct_0(sK2),sK0(X1_50)),sK2)
    | X0_51 != sK2
    | X0_50 != k6_domain_1(u1_struct_0(sK2),sK0(X1_50)) ),
    inference(instantiation,[status(thm)],[c_1488])).

cnf(c_2109,plain,
    ( X0_51 != sK2
    | X0_50 != k6_domain_1(u1_struct_0(sK2),sK0(X1_50))
    | v2_tex_2(X0_50,X0_51) = iProver_top
    | v2_tex_2(k6_domain_1(u1_struct_0(sK2),sK0(X1_50)),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2108])).

cnf(c_2111,plain,
    ( sK2 != sK2
    | sK3 != k6_domain_1(u1_struct_0(sK2),sK0(sK3))
    | v2_tex_2(k6_domain_1(u1_struct_0(sK2),sK0(sK3)),sK2) != iProver_top
    | v2_tex_2(sK3,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2109])).

cnf(c_1480,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_2278,plain,
    ( X0_50 != X1_50
    | X0_50 = k6_domain_1(u1_struct_0(sK2),sK0(X2_50))
    | k6_domain_1(u1_struct_0(sK2),sK0(X2_50)) != X1_50 ),
    inference(instantiation,[status(thm)],[c_1480])).

cnf(c_2785,plain,
    ( X0_50 = k6_domain_1(u1_struct_0(sK2),sK0(X1_50))
    | X0_50 != k1_tarski(sK0(X1_50))
    | k6_domain_1(u1_struct_0(sK2),sK0(X1_50)) != k1_tarski(sK0(X1_50)) ),
    inference(instantiation,[status(thm)],[c_2278])).

cnf(c_2787,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK0(sK3)) != k1_tarski(sK0(sK3))
    | sK3 = k6_domain_1(u1_struct_0(sK2),sK0(sK3))
    | sK3 != k1_tarski(sK0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2785])).

cnf(c_2012,plain,
    ( ~ m1_subset_1(sK0(X0_50),X1_50)
    | v1_xboole_0(X1_50)
    | k6_domain_1(X1_50,sK0(X0_50)) = k1_tarski(sK0(X0_50)) ),
    inference(instantiation,[status(thm)],[c_1473])).

cnf(c_2786,plain,
    ( ~ m1_subset_1(sK0(X0_50),u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK0(X0_50)) = k1_tarski(sK0(X0_50)) ),
    inference(instantiation,[status(thm)],[c_2012])).

cnf(c_2789,plain,
    ( ~ m1_subset_1(sK0(sK3),u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK0(sK3)) = k1_tarski(sK0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2786])).

cnf(c_3235,plain,
    ( ~ m1_subset_1(k1_tarski(sK0(X0_50)),k1_zfmisc_1(X1_50))
    | ~ v1_zfmisc_1(X1_50)
    | v1_xboole_0(k1_tarski(sK0(X0_50)))
    | X1_50 = k1_tarski(sK0(X0_50)) ),
    inference(instantiation,[status(thm)],[c_1468])).

cnf(c_3236,plain,
    ( X0_50 = k1_tarski(sK0(X1_50))
    | m1_subset_1(k1_tarski(sK0(X1_50)),k1_zfmisc_1(X0_50)) != iProver_top
    | v1_zfmisc_1(X0_50) != iProver_top
    | v1_xboole_0(k1_tarski(sK0(X1_50))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3235])).

cnf(c_3238,plain,
    ( sK3 = k1_tarski(sK0(sK3))
    | m1_subset_1(k1_tarski(sK0(sK3)),k1_zfmisc_1(sK3)) != iProver_top
    | v1_zfmisc_1(sK3) != iProver_top
    | v1_xboole_0(k1_tarski(sK0(sK3))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3236])).

cnf(c_3278,plain,
    ( v1_zfmisc_1(sK3) != iProver_top
    | v1_xboole_0(k1_tarski(sK0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3182,c_24,c_33,c_23,c_34,c_36,c_1499,c_1517,c_2002,c_2003,c_2007,c_2078,c_2111,c_2787,c_2789,c_3003,c_3238])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1476,plain,
    ( ~ v1_xboole_0(k1_tarski(X0_50)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1873,plain,
    ( v1_xboole_0(k1_tarski(X0_50)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1476])).

cnf(c_3284,plain,
    ( v1_zfmisc_1(sK3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3278,c_1873])).

cnf(c_3286,plain,
    ( u1_struct_0(sK1(sK2,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_2204,c_3284])).

cnf(c_18,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v1_tdlat_3(sK1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_919,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v1_tdlat_3(sK1(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_920,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | v1_tdlat_3(sK1(sK2,X0))
    | ~ l1_pre_topc(sK2)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_919])).

cnf(c_924,plain,
    ( v1_tdlat_3(sK1(sK2,X0))
    | ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_920,c_28,c_25])).

cnf(c_925,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_tdlat_3(sK1(sK2,X0))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_924])).

cnf(c_19,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_895,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK1(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_27])).

cnf(c_896,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_struct_0(sK1(sK2,X0))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_895])).

cnf(c_900,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_struct_0(sK1(sK2,X0))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_896,c_28,c_25])).

cnf(c_17,plain,
    ( ~ v2_tex_2(X0,X1)
    | m1_pre_topc(sK1(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_7,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_9,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_372,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_7,c_9])).

cnf(c_452,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_13,c_372])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_456,plain,
    ( v1_zfmisc_1(u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_452,c_8])).

cnf(c_457,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_456])).

cnf(c_12,plain,
    ( ~ v2_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_476,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X1)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_457,c_12])).

cnf(c_26,negated_conjecture,
    ( v2_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_497,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_476,c_26])).

cnf(c_498,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ v1_tdlat_3(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_497])).

cnf(c_502,plain,
    ( v1_zfmisc_1(u1_struct_0(X0))
    | ~ v1_tdlat_3(X0)
    | ~ m1_pre_topc(X0,sK2)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_498,c_28,c_25])).

cnf(c_503,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(renaming,[status(thm)],[c_502])).

cnf(c_675,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X2)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK1(X1,X0) != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_503])).

cnf(c_676,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK1(sK2,X0))
    | v2_struct_0(sK2)
    | ~ v1_tdlat_3(sK1(sK2,X0))
    | ~ v2_pre_topc(sK2)
    | v1_zfmisc_1(u1_struct_0(sK1(sK2,X0)))
    | ~ l1_pre_topc(sK2)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_675])).

cnf(c_680,plain,
    ( v1_zfmisc_1(u1_struct_0(sK1(sK2,X0)))
    | v2_struct_0(sK1(sK2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | ~ v1_tdlat_3(sK1(sK2,X0))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_676,c_28,c_27,c_25])).

cnf(c_681,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK1(sK2,X0))
    | ~ v1_tdlat_3(sK1(sK2,X0))
    | v1_zfmisc_1(u1_struct_0(sK1(sK2,X0)))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_680])).

cnf(c_978,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_tdlat_3(sK1(sK2,X0))
    | v1_zfmisc_1(u1_struct_0(sK1(sK2,X0)))
    | v1_xboole_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_900,c_681])).

cnf(c_987,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_zfmisc_1(u1_struct_0(sK1(sK2,X0)))
    | v1_xboole_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_925,c_978])).

cnf(c_1463,plain,
    ( ~ v2_tex_2(X0_50,sK2)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_zfmisc_1(u1_struct_0(sK1(sK2,X0_50)))
    | v1_xboole_0(X0_50) ),
    inference(subtyping,[status(esa)],[c_987])).

cnf(c_1886,plain,
    ( v2_tex_2(X0_50,sK2) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1(sK2,X0_50))) = iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1463])).

cnf(c_2527,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1(sK2,sK3))) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1879,c_1886])).

cnf(c_2550,plain,
    ( v1_zfmisc_1(u1_struct_0(sK1(sK2,sK3))) = iProver_top
    | v2_tex_2(sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2527,c_33])).

cnf(c_2551,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1(sK2,sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_2550])).

cnf(c_3384,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | v1_zfmisc_1(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3286,c_2551])).

cnf(c_35,plain,
    ( v2_tex_2(sK3,sK2) = iProver_top
    | v1_zfmisc_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3384,c_3284,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:59:08 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 2.46/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/0.97  
% 2.46/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.46/0.97  
% 2.46/0.97  ------  iProver source info
% 2.46/0.97  
% 2.46/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.46/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.46/0.97  git: non_committed_changes: false
% 2.46/0.97  git: last_make_outside_of_git: false
% 2.46/0.97  
% 2.46/0.97  ------ 
% 2.46/0.97  
% 2.46/0.97  ------ Input Options
% 2.46/0.97  
% 2.46/0.97  --out_options                           all
% 2.46/0.97  --tptp_safe_out                         true
% 2.46/0.97  --problem_path                          ""
% 2.46/0.97  --include_path                          ""
% 2.46/0.97  --clausifier                            res/vclausify_rel
% 2.46/0.97  --clausifier_options                    --mode clausify
% 2.46/0.97  --stdin                                 false
% 2.46/0.97  --stats_out                             all
% 2.46/0.97  
% 2.46/0.97  ------ General Options
% 2.46/0.97  
% 2.46/0.97  --fof                                   false
% 2.46/0.97  --time_out_real                         305.
% 2.46/0.97  --time_out_virtual                      -1.
% 2.46/0.97  --symbol_type_check                     false
% 2.46/0.97  --clausify_out                          false
% 2.46/0.97  --sig_cnt_out                           false
% 2.46/0.97  --trig_cnt_out                          false
% 2.46/0.97  --trig_cnt_out_tolerance                1.
% 2.46/0.97  --trig_cnt_out_sk_spl                   false
% 2.46/0.97  --abstr_cl_out                          false
% 2.46/0.97  
% 2.46/0.97  ------ Global Options
% 2.46/0.97  
% 2.46/0.97  --schedule                              default
% 2.46/0.97  --add_important_lit                     false
% 2.46/0.97  --prop_solver_per_cl                    1000
% 2.46/0.97  --min_unsat_core                        false
% 2.46/0.97  --soft_assumptions                      false
% 2.46/0.97  --soft_lemma_size                       3
% 2.46/0.97  --prop_impl_unit_size                   0
% 2.46/0.97  --prop_impl_unit                        []
% 2.46/0.97  --share_sel_clauses                     true
% 2.46/0.97  --reset_solvers                         false
% 2.46/0.97  --bc_imp_inh                            [conj_cone]
% 2.46/0.97  --conj_cone_tolerance                   3.
% 2.46/0.97  --extra_neg_conj                        none
% 2.46/0.97  --large_theory_mode                     true
% 2.46/0.97  --prolific_symb_bound                   200
% 2.46/0.97  --lt_threshold                          2000
% 2.46/0.97  --clause_weak_htbl                      true
% 2.46/0.97  --gc_record_bc_elim                     false
% 2.46/0.97  
% 2.46/0.97  ------ Preprocessing Options
% 2.46/0.97  
% 2.46/0.97  --preprocessing_flag                    true
% 2.46/0.97  --time_out_prep_mult                    0.1
% 2.46/0.97  --splitting_mode                        input
% 2.46/0.97  --splitting_grd                         true
% 2.46/0.97  --splitting_cvd                         false
% 2.46/0.97  --splitting_cvd_svl                     false
% 2.46/0.97  --splitting_nvd                         32
% 2.46/0.97  --sub_typing                            true
% 2.46/0.97  --prep_gs_sim                           true
% 2.46/0.97  --prep_unflatten                        true
% 2.46/0.97  --prep_res_sim                          true
% 2.46/0.97  --prep_upred                            true
% 2.46/0.97  --prep_sem_filter                       exhaustive
% 2.46/0.97  --prep_sem_filter_out                   false
% 2.46/0.97  --pred_elim                             true
% 2.46/0.97  --res_sim_input                         true
% 2.46/0.97  --eq_ax_congr_red                       true
% 2.46/0.97  --pure_diseq_elim                       true
% 2.46/0.97  --brand_transform                       false
% 2.46/0.97  --non_eq_to_eq                          false
% 2.46/0.97  --prep_def_merge                        true
% 2.46/0.97  --prep_def_merge_prop_impl              false
% 2.46/0.98  --prep_def_merge_mbd                    true
% 2.46/0.98  --prep_def_merge_tr_red                 false
% 2.46/0.98  --prep_def_merge_tr_cl                  false
% 2.46/0.98  --smt_preprocessing                     true
% 2.46/0.98  --smt_ac_axioms                         fast
% 2.46/0.98  --preprocessed_out                      false
% 2.46/0.98  --preprocessed_stats                    false
% 2.46/0.98  
% 2.46/0.98  ------ Abstraction refinement Options
% 2.46/0.98  
% 2.46/0.98  --abstr_ref                             []
% 2.46/0.98  --abstr_ref_prep                        false
% 2.46/0.98  --abstr_ref_until_sat                   false
% 2.46/0.98  --abstr_ref_sig_restrict                funpre
% 2.46/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.46/0.98  --abstr_ref_under                       []
% 2.46/0.98  
% 2.46/0.98  ------ SAT Options
% 2.46/0.98  
% 2.46/0.98  --sat_mode                              false
% 2.46/0.98  --sat_fm_restart_options                ""
% 2.46/0.98  --sat_gr_def                            false
% 2.46/0.98  --sat_epr_types                         true
% 2.46/0.98  --sat_non_cyclic_types                  false
% 2.46/0.98  --sat_finite_models                     false
% 2.46/0.98  --sat_fm_lemmas                         false
% 2.46/0.98  --sat_fm_prep                           false
% 2.46/0.98  --sat_fm_uc_incr                        true
% 2.46/0.98  --sat_out_model                         small
% 2.46/0.98  --sat_out_clauses                       false
% 2.46/0.98  
% 2.46/0.98  ------ QBF Options
% 2.46/0.98  
% 2.46/0.98  --qbf_mode                              false
% 2.46/0.98  --qbf_elim_univ                         false
% 2.46/0.98  --qbf_dom_inst                          none
% 2.46/0.98  --qbf_dom_pre_inst                      false
% 2.46/0.98  --qbf_sk_in                             false
% 2.46/0.98  --qbf_pred_elim                         true
% 2.46/0.98  --qbf_split                             512
% 2.46/0.98  
% 2.46/0.98  ------ BMC1 Options
% 2.46/0.98  
% 2.46/0.98  --bmc1_incremental                      false
% 2.46/0.98  --bmc1_axioms                           reachable_all
% 2.46/0.98  --bmc1_min_bound                        0
% 2.46/0.98  --bmc1_max_bound                        -1
% 2.46/0.98  --bmc1_max_bound_default                -1
% 2.46/0.98  --bmc1_symbol_reachability              true
% 2.46/0.98  --bmc1_property_lemmas                  false
% 2.46/0.98  --bmc1_k_induction                      false
% 2.46/0.98  --bmc1_non_equiv_states                 false
% 2.46/0.98  --bmc1_deadlock                         false
% 2.46/0.98  --bmc1_ucm                              false
% 2.46/0.98  --bmc1_add_unsat_core                   none
% 2.46/0.98  --bmc1_unsat_core_children              false
% 2.46/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.46/0.98  --bmc1_out_stat                         full
% 2.46/0.98  --bmc1_ground_init                      false
% 2.46/0.98  --bmc1_pre_inst_next_state              false
% 2.46/0.98  --bmc1_pre_inst_state                   false
% 2.46/0.98  --bmc1_pre_inst_reach_state             false
% 2.46/0.98  --bmc1_out_unsat_core                   false
% 2.46/0.98  --bmc1_aig_witness_out                  false
% 2.46/0.98  --bmc1_verbose                          false
% 2.46/0.98  --bmc1_dump_clauses_tptp                false
% 2.46/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.46/0.98  --bmc1_dump_file                        -
% 2.46/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.46/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.46/0.98  --bmc1_ucm_extend_mode                  1
% 2.46/0.98  --bmc1_ucm_init_mode                    2
% 2.46/0.98  --bmc1_ucm_cone_mode                    none
% 2.46/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.46/0.98  --bmc1_ucm_relax_model                  4
% 2.46/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.46/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.46/0.98  --bmc1_ucm_layered_model                none
% 2.46/0.98  --bmc1_ucm_max_lemma_size               10
% 2.46/0.98  
% 2.46/0.98  ------ AIG Options
% 2.46/0.98  
% 2.46/0.98  --aig_mode                              false
% 2.46/0.98  
% 2.46/0.98  ------ Instantiation Options
% 2.46/0.98  
% 2.46/0.98  --instantiation_flag                    true
% 2.46/0.98  --inst_sos_flag                         false
% 2.46/0.98  --inst_sos_phase                        true
% 2.46/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.46/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.46/0.98  --inst_lit_sel_side                     num_symb
% 2.46/0.98  --inst_solver_per_active                1400
% 2.46/0.98  --inst_solver_calls_frac                1.
% 2.46/0.98  --inst_passive_queue_type               priority_queues
% 2.46/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.46/0.98  --inst_passive_queues_freq              [25;2]
% 2.46/0.98  --inst_dismatching                      true
% 2.46/0.98  --inst_eager_unprocessed_to_passive     true
% 2.46/0.98  --inst_prop_sim_given                   true
% 2.46/0.98  --inst_prop_sim_new                     false
% 2.46/0.98  --inst_subs_new                         false
% 2.46/0.98  --inst_eq_res_simp                      false
% 2.46/0.98  --inst_subs_given                       false
% 2.46/0.98  --inst_orphan_elimination               true
% 2.46/0.98  --inst_learning_loop_flag               true
% 2.46/0.98  --inst_learning_start                   3000
% 2.46/0.98  --inst_learning_factor                  2
% 2.46/0.98  --inst_start_prop_sim_after_learn       3
% 2.46/0.98  --inst_sel_renew                        solver
% 2.46/0.98  --inst_lit_activity_flag                true
% 2.46/0.98  --inst_restr_to_given                   false
% 2.46/0.98  --inst_activity_threshold               500
% 2.46/0.98  --inst_out_proof                        true
% 2.46/0.98  
% 2.46/0.98  ------ Resolution Options
% 2.46/0.98  
% 2.46/0.98  --resolution_flag                       true
% 2.46/0.98  --res_lit_sel                           adaptive
% 2.46/0.98  --res_lit_sel_side                      none
% 2.46/0.98  --res_ordering                          kbo
% 2.46/0.98  --res_to_prop_solver                    active
% 2.46/0.98  --res_prop_simpl_new                    false
% 2.46/0.98  --res_prop_simpl_given                  true
% 2.46/0.98  --res_passive_queue_type                priority_queues
% 2.46/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.46/0.98  --res_passive_queues_freq               [15;5]
% 2.46/0.98  --res_forward_subs                      full
% 2.46/0.98  --res_backward_subs                     full
% 2.46/0.98  --res_forward_subs_resolution           true
% 2.46/0.98  --res_backward_subs_resolution          true
% 2.46/0.98  --res_orphan_elimination                true
% 2.46/0.98  --res_time_limit                        2.
% 2.46/0.98  --res_out_proof                         true
% 2.46/0.98  
% 2.46/0.98  ------ Superposition Options
% 2.46/0.98  
% 2.46/0.98  --superposition_flag                    true
% 2.46/0.98  --sup_passive_queue_type                priority_queues
% 2.46/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.46/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.46/0.98  --demod_completeness_check              fast
% 2.46/0.98  --demod_use_ground                      true
% 2.46/0.98  --sup_to_prop_solver                    passive
% 2.46/0.98  --sup_prop_simpl_new                    true
% 2.46/0.98  --sup_prop_simpl_given                  true
% 2.46/0.98  --sup_fun_splitting                     false
% 2.46/0.98  --sup_smt_interval                      50000
% 2.46/0.98  
% 2.46/0.98  ------ Superposition Simplification Setup
% 2.46/0.98  
% 2.46/0.98  --sup_indices_passive                   []
% 2.46/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.46/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.98  --sup_full_bw                           [BwDemod]
% 2.46/0.98  --sup_immed_triv                        [TrivRules]
% 2.46/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.46/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.98  --sup_immed_bw_main                     []
% 2.46/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.46/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/0.98  
% 2.46/0.98  ------ Combination Options
% 2.46/0.98  
% 2.46/0.98  --comb_res_mult                         3
% 2.46/0.98  --comb_sup_mult                         2
% 2.46/0.98  --comb_inst_mult                        10
% 2.46/0.98  
% 2.46/0.98  ------ Debug Options
% 2.46/0.98  
% 2.46/0.98  --dbg_backtrace                         false
% 2.46/0.98  --dbg_dump_prop_clauses                 false
% 2.46/0.98  --dbg_dump_prop_clauses_file            -
% 2.46/0.98  --dbg_out_stat                          false
% 2.46/0.98  ------ Parsing...
% 2.46/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.46/0.98  
% 2.46/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.46/0.98  
% 2.46/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.46/0.98  
% 2.46/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.46/0.98  ------ Proving...
% 2.46/0.98  ------ Problem Properties 
% 2.46/0.98  
% 2.46/0.98  
% 2.46/0.98  clauses                                 14
% 2.46/0.98  conjectures                             4
% 2.46/0.98  EPR                                     3
% 2.46/0.98  Horn                                    6
% 2.46/0.98  unary                                   3
% 2.46/0.98  binary                                  4
% 2.46/0.98  lits                                    35
% 2.46/0.98  lits eq                                 3
% 2.46/0.98  fd_pure                                 0
% 2.46/0.98  fd_pseudo                               0
% 2.46/0.98  fd_cond                                 0
% 2.46/0.98  fd_pseudo_cond                          1
% 2.46/0.98  AC symbols                              0
% 2.46/0.98  
% 2.46/0.98  ------ Schedule dynamic 5 is on 
% 2.46/0.98  
% 2.46/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.46/0.98  
% 2.46/0.98  
% 2.46/0.98  ------ 
% 2.46/0.98  Current options:
% 2.46/0.98  ------ 
% 2.46/0.98  
% 2.46/0.98  ------ Input Options
% 2.46/0.98  
% 2.46/0.98  --out_options                           all
% 2.46/0.98  --tptp_safe_out                         true
% 2.46/0.98  --problem_path                          ""
% 2.46/0.98  --include_path                          ""
% 2.46/0.98  --clausifier                            res/vclausify_rel
% 2.46/0.98  --clausifier_options                    --mode clausify
% 2.46/0.98  --stdin                                 false
% 2.46/0.98  --stats_out                             all
% 2.46/0.98  
% 2.46/0.98  ------ General Options
% 2.46/0.98  
% 2.46/0.98  --fof                                   false
% 2.46/0.98  --time_out_real                         305.
% 2.46/0.98  --time_out_virtual                      -1.
% 2.46/0.98  --symbol_type_check                     false
% 2.46/0.98  --clausify_out                          false
% 2.46/0.98  --sig_cnt_out                           false
% 2.46/0.98  --trig_cnt_out                          false
% 2.46/0.98  --trig_cnt_out_tolerance                1.
% 2.46/0.98  --trig_cnt_out_sk_spl                   false
% 2.46/0.98  --abstr_cl_out                          false
% 2.46/0.98  
% 2.46/0.98  ------ Global Options
% 2.46/0.98  
% 2.46/0.98  --schedule                              default
% 2.46/0.98  --add_important_lit                     false
% 2.46/0.98  --prop_solver_per_cl                    1000
% 2.46/0.98  --min_unsat_core                        false
% 2.46/0.98  --soft_assumptions                      false
% 2.46/0.98  --soft_lemma_size                       3
% 2.46/0.98  --prop_impl_unit_size                   0
% 2.46/0.98  --prop_impl_unit                        []
% 2.46/0.98  --share_sel_clauses                     true
% 2.46/0.98  --reset_solvers                         false
% 2.46/0.98  --bc_imp_inh                            [conj_cone]
% 2.46/0.98  --conj_cone_tolerance                   3.
% 2.46/0.98  --extra_neg_conj                        none
% 2.46/0.98  --large_theory_mode                     true
% 2.46/0.98  --prolific_symb_bound                   200
% 2.46/0.98  --lt_threshold                          2000
% 2.46/0.98  --clause_weak_htbl                      true
% 2.46/0.98  --gc_record_bc_elim                     false
% 2.46/0.98  
% 2.46/0.98  ------ Preprocessing Options
% 2.46/0.98  
% 2.46/0.98  --preprocessing_flag                    true
% 2.46/0.98  --time_out_prep_mult                    0.1
% 2.46/0.98  --splitting_mode                        input
% 2.46/0.98  --splitting_grd                         true
% 2.46/0.98  --splitting_cvd                         false
% 2.46/0.98  --splitting_cvd_svl                     false
% 2.46/0.98  --splitting_nvd                         32
% 2.46/0.98  --sub_typing                            true
% 2.46/0.98  --prep_gs_sim                           true
% 2.46/0.98  --prep_unflatten                        true
% 2.46/0.98  --prep_res_sim                          true
% 2.46/0.98  --prep_upred                            true
% 2.46/0.98  --prep_sem_filter                       exhaustive
% 2.46/0.98  --prep_sem_filter_out                   false
% 2.46/0.98  --pred_elim                             true
% 2.46/0.98  --res_sim_input                         true
% 2.46/0.98  --eq_ax_congr_red                       true
% 2.46/0.98  --pure_diseq_elim                       true
% 2.46/0.98  --brand_transform                       false
% 2.46/0.98  --non_eq_to_eq                          false
% 2.46/0.98  --prep_def_merge                        true
% 2.46/0.98  --prep_def_merge_prop_impl              false
% 2.46/0.98  --prep_def_merge_mbd                    true
% 2.46/0.98  --prep_def_merge_tr_red                 false
% 2.46/0.98  --prep_def_merge_tr_cl                  false
% 2.46/0.98  --smt_preprocessing                     true
% 2.46/0.98  --smt_ac_axioms                         fast
% 2.46/0.98  --preprocessed_out                      false
% 2.46/0.98  --preprocessed_stats                    false
% 2.46/0.98  
% 2.46/0.98  ------ Abstraction refinement Options
% 2.46/0.98  
% 2.46/0.98  --abstr_ref                             []
% 2.46/0.98  --abstr_ref_prep                        false
% 2.46/0.98  --abstr_ref_until_sat                   false
% 2.46/0.98  --abstr_ref_sig_restrict                funpre
% 2.46/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.46/0.98  --abstr_ref_under                       []
% 2.46/0.98  
% 2.46/0.98  ------ SAT Options
% 2.46/0.98  
% 2.46/0.98  --sat_mode                              false
% 2.46/0.98  --sat_fm_restart_options                ""
% 2.46/0.98  --sat_gr_def                            false
% 2.46/0.98  --sat_epr_types                         true
% 2.46/0.98  --sat_non_cyclic_types                  false
% 2.46/0.98  --sat_finite_models                     false
% 2.46/0.98  --sat_fm_lemmas                         false
% 2.46/0.98  --sat_fm_prep                           false
% 2.46/0.98  --sat_fm_uc_incr                        true
% 2.46/0.98  --sat_out_model                         small
% 2.46/0.98  --sat_out_clauses                       false
% 2.46/0.98  
% 2.46/0.98  ------ QBF Options
% 2.46/0.98  
% 2.46/0.98  --qbf_mode                              false
% 2.46/0.98  --qbf_elim_univ                         false
% 2.46/0.98  --qbf_dom_inst                          none
% 2.46/0.98  --qbf_dom_pre_inst                      false
% 2.46/0.98  --qbf_sk_in                             false
% 2.46/0.98  --qbf_pred_elim                         true
% 2.46/0.98  --qbf_split                             512
% 2.46/0.98  
% 2.46/0.98  ------ BMC1 Options
% 2.46/0.98  
% 2.46/0.98  --bmc1_incremental                      false
% 2.46/0.98  --bmc1_axioms                           reachable_all
% 2.46/0.98  --bmc1_min_bound                        0
% 2.46/0.98  --bmc1_max_bound                        -1
% 2.46/0.98  --bmc1_max_bound_default                -1
% 2.46/0.98  --bmc1_symbol_reachability              true
% 2.46/0.98  --bmc1_property_lemmas                  false
% 2.46/0.98  --bmc1_k_induction                      false
% 2.46/0.98  --bmc1_non_equiv_states                 false
% 2.46/0.98  --bmc1_deadlock                         false
% 2.46/0.98  --bmc1_ucm                              false
% 2.46/0.98  --bmc1_add_unsat_core                   none
% 2.46/0.98  --bmc1_unsat_core_children              false
% 2.46/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.46/0.98  --bmc1_out_stat                         full
% 2.46/0.98  --bmc1_ground_init                      false
% 2.46/0.98  --bmc1_pre_inst_next_state              false
% 2.46/0.98  --bmc1_pre_inst_state                   false
% 2.46/0.98  --bmc1_pre_inst_reach_state             false
% 2.46/0.98  --bmc1_out_unsat_core                   false
% 2.46/0.98  --bmc1_aig_witness_out                  false
% 2.46/0.98  --bmc1_verbose                          false
% 2.46/0.98  --bmc1_dump_clauses_tptp                false
% 2.46/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.46/0.98  --bmc1_dump_file                        -
% 2.46/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.46/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.46/0.98  --bmc1_ucm_extend_mode                  1
% 2.46/0.98  --bmc1_ucm_init_mode                    2
% 2.46/0.98  --bmc1_ucm_cone_mode                    none
% 2.46/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.46/0.98  --bmc1_ucm_relax_model                  4
% 2.46/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.46/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.46/0.98  --bmc1_ucm_layered_model                none
% 2.46/0.98  --bmc1_ucm_max_lemma_size               10
% 2.46/0.98  
% 2.46/0.98  ------ AIG Options
% 2.46/0.98  
% 2.46/0.98  --aig_mode                              false
% 2.46/0.98  
% 2.46/0.98  ------ Instantiation Options
% 2.46/0.98  
% 2.46/0.98  --instantiation_flag                    true
% 2.46/0.98  --inst_sos_flag                         false
% 2.46/0.98  --inst_sos_phase                        true
% 2.46/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.46/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.46/0.98  --inst_lit_sel_side                     none
% 2.46/0.98  --inst_solver_per_active                1400
% 2.46/0.98  --inst_solver_calls_frac                1.
% 2.46/0.98  --inst_passive_queue_type               priority_queues
% 2.46/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.46/0.98  --inst_passive_queues_freq              [25;2]
% 2.46/0.98  --inst_dismatching                      true
% 2.46/0.98  --inst_eager_unprocessed_to_passive     true
% 2.46/0.98  --inst_prop_sim_given                   true
% 2.46/0.98  --inst_prop_sim_new                     false
% 2.46/0.98  --inst_subs_new                         false
% 2.46/0.98  --inst_eq_res_simp                      false
% 2.46/0.98  --inst_subs_given                       false
% 2.46/0.98  --inst_orphan_elimination               true
% 2.46/0.98  --inst_learning_loop_flag               true
% 2.46/0.98  --inst_learning_start                   3000
% 2.46/0.98  --inst_learning_factor                  2
% 2.46/0.98  --inst_start_prop_sim_after_learn       3
% 2.46/0.98  --inst_sel_renew                        solver
% 2.46/0.98  --inst_lit_activity_flag                true
% 2.46/0.98  --inst_restr_to_given                   false
% 2.46/0.98  --inst_activity_threshold               500
% 2.46/0.98  --inst_out_proof                        true
% 2.46/0.98  
% 2.46/0.98  ------ Resolution Options
% 2.46/0.98  
% 2.46/0.98  --resolution_flag                       false
% 2.46/0.98  --res_lit_sel                           adaptive
% 2.46/0.98  --res_lit_sel_side                      none
% 2.46/0.98  --res_ordering                          kbo
% 2.46/0.98  --res_to_prop_solver                    active
% 2.46/0.98  --res_prop_simpl_new                    false
% 2.46/0.98  --res_prop_simpl_given                  true
% 2.46/0.98  --res_passive_queue_type                priority_queues
% 2.46/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.46/0.98  --res_passive_queues_freq               [15;5]
% 2.46/0.98  --res_forward_subs                      full
% 2.46/0.98  --res_backward_subs                     full
% 2.46/0.98  --res_forward_subs_resolution           true
% 2.46/0.98  --res_backward_subs_resolution          true
% 2.46/0.98  --res_orphan_elimination                true
% 2.46/0.98  --res_time_limit                        2.
% 2.46/0.98  --res_out_proof                         true
% 2.46/0.98  
% 2.46/0.98  ------ Superposition Options
% 2.46/0.98  
% 2.46/0.98  --superposition_flag                    true
% 2.46/0.98  --sup_passive_queue_type                priority_queues
% 2.46/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.46/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.46/0.98  --demod_completeness_check              fast
% 2.46/0.98  --demod_use_ground                      true
% 2.46/0.98  --sup_to_prop_solver                    passive
% 2.46/0.98  --sup_prop_simpl_new                    true
% 2.46/0.98  --sup_prop_simpl_given                  true
% 2.46/0.98  --sup_fun_splitting                     false
% 2.46/0.98  --sup_smt_interval                      50000
% 2.46/0.98  
% 2.46/0.98  ------ Superposition Simplification Setup
% 2.46/0.98  
% 2.46/0.98  --sup_indices_passive                   []
% 2.46/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.46/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.98  --sup_full_bw                           [BwDemod]
% 2.46/0.98  --sup_immed_triv                        [TrivRules]
% 2.46/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.46/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.98  --sup_immed_bw_main                     []
% 2.46/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.46/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/0.98  
% 2.46/0.98  ------ Combination Options
% 2.46/0.98  
% 2.46/0.98  --comb_res_mult                         3
% 2.46/0.98  --comb_sup_mult                         2
% 2.46/0.98  --comb_inst_mult                        10
% 2.46/0.98  
% 2.46/0.98  ------ Debug Options
% 2.46/0.98  
% 2.46/0.98  --dbg_backtrace                         false
% 2.46/0.98  --dbg_dump_prop_clauses                 false
% 2.46/0.98  --dbg_dump_prop_clauses_file            -
% 2.46/0.98  --dbg_out_stat                          false
% 2.46/0.98  
% 2.46/0.98  
% 2.46/0.98  
% 2.46/0.98  
% 2.46/0.98  ------ Proving...
% 2.46/0.98  
% 2.46/0.98  
% 2.46/0.98  % SZS status Theorem for theBenchmark.p
% 2.46/0.98  
% 2.46/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.46/0.98  
% 2.46/0.98  fof(f17,conjecture,(
% 2.46/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 2.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f18,negated_conjecture,(
% 2.46/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 2.46/0.98    inference(negated_conjecture,[],[f17])).
% 2.46/0.98  
% 2.46/0.98  fof(f44,plain,(
% 2.46/0.98    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.46/0.98    inference(ennf_transformation,[],[f18])).
% 2.46/0.98  
% 2.46/0.98  fof(f45,plain,(
% 2.46/0.98    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.46/0.98    inference(flattening,[],[f44])).
% 2.46/0.98  
% 2.46/0.98  fof(f52,plain,(
% 2.46/0.98    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.46/0.98    inference(nnf_transformation,[],[f45])).
% 2.46/0.98  
% 2.46/0.98  fof(f53,plain,(
% 2.46/0.98    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.46/0.98    inference(flattening,[],[f52])).
% 2.46/0.98  
% 2.46/0.98  fof(f55,plain,(
% 2.46/0.98    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK3) | ~v2_tex_2(sK3,X0)) & (v1_zfmisc_1(sK3) | v2_tex_2(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK3))) )),
% 2.46/0.98    introduced(choice_axiom,[])).
% 2.46/0.98  
% 2.46/0.98  fof(f54,plain,(
% 2.46/0.98    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK2)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.46/0.98    introduced(choice_axiom,[])).
% 2.46/0.98  
% 2.46/0.98  fof(f56,plain,(
% 2.46/0.98    ((~v1_zfmisc_1(sK3) | ~v2_tex_2(sK3,sK2)) & (v1_zfmisc_1(sK3) | v2_tex_2(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.46/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f53,f55,f54])).
% 2.46/0.98  
% 2.46/0.98  fof(f84,plain,(
% 2.46/0.98    v1_zfmisc_1(sK3) | v2_tex_2(sK3,sK2)),
% 2.46/0.98    inference(cnf_transformation,[],[f56])).
% 2.46/0.98  
% 2.46/0.98  fof(f83,plain,(
% 2.46/0.98    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 2.46/0.98    inference(cnf_transformation,[],[f56])).
% 2.46/0.98  
% 2.46/0.98  fof(f15,axiom,(
% 2.46/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 2.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f20,plain,(
% 2.46/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 2.46/0.98    inference(pure_predicate_removal,[],[f15])).
% 2.46/0.98  
% 2.46/0.98  fof(f40,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.46/0.98    inference(ennf_transformation,[],[f20])).
% 2.46/0.98  
% 2.46/0.98  fof(f41,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.46/0.98    inference(flattening,[],[f40])).
% 2.46/0.98  
% 2.46/0.98  fof(f50,plain,(
% 2.46/0.98    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & v1_tdlat_3(sK1(X0,X1)) & ~v2_struct_0(sK1(X0,X1))))),
% 2.46/0.98    introduced(choice_axiom,[])).
% 2.46/0.98  
% 2.46/0.98  fof(f51,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : ((u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & v1_tdlat_3(sK1(X0,X1)) & ~v2_struct_0(sK1(X0,X1))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.46/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f50])).
% 2.46/0.98  
% 2.46/0.98  fof(f76,plain,(
% 2.46/0.98    ( ! [X0,X1] : (u1_struct_0(sK1(X0,X1)) = X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f51])).
% 2.46/0.98  
% 2.46/0.98  fof(f79,plain,(
% 2.46/0.98    v2_pre_topc(sK2)),
% 2.46/0.98    inference(cnf_transformation,[],[f56])).
% 2.46/0.98  
% 2.46/0.98  fof(f78,plain,(
% 2.46/0.98    ~v2_struct_0(sK2)),
% 2.46/0.98    inference(cnf_transformation,[],[f56])).
% 2.46/0.98  
% 2.46/0.98  fof(f81,plain,(
% 2.46/0.98    l1_pre_topc(sK2)),
% 2.46/0.98    inference(cnf_transformation,[],[f56])).
% 2.46/0.98  
% 2.46/0.98  fof(f82,plain,(
% 2.46/0.98    ~v1_xboole_0(sK3)),
% 2.46/0.98    inference(cnf_transformation,[],[f56])).
% 2.46/0.98  
% 2.46/0.98  fof(f1,axiom,(
% 2.46/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f46,plain,(
% 2.46/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.46/0.98    inference(nnf_transformation,[],[f1])).
% 2.46/0.98  
% 2.46/0.98  fof(f47,plain,(
% 2.46/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.46/0.98    inference(rectify,[],[f46])).
% 2.46/0.98  
% 2.46/0.98  fof(f48,plain,(
% 2.46/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.46/0.98    introduced(choice_axiom,[])).
% 2.46/0.98  
% 2.46/0.98  fof(f49,plain,(
% 2.46/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.46/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).
% 2.46/0.98  
% 2.46/0.98  fof(f58,plain,(
% 2.46/0.98    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f49])).
% 2.46/0.98  
% 2.46/0.98  fof(f4,axiom,(
% 2.46/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f22,plain,(
% 2.46/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.46/0.98    inference(ennf_transformation,[],[f4])).
% 2.46/0.98  
% 2.46/0.98  fof(f61,plain,(
% 2.46/0.98    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f22])).
% 2.46/0.98  
% 2.46/0.98  fof(f11,axiom,(
% 2.46/0.98    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f32,plain,(
% 2.46/0.98    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.46/0.98    inference(ennf_transformation,[],[f11])).
% 2.46/0.98  
% 2.46/0.98  fof(f33,plain,(
% 2.46/0.98    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.46/0.98    inference(flattening,[],[f32])).
% 2.46/0.98  
% 2.46/0.98  fof(f68,plain,(
% 2.46/0.98    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f33])).
% 2.46/0.98  
% 2.46/0.98  fof(f10,axiom,(
% 2.46/0.98    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f30,plain,(
% 2.46/0.98    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.46/0.98    inference(ennf_transformation,[],[f10])).
% 2.46/0.98  
% 2.46/0.98  fof(f31,plain,(
% 2.46/0.98    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.46/0.98    inference(flattening,[],[f30])).
% 2.46/0.98  
% 2.46/0.98  fof(f67,plain,(
% 2.46/0.98    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f31])).
% 2.46/0.98  
% 2.46/0.98  fof(f5,axiom,(
% 2.46/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f19,plain,(
% 2.46/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.46/0.98    inference(unused_predicate_definition_removal,[],[f5])).
% 2.46/0.98  
% 2.46/0.98  fof(f23,plain,(
% 2.46/0.98    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.46/0.98    inference(ennf_transformation,[],[f19])).
% 2.46/0.98  
% 2.46/0.98  fof(f62,plain,(
% 2.46/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.46/0.98    inference(cnf_transformation,[],[f23])).
% 2.46/0.98  
% 2.46/0.98  fof(f14,axiom,(
% 2.46/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 2.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f38,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 2.46/0.98    inference(ennf_transformation,[],[f14])).
% 2.46/0.98  
% 2.46/0.98  fof(f39,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.46/0.98    inference(flattening,[],[f38])).
% 2.46/0.98  
% 2.46/0.98  fof(f72,plain,(
% 2.46/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f39])).
% 2.46/0.98  
% 2.46/0.98  fof(f3,axiom,(
% 2.46/0.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f21,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.46/0.98    inference(ennf_transformation,[],[f3])).
% 2.46/0.98  
% 2.46/0.98  fof(f60,plain,(
% 2.46/0.98    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f21])).
% 2.46/0.98  
% 2.46/0.98  fof(f85,plain,(
% 2.46/0.98    ~v1_zfmisc_1(sK3) | ~v2_tex_2(sK3,sK2)),
% 2.46/0.98    inference(cnf_transformation,[],[f56])).
% 2.46/0.98  
% 2.46/0.98  fof(f6,axiom,(
% 2.46/0.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f24,plain,(
% 2.46/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.46/0.98    inference(ennf_transformation,[],[f6])).
% 2.46/0.98  
% 2.46/0.98  fof(f25,plain,(
% 2.46/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.46/0.98    inference(flattening,[],[f24])).
% 2.46/0.98  
% 2.46/0.98  fof(f63,plain,(
% 2.46/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f25])).
% 2.46/0.98  
% 2.46/0.98  fof(f16,axiom,(
% 2.46/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 2.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f42,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.46/0.98    inference(ennf_transformation,[],[f16])).
% 2.46/0.98  
% 2.46/0.98  fof(f43,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.46/0.98    inference(flattening,[],[f42])).
% 2.46/0.98  
% 2.46/0.98  fof(f77,plain,(
% 2.46/0.98    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f43])).
% 2.46/0.98  
% 2.46/0.98  fof(f2,axiom,(
% 2.46/0.98    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 2.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f59,plain,(
% 2.46/0.98    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 2.46/0.98    inference(cnf_transformation,[],[f2])).
% 2.46/0.98  
% 2.46/0.98  fof(f74,plain,(
% 2.46/0.98    ( ! [X0,X1] : (v1_tdlat_3(sK1(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f51])).
% 2.46/0.98  
% 2.46/0.98  fof(f73,plain,(
% 2.46/0.98    ( ! [X0,X1] : (~v2_struct_0(sK1(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f51])).
% 2.46/0.98  
% 2.46/0.98  fof(f75,plain,(
% 2.46/0.98    ( ! [X0,X1] : (m1_pre_topc(sK1(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f51])).
% 2.46/0.98  
% 2.46/0.98  fof(f13,axiom,(
% 2.46/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((~v7_struct_0(X1) & ~v2_struct_0(X1)) => (~v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 2.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f36,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : (((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.46/0.98    inference(ennf_transformation,[],[f13])).
% 2.46/0.98  
% 2.46/0.98  fof(f37,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : ((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.46/0.98    inference(flattening,[],[f36])).
% 2.46/0.98  
% 2.46/0.98  fof(f71,plain,(
% 2.46/0.98    ( ! [X0,X1] : (~v1_tdlat_3(X1) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f37])).
% 2.46/0.98  
% 2.46/0.98  fof(f7,axiom,(
% 2.46/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f26,plain,(
% 2.46/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.46/0.98    inference(ennf_transformation,[],[f7])).
% 2.46/0.98  
% 2.46/0.98  fof(f64,plain,(
% 2.46/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f26])).
% 2.46/0.98  
% 2.46/0.98  fof(f9,axiom,(
% 2.46/0.98    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 2.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f28,plain,(
% 2.46/0.98    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 2.46/0.98    inference(ennf_transformation,[],[f9])).
% 2.46/0.98  
% 2.46/0.98  fof(f29,plain,(
% 2.46/0.98    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 2.46/0.98    inference(flattening,[],[f28])).
% 2.46/0.98  
% 2.46/0.98  fof(f66,plain,(
% 2.46/0.98    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f29])).
% 2.46/0.98  
% 2.46/0.98  fof(f8,axiom,(
% 2.46/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f27,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.46/0.98    inference(ennf_transformation,[],[f8])).
% 2.46/0.98  
% 2.46/0.98  fof(f65,plain,(
% 2.46/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f27])).
% 2.46/0.98  
% 2.46/0.98  fof(f12,axiom,(
% 2.46/0.98    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 2.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f34,plain,(
% 2.46/0.98    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 2.46/0.98    inference(ennf_transformation,[],[f12])).
% 2.46/0.98  
% 2.46/0.98  fof(f35,plain,(
% 2.46/0.98    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 2.46/0.98    inference(flattening,[],[f34])).
% 2.46/0.98  
% 2.46/0.98  fof(f69,plain,(
% 2.46/0.98    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f35])).
% 2.46/0.98  
% 2.46/0.98  fof(f80,plain,(
% 2.46/0.98    v2_tdlat_3(sK2)),
% 2.46/0.98    inference(cnf_transformation,[],[f56])).
% 2.46/0.98  
% 2.46/0.98  cnf(c_22,negated_conjecture,
% 2.46/0.98      ( v2_tex_2(sK3,sK2) | v1_zfmisc_1(sK3) ),
% 2.46/0.98      inference(cnf_transformation,[],[f84]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1471,negated_conjecture,
% 2.46/0.98      ( v2_tex_2(sK3,sK2) | v1_zfmisc_1(sK3) ),
% 2.46/0.98      inference(subtyping,[status(esa)],[c_22]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1878,plain,
% 2.46/0.98      ( v2_tex_2(sK3,sK2) = iProver_top
% 2.46/0.98      | v1_zfmisc_1(sK3) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_1471]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_23,negated_conjecture,
% 2.46/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.46/0.98      inference(cnf_transformation,[],[f83]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1470,negated_conjecture,
% 2.46/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.46/0.98      inference(subtyping,[status(esa)],[c_23]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1879,plain,
% 2.46/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_1470]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_16,plain,
% 2.46/0.98      ( ~ v2_tex_2(X0,X1)
% 2.46/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | ~ v2_pre_topc(X1)
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | v1_xboole_0(X0)
% 2.46/0.98      | u1_struct_0(sK1(X1,X0)) = X0 ),
% 2.46/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_27,negated_conjecture,
% 2.46/0.98      ( v2_pre_topc(sK2) ),
% 2.46/0.98      inference(cnf_transformation,[],[f79]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_943,plain,
% 2.46/0.98      ( ~ v2_tex_2(X0,X1)
% 2.46/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | v1_xboole_0(X0)
% 2.46/0.98      | u1_struct_0(sK1(X1,X0)) = X0
% 2.46/0.98      | sK2 != X1 ),
% 2.46/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_944,plain,
% 2.46/0.98      ( ~ v2_tex_2(X0,sK2)
% 2.46/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.46/0.98      | v2_struct_0(sK2)
% 2.46/0.98      | ~ l1_pre_topc(sK2)
% 2.46/0.98      | v1_xboole_0(X0)
% 2.46/0.98      | u1_struct_0(sK1(sK2,X0)) = X0 ),
% 2.46/0.98      inference(unflattening,[status(thm)],[c_943]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_28,negated_conjecture,
% 2.46/0.98      ( ~ v2_struct_0(sK2) ),
% 2.46/0.98      inference(cnf_transformation,[],[f78]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_25,negated_conjecture,
% 2.46/0.98      ( l1_pre_topc(sK2) ),
% 2.46/0.98      inference(cnf_transformation,[],[f81]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_948,plain,
% 2.46/0.98      ( ~ v2_tex_2(X0,sK2)
% 2.46/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.46/0.98      | v1_xboole_0(X0)
% 2.46/0.98      | u1_struct_0(sK1(sK2,X0)) = X0 ),
% 2.46/0.98      inference(global_propositional_subsumption,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_944,c_28,c_25]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1464,plain,
% 2.46/0.98      ( ~ v2_tex_2(X0_50,sK2)
% 2.46/0.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.46/0.98      | v1_xboole_0(X0_50)
% 2.46/0.98      | u1_struct_0(sK1(sK2,X0_50)) = X0_50 ),
% 2.46/0.98      inference(subtyping,[status(esa)],[c_948]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1885,plain,
% 2.46/0.98      ( u1_struct_0(sK1(sK2,X0_50)) = X0_50
% 2.46/0.98      | v2_tex_2(X0_50,sK2) != iProver_top
% 2.46/0.98      | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.46/0.98      | v1_xboole_0(X0_50) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_1464]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2094,plain,
% 2.46/0.98      ( u1_struct_0(sK1(sK2,sK3)) = sK3
% 2.46/0.98      | v2_tex_2(sK3,sK2) != iProver_top
% 2.46/0.98      | v1_xboole_0(sK3) = iProver_top ),
% 2.46/0.98      inference(superposition,[status(thm)],[c_1879,c_1885]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_24,negated_conjecture,
% 2.46/0.98      ( ~ v1_xboole_0(sK3) ),
% 2.46/0.98      inference(cnf_transformation,[],[f82]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_33,plain,
% 2.46/0.98      ( v1_xboole_0(sK3) != iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2198,plain,
% 2.46/0.98      ( v2_tex_2(sK3,sK2) != iProver_top
% 2.46/0.98      | u1_struct_0(sK1(sK2,sK3)) = sK3 ),
% 2.46/0.98      inference(global_propositional_subsumption,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_2094,c_33]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2199,plain,
% 2.46/0.98      ( u1_struct_0(sK1(sK2,sK3)) = sK3
% 2.46/0.98      | v2_tex_2(sK3,sK2) != iProver_top ),
% 2.46/0.98      inference(renaming,[status(thm)],[c_2198]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2204,plain,
% 2.46/0.98      ( u1_struct_0(sK1(sK2,sK3)) = sK3
% 2.46/0.98      | v1_zfmisc_1(sK3) = iProver_top ),
% 2.46/0.98      inference(superposition,[status(thm)],[c_1878,c_2199]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_0,plain,
% 2.46/0.98      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.46/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_4,plain,
% 2.46/0.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.46/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_416,plain,
% 2.46/0.98      ( m1_subset_1(X0,X1) | v1_xboole_0(X2) | X1 != X2 | sK0(X2) != X0 ),
% 2.46/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_417,plain,
% 2.46/0.98      ( m1_subset_1(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.46/0.98      inference(unflattening,[status(thm)],[c_416]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1467,plain,
% 2.46/0.98      ( m1_subset_1(sK0(X0_50),X0_50) | v1_xboole_0(X0_50) ),
% 2.46/0.98      inference(subtyping,[status(esa)],[c_417]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1882,plain,
% 2.46/0.98      ( m1_subset_1(sK0(X0_50),X0_50) = iProver_top
% 2.46/0.98      | v1_xboole_0(X0_50) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_1467]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_11,plain,
% 2.46/0.98      ( ~ m1_subset_1(X0,X1)
% 2.46/0.98      | v1_xboole_0(X1)
% 2.46/0.98      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 2.46/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1473,plain,
% 2.46/0.98      ( ~ m1_subset_1(X0_50,X1_50)
% 2.46/0.98      | v1_xboole_0(X1_50)
% 2.46/0.98      | k6_domain_1(X1_50,X0_50) = k1_tarski(X0_50) ),
% 2.46/0.98      inference(subtyping,[status(esa)],[c_11]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1876,plain,
% 2.46/0.98      ( k6_domain_1(X0_50,X1_50) = k1_tarski(X1_50)
% 2.46/0.98      | m1_subset_1(X1_50,X0_50) != iProver_top
% 2.46/0.98      | v1_xboole_0(X0_50) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_1473]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2721,plain,
% 2.46/0.98      ( k6_domain_1(X0_50,sK0(X0_50)) = k1_tarski(sK0(X0_50))
% 2.46/0.98      | v1_xboole_0(X0_50) = iProver_top ),
% 2.46/0.98      inference(superposition,[status(thm)],[c_1882,c_1876]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1469,negated_conjecture,
% 2.46/0.98      ( ~ v1_xboole_0(sK3) ),
% 2.46/0.98      inference(subtyping,[status(esa)],[c_24]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1880,plain,
% 2.46/0.98      ( v1_xboole_0(sK3) != iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_1469]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2897,plain,
% 2.46/0.98      ( k6_domain_1(sK3,sK0(sK3)) = k1_tarski(sK0(sK3)) ),
% 2.46/0.98      inference(superposition,[status(thm)],[c_2721,c_1880]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_10,plain,
% 2.46/0.98      ( ~ m1_subset_1(X0,X1)
% 2.46/0.98      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 2.46/0.98      | v1_xboole_0(X1) ),
% 2.46/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1474,plain,
% 2.46/0.98      ( ~ m1_subset_1(X0_50,X1_50)
% 2.46/0.98      | m1_subset_1(k6_domain_1(X1_50,X0_50),k1_zfmisc_1(X1_50))
% 2.46/0.98      | v1_xboole_0(X1_50) ),
% 2.46/0.98      inference(subtyping,[status(esa)],[c_10]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1875,plain,
% 2.46/0.98      ( m1_subset_1(X0_50,X1_50) != iProver_top
% 2.46/0.98      | m1_subset_1(k6_domain_1(X1_50,X0_50),k1_zfmisc_1(X1_50)) = iProver_top
% 2.46/0.98      | v1_xboole_0(X1_50) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_1474]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_3003,plain,
% 2.46/0.98      ( m1_subset_1(k1_tarski(sK0(sK3)),k1_zfmisc_1(sK3)) = iProver_top
% 2.46/0.98      | m1_subset_1(sK0(sK3),sK3) != iProver_top
% 2.46/0.98      | v1_xboole_0(sK3) = iProver_top ),
% 2.46/0.98      inference(superposition,[status(thm)],[c_2897,c_1875]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1515,plain,
% 2.46/0.98      ( m1_subset_1(sK0(X0_50),X0_50) = iProver_top
% 2.46/0.98      | v1_xboole_0(X0_50) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_1467]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1517,plain,
% 2.46/0.98      ( m1_subset_1(sK0(sK3),sK3) = iProver_top
% 2.46/0.98      | v1_xboole_0(sK3) = iProver_top ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_1515]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_3175,plain,
% 2.46/0.98      ( m1_subset_1(k1_tarski(sK0(sK3)),k1_zfmisc_1(sK3)) = iProver_top ),
% 2.46/0.98      inference(global_propositional_subsumption,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_3003,c_33,c_1517]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_5,plain,
% 2.46/0.98      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.46/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_15,plain,
% 2.46/0.98      ( ~ r1_tarski(X0,X1)
% 2.46/0.98      | ~ v1_zfmisc_1(X1)
% 2.46/0.98      | v1_xboole_0(X0)
% 2.46/0.98      | v1_xboole_0(X1)
% 2.46/0.98      | X1 = X0 ),
% 2.46/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_390,plain,
% 2.46/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.46/0.98      | ~ v1_zfmisc_1(X1)
% 2.46/0.98      | v1_xboole_0(X0)
% 2.46/0.98      | v1_xboole_0(X1)
% 2.46/0.98      | X1 = X0 ),
% 2.46/0.98      inference(resolution,[status(thm)],[c_5,c_15]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_3,plain,
% 2.46/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.46/0.98      | ~ v1_xboole_0(X1)
% 2.46/0.98      | v1_xboole_0(X0) ),
% 2.46/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_394,plain,
% 2.46/0.98      ( v1_xboole_0(X0)
% 2.46/0.98      | ~ v1_zfmisc_1(X1)
% 2.46/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.46/0.98      | X1 = X0 ),
% 2.46/0.98      inference(global_propositional_subsumption,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_390,c_3]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_395,plain,
% 2.46/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.46/0.98      | ~ v1_zfmisc_1(X1)
% 2.46/0.98      | v1_xboole_0(X0)
% 2.46/0.98      | X1 = X0 ),
% 2.46/0.98      inference(renaming,[status(thm)],[c_394]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1468,plain,
% 2.46/0.98      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
% 2.46/0.98      | ~ v1_zfmisc_1(X1_50)
% 2.46/0.98      | v1_xboole_0(X0_50)
% 2.46/0.98      | X1_50 = X0_50 ),
% 2.46/0.98      inference(subtyping,[status(esa)],[c_395]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1881,plain,
% 2.46/0.98      ( X0_50 = X1_50
% 2.46/0.98      | m1_subset_1(X1_50,k1_zfmisc_1(X0_50)) != iProver_top
% 2.46/0.98      | v1_zfmisc_1(X0_50) != iProver_top
% 2.46/0.98      | v1_xboole_0(X1_50) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_1468]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_3182,plain,
% 2.46/0.98      ( k1_tarski(sK0(sK3)) = sK3
% 2.46/0.98      | v1_zfmisc_1(sK3) != iProver_top
% 2.46/0.98      | v1_xboole_0(k1_tarski(sK0(sK3))) = iProver_top ),
% 2.46/0.98      inference(superposition,[status(thm)],[c_3175,c_1881]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_34,plain,
% 2.46/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_21,negated_conjecture,
% 2.46/0.98      ( ~ v2_tex_2(sK3,sK2) | ~ v1_zfmisc_1(sK3) ),
% 2.46/0.98      inference(cnf_transformation,[],[f85]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_36,plain,
% 2.46/0.98      ( v2_tex_2(sK3,sK2) != iProver_top
% 2.46/0.98      | v1_zfmisc_1(sK3) != iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1479,plain,( X0_51 = X0_51 ),theory(equality) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1499,plain,
% 2.46/0.98      ( sK2 = sK2 ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_1479]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_6,plain,
% 2.46/0.98      ( m1_subset_1(X0,X1)
% 2.46/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.46/0.98      | ~ r2_hidden(X0,X2) ),
% 2.46/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_430,plain,
% 2.46/0.98      ( m1_subset_1(X0,X1)
% 2.46/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.46/0.98      | v1_xboole_0(X3)
% 2.46/0.98      | X2 != X3
% 2.46/0.98      | sK0(X3) != X0 ),
% 2.46/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_6]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_431,plain,
% 2.46/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.46/0.98      | m1_subset_1(sK0(X0),X1)
% 2.46/0.98      | v1_xboole_0(X0) ),
% 2.46/0.98      inference(unflattening,[status(thm)],[c_430]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1466,plain,
% 2.46/0.98      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
% 2.46/0.98      | m1_subset_1(sK0(X0_50),X1_50)
% 2.46/0.98      | v1_xboole_0(X0_50) ),
% 2.46/0.98      inference(subtyping,[status(esa)],[c_431]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1999,plain,
% 2.46/0.98      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.46/0.98      | m1_subset_1(sK0(X0_50),u1_struct_0(sK2))
% 2.46/0.98      | v1_xboole_0(X0_50) ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_1466]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2002,plain,
% 2.46/0.98      ( m1_subset_1(sK0(sK3),u1_struct_0(sK2))
% 2.46/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.46/0.98      | v1_xboole_0(sK3) ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_1999]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2001,plain,
% 2.46/0.98      ( m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.46/0.98      | m1_subset_1(sK0(X0_50),u1_struct_0(sK2)) = iProver_top
% 2.46/0.98      | v1_xboole_0(X0_50) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_1999]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2003,plain,
% 2.46/0.98      ( m1_subset_1(sK0(sK3),u1_struct_0(sK2)) = iProver_top
% 2.46/0.98      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.46/0.98      | v1_xboole_0(sK3) = iProver_top ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_2001]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_20,plain,
% 2.46/0.98      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 2.46/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.46/0.98      | v2_struct_0(X0)
% 2.46/0.98      | ~ v2_pre_topc(X0)
% 2.46/0.98      | ~ l1_pre_topc(X0) ),
% 2.46/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_853,plain,
% 2.46/0.98      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 2.46/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.46/0.98      | v2_struct_0(X0)
% 2.46/0.98      | ~ l1_pre_topc(X0)
% 2.46/0.98      | sK2 != X0 ),
% 2.46/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_854,plain,
% 2.46/0.98      ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
% 2.46/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.46/0.98      | v2_struct_0(sK2)
% 2.46/0.98      | ~ l1_pre_topc(sK2) ),
% 2.46/0.98      inference(unflattening,[status(thm)],[c_853]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_858,plain,
% 2.46/0.98      ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
% 2.46/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 2.46/0.98      inference(global_propositional_subsumption,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_854,c_28,c_25]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1465,plain,
% 2.46/0.98      ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0_50),sK2)
% 2.46/0.98      | ~ m1_subset_1(X0_50,u1_struct_0(sK2)) ),
% 2.46/0.98      inference(subtyping,[status(esa)],[c_858]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2000,plain,
% 2.46/0.98      ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),sK0(X0_50)),sK2)
% 2.46/0.98      | ~ m1_subset_1(sK0(X0_50),u1_struct_0(sK2)) ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_1465]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2005,plain,
% 2.46/0.98      ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),sK0(X0_50)),sK2) = iProver_top
% 2.46/0.98      | m1_subset_1(sK0(X0_50),u1_struct_0(sK2)) != iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_2000]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2007,plain,
% 2.46/0.98      ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),sK0(sK3)),sK2) = iProver_top
% 2.46/0.98      | m1_subset_1(sK0(sK3),u1_struct_0(sK2)) != iProver_top ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_2005]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1475,plain,
% 2.46/0.98      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
% 2.46/0.98      | ~ v1_xboole_0(X1_50)
% 2.46/0.98      | v1_xboole_0(X0_50) ),
% 2.46/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2076,plain,
% 2.46/0.98      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.46/0.98      | v1_xboole_0(X0_50)
% 2.46/0.98      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_1475]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2078,plain,
% 2.46/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.46/0.98      | ~ v1_xboole_0(u1_struct_0(sK2))
% 2.46/0.98      | v1_xboole_0(sK3) ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_2076]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1488,plain,
% 2.46/0.98      ( ~ v2_tex_2(X0_50,X0_51)
% 2.46/0.98      | v2_tex_2(X1_50,X1_51)
% 2.46/0.98      | X1_51 != X0_51
% 2.46/0.98      | X1_50 != X0_50 ),
% 2.46/0.98      theory(equality) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2108,plain,
% 2.46/0.98      ( v2_tex_2(X0_50,X0_51)
% 2.46/0.98      | ~ v2_tex_2(k6_domain_1(u1_struct_0(sK2),sK0(X1_50)),sK2)
% 2.46/0.98      | X0_51 != sK2
% 2.46/0.98      | X0_50 != k6_domain_1(u1_struct_0(sK2),sK0(X1_50)) ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_1488]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2109,plain,
% 2.46/0.98      ( X0_51 != sK2
% 2.46/0.98      | X0_50 != k6_domain_1(u1_struct_0(sK2),sK0(X1_50))
% 2.46/0.98      | v2_tex_2(X0_50,X0_51) = iProver_top
% 2.46/0.98      | v2_tex_2(k6_domain_1(u1_struct_0(sK2),sK0(X1_50)),sK2) != iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_2108]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2111,plain,
% 2.46/0.98      ( sK2 != sK2
% 2.46/0.98      | sK3 != k6_domain_1(u1_struct_0(sK2),sK0(sK3))
% 2.46/0.98      | v2_tex_2(k6_domain_1(u1_struct_0(sK2),sK0(sK3)),sK2) != iProver_top
% 2.46/0.98      | v2_tex_2(sK3,sK2) = iProver_top ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_2109]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1480,plain,
% 2.46/0.98      ( X0_50 != X1_50 | X2_50 != X1_50 | X2_50 = X0_50 ),
% 2.46/0.98      theory(equality) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2278,plain,
% 2.46/0.98      ( X0_50 != X1_50
% 2.46/0.98      | X0_50 = k6_domain_1(u1_struct_0(sK2),sK0(X2_50))
% 2.46/0.98      | k6_domain_1(u1_struct_0(sK2),sK0(X2_50)) != X1_50 ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_1480]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2785,plain,
% 2.46/0.98      ( X0_50 = k6_domain_1(u1_struct_0(sK2),sK0(X1_50))
% 2.46/0.98      | X0_50 != k1_tarski(sK0(X1_50))
% 2.46/0.98      | k6_domain_1(u1_struct_0(sK2),sK0(X1_50)) != k1_tarski(sK0(X1_50)) ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_2278]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2787,plain,
% 2.46/0.98      ( k6_domain_1(u1_struct_0(sK2),sK0(sK3)) != k1_tarski(sK0(sK3))
% 2.46/0.98      | sK3 = k6_domain_1(u1_struct_0(sK2),sK0(sK3))
% 2.46/0.98      | sK3 != k1_tarski(sK0(sK3)) ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_2785]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2012,plain,
% 2.46/0.98      ( ~ m1_subset_1(sK0(X0_50),X1_50)
% 2.46/0.98      | v1_xboole_0(X1_50)
% 2.46/0.98      | k6_domain_1(X1_50,sK0(X0_50)) = k1_tarski(sK0(X0_50)) ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_1473]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2786,plain,
% 2.46/0.98      ( ~ m1_subset_1(sK0(X0_50),u1_struct_0(sK2))
% 2.46/0.98      | v1_xboole_0(u1_struct_0(sK2))
% 2.46/0.98      | k6_domain_1(u1_struct_0(sK2),sK0(X0_50)) = k1_tarski(sK0(X0_50)) ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_2012]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2789,plain,
% 2.46/0.98      ( ~ m1_subset_1(sK0(sK3),u1_struct_0(sK2))
% 2.46/0.98      | v1_xboole_0(u1_struct_0(sK2))
% 2.46/0.98      | k6_domain_1(u1_struct_0(sK2),sK0(sK3)) = k1_tarski(sK0(sK3)) ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_2786]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_3235,plain,
% 2.46/0.98      ( ~ m1_subset_1(k1_tarski(sK0(X0_50)),k1_zfmisc_1(X1_50))
% 2.46/0.98      | ~ v1_zfmisc_1(X1_50)
% 2.46/0.98      | v1_xboole_0(k1_tarski(sK0(X0_50)))
% 2.46/0.98      | X1_50 = k1_tarski(sK0(X0_50)) ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_1468]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_3236,plain,
% 2.46/0.98      ( X0_50 = k1_tarski(sK0(X1_50))
% 2.46/0.98      | m1_subset_1(k1_tarski(sK0(X1_50)),k1_zfmisc_1(X0_50)) != iProver_top
% 2.46/0.98      | v1_zfmisc_1(X0_50) != iProver_top
% 2.46/0.98      | v1_xboole_0(k1_tarski(sK0(X1_50))) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_3235]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_3238,plain,
% 2.46/0.98      ( sK3 = k1_tarski(sK0(sK3))
% 2.46/0.98      | m1_subset_1(k1_tarski(sK0(sK3)),k1_zfmisc_1(sK3)) != iProver_top
% 2.46/0.98      | v1_zfmisc_1(sK3) != iProver_top
% 2.46/0.98      | v1_xboole_0(k1_tarski(sK0(sK3))) = iProver_top ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_3236]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_3278,plain,
% 2.46/0.98      ( v1_zfmisc_1(sK3) != iProver_top
% 2.46/0.98      | v1_xboole_0(k1_tarski(sK0(sK3))) = iProver_top ),
% 2.46/0.98      inference(global_propositional_subsumption,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_3182,c_24,c_33,c_23,c_34,c_36,c_1499,c_1517,c_2002,
% 2.46/0.98                 c_2003,c_2007,c_2078,c_2111,c_2787,c_2789,c_3003,c_3238]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2,plain,
% 2.46/0.98      ( ~ v1_xboole_0(k1_tarski(X0)) ),
% 2.46/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1476,plain,
% 2.46/0.98      ( ~ v1_xboole_0(k1_tarski(X0_50)) ),
% 2.46/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1873,plain,
% 2.46/0.98      ( v1_xboole_0(k1_tarski(X0_50)) != iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_1476]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_3284,plain,
% 2.46/0.98      ( v1_zfmisc_1(sK3) != iProver_top ),
% 2.46/0.98      inference(forward_subsumption_resolution,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_3278,c_1873]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_3286,plain,
% 2.46/0.98      ( u1_struct_0(sK1(sK2,sK3)) = sK3 ),
% 2.46/0.98      inference(superposition,[status(thm)],[c_2204,c_3284]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_18,plain,
% 2.46/0.98      ( ~ v2_tex_2(X0,X1)
% 2.46/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | v1_tdlat_3(sK1(X1,X0))
% 2.46/0.98      | ~ v2_pre_topc(X1)
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | v1_xboole_0(X0) ),
% 2.46/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_919,plain,
% 2.46/0.98      ( ~ v2_tex_2(X0,X1)
% 2.46/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | v1_tdlat_3(sK1(X1,X0))
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | v1_xboole_0(X0)
% 2.46/0.98      | sK2 != X1 ),
% 2.46/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_920,plain,
% 2.46/0.98      ( ~ v2_tex_2(X0,sK2)
% 2.46/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.46/0.98      | v2_struct_0(sK2)
% 2.46/0.98      | v1_tdlat_3(sK1(sK2,X0))
% 2.46/0.98      | ~ l1_pre_topc(sK2)
% 2.46/0.98      | v1_xboole_0(X0) ),
% 2.46/0.98      inference(unflattening,[status(thm)],[c_919]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_924,plain,
% 2.46/0.98      ( v1_tdlat_3(sK1(sK2,X0))
% 2.46/0.98      | ~ v2_tex_2(X0,sK2)
% 2.46/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.46/0.98      | v1_xboole_0(X0) ),
% 2.46/0.98      inference(global_propositional_subsumption,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_920,c_28,c_25]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_925,plain,
% 2.46/0.98      ( ~ v2_tex_2(X0,sK2)
% 2.46/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.46/0.98      | v1_tdlat_3(sK1(sK2,X0))
% 2.46/0.98      | v1_xboole_0(X0) ),
% 2.46/0.98      inference(renaming,[status(thm)],[c_924]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_19,plain,
% 2.46/0.98      ( ~ v2_tex_2(X0,X1)
% 2.46/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | ~ v2_struct_0(sK1(X1,X0))
% 2.46/0.98      | ~ v2_pre_topc(X1)
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | v1_xboole_0(X0) ),
% 2.46/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_895,plain,
% 2.46/0.98      ( ~ v2_tex_2(X0,X1)
% 2.46/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | ~ v2_struct_0(sK1(X1,X0))
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | v1_xboole_0(X0)
% 2.46/0.98      | sK2 != X1 ),
% 2.46/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_27]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_896,plain,
% 2.46/0.98      ( ~ v2_tex_2(X0,sK2)
% 2.46/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.46/0.98      | ~ v2_struct_0(sK1(sK2,X0))
% 2.46/0.98      | v2_struct_0(sK2)
% 2.46/0.98      | ~ l1_pre_topc(sK2)
% 2.46/0.98      | v1_xboole_0(X0) ),
% 2.46/0.98      inference(unflattening,[status(thm)],[c_895]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_900,plain,
% 2.46/0.98      ( ~ v2_tex_2(X0,sK2)
% 2.46/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.46/0.98      | ~ v2_struct_0(sK1(sK2,X0))
% 2.46/0.98      | v1_xboole_0(X0) ),
% 2.46/0.98      inference(global_propositional_subsumption,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_896,c_28,c_25]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_17,plain,
% 2.46/0.98      ( ~ v2_tex_2(X0,X1)
% 2.46/0.98      | m1_pre_topc(sK1(X1,X0),X1)
% 2.46/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | ~ v2_pre_topc(X1)
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | v1_xboole_0(X0) ),
% 2.46/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_13,plain,
% 2.46/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | v2_struct_0(X0)
% 2.46/0.98      | ~ v1_tdlat_3(X0)
% 2.46/0.98      | ~ v2_tdlat_3(X1)
% 2.46/0.98      | ~ v2_pre_topc(X1)
% 2.46/0.98      | v7_struct_0(X0)
% 2.46/0.98      | ~ l1_pre_topc(X1) ),
% 2.46/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_7,plain,
% 2.46/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.46/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_9,plain,
% 2.46/0.98      ( ~ v7_struct_0(X0)
% 2.46/0.98      | v1_zfmisc_1(u1_struct_0(X0))
% 2.46/0.98      | ~ l1_struct_0(X0) ),
% 2.46/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_372,plain,
% 2.46/0.98      ( ~ v7_struct_0(X0)
% 2.46/0.98      | v1_zfmisc_1(u1_struct_0(X0))
% 2.46/0.98      | ~ l1_pre_topc(X0) ),
% 2.46/0.98      inference(resolution,[status(thm)],[c_7,c_9]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_452,plain,
% 2.46/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.46/0.98      | v2_struct_0(X0)
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | ~ v1_tdlat_3(X0)
% 2.46/0.98      | ~ v2_tdlat_3(X1)
% 2.46/0.98      | ~ v2_pre_topc(X1)
% 2.46/0.98      | v1_zfmisc_1(u1_struct_0(X0))
% 2.46/0.98      | ~ l1_pre_topc(X0)
% 2.46/0.98      | ~ l1_pre_topc(X1) ),
% 2.46/0.98      inference(resolution,[status(thm)],[c_13,c_372]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_8,plain,
% 2.46/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.46/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_456,plain,
% 2.46/0.98      ( v1_zfmisc_1(u1_struct_0(X0))
% 2.46/0.98      | ~ v2_pre_topc(X1)
% 2.46/0.98      | ~ v2_tdlat_3(X1)
% 2.46/0.98      | ~ v1_tdlat_3(X0)
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | v2_struct_0(X0)
% 2.46/0.98      | ~ m1_pre_topc(X0,X1)
% 2.46/0.98      | ~ l1_pre_topc(X1) ),
% 2.46/0.98      inference(global_propositional_subsumption,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_452,c_8]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_457,plain,
% 2.46/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.46/0.98      | v2_struct_0(X0)
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | ~ v1_tdlat_3(X0)
% 2.46/0.98      | ~ v2_tdlat_3(X1)
% 2.46/0.98      | ~ v2_pre_topc(X1)
% 2.46/0.98      | v1_zfmisc_1(u1_struct_0(X0))
% 2.46/0.98      | ~ l1_pre_topc(X1) ),
% 2.46/0.98      inference(renaming,[status(thm)],[c_456]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_12,plain,
% 2.46/0.98      ( ~ v2_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 2.46/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_476,plain,
% 2.46/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.46/0.98      | v2_struct_0(X0)
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | ~ v1_tdlat_3(X0)
% 2.46/0.98      | ~ v2_tdlat_3(X1)
% 2.46/0.98      | v1_zfmisc_1(u1_struct_0(X0))
% 2.46/0.98      | ~ l1_pre_topc(X1) ),
% 2.46/0.98      inference(forward_subsumption_resolution,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_457,c_12]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_26,negated_conjecture,
% 2.46/0.98      ( v2_tdlat_3(sK2) ),
% 2.46/0.98      inference(cnf_transformation,[],[f80]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_497,plain,
% 2.46/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.46/0.98      | v2_struct_0(X0)
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | ~ v1_tdlat_3(X0)
% 2.46/0.98      | v1_zfmisc_1(u1_struct_0(X0))
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | sK2 != X1 ),
% 2.46/0.98      inference(resolution_lifted,[status(thm)],[c_476,c_26]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_498,plain,
% 2.46/0.98      ( ~ m1_pre_topc(X0,sK2)
% 2.46/0.98      | v2_struct_0(X0)
% 2.46/0.98      | v2_struct_0(sK2)
% 2.46/0.98      | ~ v1_tdlat_3(X0)
% 2.46/0.98      | v1_zfmisc_1(u1_struct_0(X0))
% 2.46/0.98      | ~ l1_pre_topc(sK2) ),
% 2.46/0.98      inference(unflattening,[status(thm)],[c_497]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_502,plain,
% 2.46/0.98      ( v1_zfmisc_1(u1_struct_0(X0))
% 2.46/0.98      | ~ v1_tdlat_3(X0)
% 2.46/0.98      | ~ m1_pre_topc(X0,sK2)
% 2.46/0.98      | v2_struct_0(X0) ),
% 2.46/0.98      inference(global_propositional_subsumption,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_498,c_28,c_25]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_503,plain,
% 2.46/0.98      ( ~ m1_pre_topc(X0,sK2)
% 2.46/0.98      | v2_struct_0(X0)
% 2.46/0.98      | ~ v1_tdlat_3(X0)
% 2.46/0.98      | v1_zfmisc_1(u1_struct_0(X0)) ),
% 2.46/0.98      inference(renaming,[status(thm)],[c_502]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_675,plain,
% 2.46/0.98      ( ~ v2_tex_2(X0,X1)
% 2.46/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.46/0.98      | v2_struct_0(X2)
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | ~ v1_tdlat_3(X2)
% 2.46/0.98      | ~ v2_pre_topc(X1)
% 2.46/0.98      | v1_zfmisc_1(u1_struct_0(X2))
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | v1_xboole_0(X0)
% 2.46/0.98      | sK1(X1,X0) != X2
% 2.46/0.98      | sK2 != X1 ),
% 2.46/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_503]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_676,plain,
% 2.46/0.98      ( ~ v2_tex_2(X0,sK2)
% 2.46/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.46/0.98      | v2_struct_0(sK1(sK2,X0))
% 2.46/0.98      | v2_struct_0(sK2)
% 2.46/0.98      | ~ v1_tdlat_3(sK1(sK2,X0))
% 2.46/0.98      | ~ v2_pre_topc(sK2)
% 2.46/0.98      | v1_zfmisc_1(u1_struct_0(sK1(sK2,X0)))
% 2.46/0.98      | ~ l1_pre_topc(sK2)
% 2.46/0.98      | v1_xboole_0(X0) ),
% 2.46/0.98      inference(unflattening,[status(thm)],[c_675]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_680,plain,
% 2.46/0.98      ( v1_zfmisc_1(u1_struct_0(sK1(sK2,X0)))
% 2.46/0.98      | v2_struct_0(sK1(sK2,X0))
% 2.46/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.46/0.98      | ~ v2_tex_2(X0,sK2)
% 2.46/0.98      | ~ v1_tdlat_3(sK1(sK2,X0))
% 2.46/0.98      | v1_xboole_0(X0) ),
% 2.46/0.98      inference(global_propositional_subsumption,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_676,c_28,c_27,c_25]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_681,plain,
% 2.46/0.98      ( ~ v2_tex_2(X0,sK2)
% 2.46/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.46/0.98      | v2_struct_0(sK1(sK2,X0))
% 2.46/0.98      | ~ v1_tdlat_3(sK1(sK2,X0))
% 2.46/0.98      | v1_zfmisc_1(u1_struct_0(sK1(sK2,X0)))
% 2.46/0.98      | v1_xboole_0(X0) ),
% 2.46/0.98      inference(renaming,[status(thm)],[c_680]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_978,plain,
% 2.46/0.98      ( ~ v2_tex_2(X0,sK2)
% 2.46/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.46/0.98      | ~ v1_tdlat_3(sK1(sK2,X0))
% 2.46/0.98      | v1_zfmisc_1(u1_struct_0(sK1(sK2,X0)))
% 2.46/0.98      | v1_xboole_0(X0) ),
% 2.46/0.98      inference(backward_subsumption_resolution,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_900,c_681]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_987,plain,
% 2.46/0.98      ( ~ v2_tex_2(X0,sK2)
% 2.46/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.46/0.98      | v1_zfmisc_1(u1_struct_0(sK1(sK2,X0)))
% 2.46/0.98      | v1_xboole_0(X0) ),
% 2.46/0.98      inference(backward_subsumption_resolution,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_925,c_978]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1463,plain,
% 2.46/0.98      ( ~ v2_tex_2(X0_50,sK2)
% 2.46/0.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.46/0.98      | v1_zfmisc_1(u1_struct_0(sK1(sK2,X0_50)))
% 2.46/0.98      | v1_xboole_0(X0_50) ),
% 2.46/0.98      inference(subtyping,[status(esa)],[c_987]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1886,plain,
% 2.46/0.98      ( v2_tex_2(X0_50,sK2) != iProver_top
% 2.46/0.98      | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.46/0.98      | v1_zfmisc_1(u1_struct_0(sK1(sK2,X0_50))) = iProver_top
% 2.46/0.98      | v1_xboole_0(X0_50) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_1463]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2527,plain,
% 2.46/0.98      ( v2_tex_2(sK3,sK2) != iProver_top
% 2.46/0.98      | v1_zfmisc_1(u1_struct_0(sK1(sK2,sK3))) = iProver_top
% 2.46/0.98      | v1_xboole_0(sK3) = iProver_top ),
% 2.46/0.98      inference(superposition,[status(thm)],[c_1879,c_1886]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2550,plain,
% 2.46/0.98      ( v1_zfmisc_1(u1_struct_0(sK1(sK2,sK3))) = iProver_top
% 2.46/0.98      | v2_tex_2(sK3,sK2) != iProver_top ),
% 2.46/0.98      inference(global_propositional_subsumption,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_2527,c_33]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2551,plain,
% 2.46/0.98      ( v2_tex_2(sK3,sK2) != iProver_top
% 2.46/0.98      | v1_zfmisc_1(u1_struct_0(sK1(sK2,sK3))) = iProver_top ),
% 2.46/0.98      inference(renaming,[status(thm)],[c_2550]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_3384,plain,
% 2.46/0.98      ( v2_tex_2(sK3,sK2) != iProver_top
% 2.46/0.98      | v1_zfmisc_1(sK3) = iProver_top ),
% 2.46/0.98      inference(demodulation,[status(thm)],[c_3286,c_2551]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_35,plain,
% 2.46/0.98      ( v2_tex_2(sK3,sK2) = iProver_top
% 2.46/0.98      | v1_zfmisc_1(sK3) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(contradiction,plain,
% 2.46/0.98      ( $false ),
% 2.46/0.98      inference(minisat,[status(thm)],[c_3384,c_3284,c_35]) ).
% 2.46/0.98  
% 2.46/0.98  
% 2.46/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.46/0.98  
% 2.46/0.98  ------                               Statistics
% 2.46/0.98  
% 2.46/0.98  ------ General
% 2.46/0.98  
% 2.46/0.98  abstr_ref_over_cycles:                  0
% 2.46/0.98  abstr_ref_under_cycles:                 0
% 2.46/0.98  gc_basic_clause_elim:                   0
% 2.46/0.98  forced_gc_time:                         0
% 2.46/0.98  parsing_time:                           0.01
% 2.46/0.98  unif_index_cands_time:                  0.
% 2.46/0.98  unif_index_add_time:                    0.
% 2.46/0.98  orderings_time:                         0.
% 2.46/0.98  out_proof_time:                         0.013
% 2.46/0.98  total_time:                             0.13
% 2.46/0.98  num_of_symbols:                         55
% 2.46/0.98  num_of_terms:                           2571
% 2.46/0.98  
% 2.46/0.98  ------ Preprocessing
% 2.46/0.98  
% 2.46/0.98  num_of_splits:                          0
% 2.46/0.98  num_of_split_atoms:                     0
% 2.46/0.98  num_of_reused_defs:                     0
% 2.46/0.98  num_eq_ax_congr_red:                    19
% 2.46/0.98  num_of_sem_filtered_clauses:            1
% 2.46/0.98  num_of_subtypes:                        2
% 2.46/0.98  monotx_restored_types:                  0
% 2.46/0.98  sat_num_of_epr_types:                   0
% 2.46/0.98  sat_num_of_non_cyclic_types:            0
% 2.46/0.98  sat_guarded_non_collapsed_types:        1
% 2.46/0.98  num_pure_diseq_elim:                    0
% 2.46/0.98  simp_replaced_by:                       0
% 2.46/0.98  res_preprocessed:                       93
% 2.46/0.98  prep_upred:                             0
% 2.46/0.98  prep_unflattend:                        34
% 2.46/0.98  smt_new_axioms:                         0
% 2.46/0.98  pred_elim_cands:                        4
% 2.46/0.98  pred_elim:                              10
% 2.46/0.98  pred_elim_cl:                           14
% 2.46/0.98  pred_elim_cycles:                       18
% 2.46/0.98  merged_defs:                            8
% 2.46/0.98  merged_defs_ncl:                        0
% 2.46/0.98  bin_hyper_res:                          8
% 2.46/0.98  prep_cycles:                            4
% 2.46/0.98  pred_elim_time:                         0.02
% 2.46/0.98  splitting_time:                         0.
% 2.46/0.98  sem_filter_time:                        0.
% 2.46/0.98  monotx_time:                            0.
% 2.46/0.98  subtype_inf_time:                       0.
% 2.46/0.98  
% 2.46/0.98  ------ Problem properties
% 2.46/0.98  
% 2.46/0.98  clauses:                                14
% 2.46/0.98  conjectures:                            4
% 2.46/0.98  epr:                                    3
% 2.46/0.98  horn:                                   6
% 2.46/0.98  ground:                                 4
% 2.46/0.98  unary:                                  3
% 2.46/0.98  binary:                                 4
% 2.46/0.98  lits:                                   35
% 2.46/0.98  lits_eq:                                3
% 2.46/0.98  fd_pure:                                0
% 2.46/0.98  fd_pseudo:                              0
% 2.46/0.98  fd_cond:                                0
% 2.46/0.98  fd_pseudo_cond:                         1
% 2.46/0.98  ac_symbols:                             0
% 2.46/0.98  
% 2.46/0.98  ------ Propositional Solver
% 2.46/0.98  
% 2.46/0.98  prop_solver_calls:                      27
% 2.46/0.98  prop_fast_solver_calls:                 844
% 2.46/0.98  smt_solver_calls:                       0
% 2.46/0.98  smt_fast_solver_calls:                  0
% 2.46/0.98  prop_num_of_clauses:                    888
% 2.46/0.98  prop_preprocess_simplified:             3467
% 2.46/0.98  prop_fo_subsumed:                       38
% 2.46/0.98  prop_solver_time:                       0.
% 2.46/0.98  smt_solver_time:                        0.
% 2.46/0.98  smt_fast_solver_time:                   0.
% 2.46/0.98  prop_fast_solver_time:                  0.
% 2.46/0.98  prop_unsat_core_time:                   0.
% 2.46/0.98  
% 2.46/0.98  ------ QBF
% 2.46/0.98  
% 2.46/0.98  qbf_q_res:                              0
% 2.46/0.98  qbf_num_tautologies:                    0
% 2.46/0.98  qbf_prep_cycles:                        0
% 2.46/0.98  
% 2.46/0.98  ------ BMC1
% 2.46/0.98  
% 2.46/0.98  bmc1_current_bound:                     -1
% 2.46/0.98  bmc1_last_solved_bound:                 -1
% 2.46/0.98  bmc1_unsat_core_size:                   -1
% 2.46/0.98  bmc1_unsat_core_parents_size:           -1
% 2.46/0.98  bmc1_merge_next_fun:                    0
% 2.46/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.46/0.98  
% 2.46/0.98  ------ Instantiation
% 2.46/0.98  
% 2.46/0.98  inst_num_of_clauses:                    211
% 2.46/0.98  inst_num_in_passive:                    14
% 2.46/0.98  inst_num_in_active:                     146
% 2.46/0.98  inst_num_in_unprocessed:                51
% 2.46/0.98  inst_num_of_loops:                      160
% 2.46/0.98  inst_num_of_learning_restarts:          0
% 2.46/0.98  inst_num_moves_active_passive:          11
% 2.46/0.98  inst_lit_activity:                      0
% 2.46/0.98  inst_lit_activity_moves:                0
% 2.46/0.98  inst_num_tautologies:                   0
% 2.46/0.98  inst_num_prop_implied:                  0
% 2.46/0.98  inst_num_existing_simplified:           0
% 2.46/0.98  inst_num_eq_res_simplified:             0
% 2.46/0.98  inst_num_child_elim:                    0
% 2.46/0.98  inst_num_of_dismatching_blockings:      99
% 2.46/0.98  inst_num_of_non_proper_insts:           254
% 2.46/0.98  inst_num_of_duplicates:                 0
% 2.46/0.98  inst_inst_num_from_inst_to_res:         0
% 2.46/0.98  inst_dismatching_checking_time:         0.
% 2.46/0.98  
% 2.46/0.98  ------ Resolution
% 2.46/0.98  
% 2.46/0.98  res_num_of_clauses:                     0
% 2.46/0.98  res_num_in_passive:                     0
% 2.46/0.98  res_num_in_active:                      0
% 2.46/0.98  res_num_of_loops:                       97
% 2.46/0.98  res_forward_subset_subsumed:            45
% 2.46/0.98  res_backward_subset_subsumed:           0
% 2.46/0.98  res_forward_subsumed:                   0
% 2.46/0.98  res_backward_subsumed:                  0
% 2.46/0.98  res_forward_subsumption_resolution:     1
% 2.46/0.98  res_backward_subsumption_resolution:    2
% 2.46/0.98  res_clause_to_clause_subsumption:       88
% 2.46/0.98  res_orphan_elimination:                 0
% 2.46/0.98  res_tautology_del:                      68
% 2.46/0.98  res_num_eq_res_simplified:              0
% 2.46/0.98  res_num_sel_changes:                    0
% 2.46/0.98  res_moves_from_active_to_pass:          0
% 2.46/0.98  
% 2.46/0.98  ------ Superposition
% 2.46/0.98  
% 2.46/0.98  sup_time_total:                         0.
% 2.46/0.98  sup_time_generating:                    0.
% 2.46/0.98  sup_time_sim_full:                      0.
% 2.46/0.98  sup_time_sim_immed:                     0.
% 2.46/0.98  
% 2.46/0.98  sup_num_of_clauses:                     39
% 2.46/0.98  sup_num_in_active:                      27
% 2.46/0.98  sup_num_in_passive:                     12
% 2.46/0.98  sup_num_of_loops:                       30
% 2.46/0.98  sup_fw_superposition:                   10
% 2.46/0.98  sup_bw_superposition:                   20
% 2.46/0.98  sup_immediate_simplified:               3
% 2.46/0.98  sup_given_eliminated:                   0
% 2.46/0.98  comparisons_done:                       0
% 2.46/0.98  comparisons_avoided:                    0
% 2.46/0.98  
% 2.46/0.98  ------ Simplifications
% 2.46/0.98  
% 2.46/0.98  
% 2.46/0.98  sim_fw_subset_subsumed:                 1
% 2.46/0.98  sim_bw_subset_subsumed:                 3
% 2.46/0.98  sim_fw_subsumed:                        0
% 2.46/0.98  sim_bw_subsumed:                        0
% 2.46/0.98  sim_fw_subsumption_res:                 1
% 2.46/0.98  sim_bw_subsumption_res:                 0
% 2.46/0.98  sim_tautology_del:                      2
% 2.46/0.98  sim_eq_tautology_del:                   0
% 2.46/0.98  sim_eq_res_simp:                        0
% 2.46/0.98  sim_fw_demodulated:                     0
% 2.46/0.98  sim_bw_demodulated:                     1
% 2.46/0.98  sim_light_normalised:                   2
% 2.46/0.98  sim_joinable_taut:                      0
% 2.46/0.98  sim_joinable_simp:                      0
% 2.46/0.98  sim_ac_normalised:                      0
% 2.46/0.98  sim_smt_subsumption:                    0
% 2.46/0.98  
%------------------------------------------------------------------------------
