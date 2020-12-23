%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:48 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :  200 (1117 expanded)
%              Number of clauses        :  114 ( 360 expanded)
%              Number of leaves         :   25 ( 238 expanded)
%              Depth                    :   19
%              Number of atoms          :  769 (6904 expanded)
%              Number of equality atoms :  158 ( 467 expanded)
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

fof(f47,plain,(
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

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

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
    inference(nnf_transformation,[],[f48])).

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
     => ( ( ~ v1_zfmisc_1(sK3)
          | ~ v2_tex_2(sK3,X0) )
        & ( v1_zfmisc_1(sK3)
          | v2_tex_2(sK3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK3) ) ) ),
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

fof(f59,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f56,f58,f57])).

fof(f88,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
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

fof(f21,plain,(
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

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f53,plain,(
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

fof(f54,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f53])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK1(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f83,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f84,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f86,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f87,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f89,plain,
    ( v1_zfmisc_1(sK3)
    | v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f50,f51])).

fof(f61,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f77,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f72,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v2_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f81,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK1(X0,X1)) = X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f90,plain,
    ( ~ v1_zfmisc_1(sK3)
    | ~ v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f13,axiom,(
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

fof(f37,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f74,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f68,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( v2_struct_0(X0)
       => v7_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f67,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f70,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK1(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f69,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f85,plain,(
    v2_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2577,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_3276,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2577])).

cnf(c_19,plain,
    ( ~ v2_tex_2(X0,X1)
    | m1_pre_topc(sK1(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2583,plain,
    ( ~ v2_tex_2(X0_51,X0_50)
    | m1_pre_topc(sK1(X0_50,X0_51),X0_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_50)))
    | ~ v2_pre_topc(X0_50)
    | ~ l1_pre_topc(X0_50)
    | v2_struct_0(X0_50)
    | v1_xboole_0(X0_51) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_3270,plain,
    ( v2_tex_2(X0_51,X0_50) != iProver_top
    | m1_pre_topc(sK1(X0_50,X0_51),X0_50) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_50))) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2583])).

cnf(c_4217,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | m1_pre_topc(sK1(sK2,sK3),sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3276,c_3270])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_31,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_32,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_34,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_35,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_36,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v2_tex_2(sK3,sK2)
    | v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_229,plain,
    ( v1_zfmisc_1(sK3)
    | v2_tex_2(sK3,sK2) ),
    inference(prop_impl,[status(thm)],[c_24])).

cnf(c_230,plain,
    ( v2_tex_2(sK3,sK2)
    | v1_zfmisc_1(sK3) ),
    inference(renaming,[status(thm)],[c_229])).

cnf(c_898,plain,
    ( m1_pre_topc(sK1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v1_zfmisc_1(sK3)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v1_xboole_0(X1)
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_230])).

cnf(c_899,plain,
    ( m1_pre_topc(sK1(sK2,sK3),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | v1_zfmisc_1(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_898])).

cnf(c_901,plain,
    ( v1_zfmisc_1(sK3)
    | m1_pre_topc(sK1(sK2,sK3),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_899,c_30,c_29,c_27,c_26,c_25])).

cnf(c_902,plain,
    ( m1_pre_topc(sK1(sK2,sK3),sK2)
    | v1_zfmisc_1(sK3) ),
    inference(renaming,[status(thm)],[c_901])).

cnf(c_903,plain,
    ( m1_pre_topc(sK1(sK2,sK3),sK2) = iProver_top
    | v1_zfmisc_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_902])).

cnf(c_2591,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_2623,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_2591])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3,plain,
    ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_451,plain,
    ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X2)
    | X1 != X2
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_452,plain,
    ( m1_subset_1(k1_tarski(sK0(X0)),k1_zfmisc_1(X0))
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_2570,plain,
    ( m1_subset_1(k1_tarski(sK0(X0_51)),k1_zfmisc_1(X0_51))
    | v1_xboole_0(X0_51) ),
    inference(subtyping,[status(esa)],[c_452])).

cnf(c_2658,plain,
    ( m1_subset_1(k1_tarski(sK0(X0_51)),k1_zfmisc_1(X0_51)) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2570])).

cnf(c_2660,plain,
    ( m1_subset_1(k1_tarski(sK0(sK3)),k1_zfmisc_1(sK3)) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2658])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_465,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | v1_xboole_0(X3)
    | X2 != X3
    | sK0(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_6])).

cnf(c_466,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X0),X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_465])).

cnf(c_2569,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | m1_subset_1(sK0(X0_51),X1_51)
    | v1_xboole_0(X0_51) ),
    inference(subtyping,[status(esa)],[c_466])).

cnf(c_3508,plain,
    ( m1_subset_1(sK0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2569])).

cnf(c_3509,plain,
    ( m1_subset_1(sK0(sK3),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3508])).

cnf(c_22,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2580,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0_50),X0_51),X0_50)
    | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
    | ~ v2_pre_topc(X0_50)
    | ~ l1_pre_topc(X0_50)
    | v2_struct_0(X0_50) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_3546,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),sK0(sK3)),sK2)
    | ~ m1_subset_1(sK0(sK3),u1_struct_0(sK2))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2580])).

cnf(c_3547,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),sK0(sK3)),sK2) = iProver_top
    | m1_subset_1(sK0(sK3),u1_struct_0(sK2)) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3546])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2586,plain,
    ( ~ m1_subset_1(X0_51,X1_51)
    | v1_xboole_0(X1_51)
    | k6_domain_1(X1_51,X0_51) = k1_tarski(X0_51) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_3550,plain,
    ( ~ m1_subset_1(sK0(sK3),u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK0(sK3)) = k1_tarski(sK0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2586])).

cnf(c_3551,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK0(sK3)) = k1_tarski(sK0(sK3))
    | m1_subset_1(sK0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3550])).

cnf(c_2607,plain,
    ( ~ v2_tex_2(X0_51,X0_50)
    | v2_tex_2(X1_51,X1_50)
    | X1_51 != X0_51
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_3636,plain,
    ( v2_tex_2(X0_51,X0_50)
    | ~ v2_tex_2(k6_domain_1(u1_struct_0(sK2),sK0(sK3)),sK2)
    | X0_51 != k6_domain_1(u1_struct_0(sK2),sK0(sK3))
    | X0_50 != sK2 ),
    inference(instantiation,[status(thm)],[c_2607])).

cnf(c_3637,plain,
    ( X0_51 != k6_domain_1(u1_struct_0(sK2),sK0(sK3))
    | X0_50 != sK2
    | v2_tex_2(X0_51,X0_50) = iProver_top
    | v2_tex_2(k6_domain_1(u1_struct_0(sK2),sK0(sK3)),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3636])).

cnf(c_3639,plain,
    ( sK3 != k6_domain_1(u1_struct_0(sK2),sK0(sK3))
    | sK2 != sK2
    | v2_tex_2(k6_domain_1(u1_struct_0(sK2),sK0(sK3)),sK2) != iProver_top
    | v2_tex_2(sK3,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3637])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2588,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | ~ v1_xboole_0(X1_51)
    | v1_xboole_0(X0_51) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_3265,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(X1_51)) != iProver_top
    | v1_xboole_0(X1_51) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2588])).

cnf(c_3725,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3276,c_3265])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2589,plain,
    ( ~ v1_xboole_0(k1_tarski(X0_51)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3854,plain,
    ( ~ v1_xboole_0(k1_tarski(sK0(X0_51))) ),
    inference(instantiation,[status(thm)],[c_2589])).

cnf(c_3855,plain,
    ( v1_xboole_0(k1_tarski(sK0(X0_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3854])).

cnf(c_3857,plain,
    ( v1_xboole_0(k1_tarski(sK0(sK3))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3855])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_391,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_5,c_17])).

cnf(c_395,plain,
    ( v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_391,c_4])).

cnf(c_396,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | X1 = X0 ),
    inference(renaming,[status(thm)],[c_395])).

cnf(c_2571,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | ~ v1_zfmisc_1(X1_51)
    | v1_xboole_0(X0_51)
    | X1_51 = X0_51 ),
    inference(subtyping,[status(esa)],[c_396])).

cnf(c_3903,plain,
    ( ~ m1_subset_1(k1_tarski(sK0(X0_51)),k1_zfmisc_1(X1_51))
    | ~ v1_zfmisc_1(X1_51)
    | v1_xboole_0(k1_tarski(sK0(X0_51)))
    | X1_51 = k1_tarski(sK0(X0_51)) ),
    inference(instantiation,[status(thm)],[c_2571])).

cnf(c_3904,plain,
    ( X0_51 = k1_tarski(sK0(X1_51))
    | m1_subset_1(k1_tarski(sK0(X1_51)),k1_zfmisc_1(X0_51)) != iProver_top
    | v1_zfmisc_1(X0_51) != iProver_top
    | v1_xboole_0(k1_tarski(sK0(X1_51))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3903])).

cnf(c_3906,plain,
    ( sK3 = k1_tarski(sK0(sK3))
    | m1_subset_1(k1_tarski(sK0(sK3)),k1_zfmisc_1(sK3)) != iProver_top
    | v1_zfmisc_1(sK3) != iProver_top
    | v1_xboole_0(k1_tarski(sK0(sK3))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3904])).

cnf(c_2593,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_3792,plain,
    ( X0_51 != X1_51
    | X0_51 = k6_domain_1(u1_struct_0(sK2),sK0(sK3))
    | k6_domain_1(u1_struct_0(sK2),sK0(sK3)) != X1_51 ),
    inference(instantiation,[status(thm)],[c_2593])).

cnf(c_4274,plain,
    ( X0_51 = k6_domain_1(u1_struct_0(sK2),sK0(sK3))
    | X0_51 != k1_tarski(sK0(sK3))
    | k6_domain_1(u1_struct_0(sK2),sK0(sK3)) != k1_tarski(sK0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3792])).

cnf(c_4275,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK0(sK3)) != k1_tarski(sK0(sK3))
    | sK3 = k6_domain_1(u1_struct_0(sK2),sK0(sK3))
    | sK3 != k1_tarski(sK0(sK3)) ),
    inference(instantiation,[status(thm)],[c_4274])).

cnf(c_4584,plain,
    ( m1_pre_topc(sK1(sK2,sK3),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4217,c_31,c_32,c_34,c_35,c_36,c_903,c_2623,c_2660,c_3509,c_3547,c_3551,c_3639,c_3725,c_3857,c_3906,c_4275])).

cnf(c_12,plain,
    ( ~ v2_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1114,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_tdlat_3(X2)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_1115,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_1114])).

cnf(c_2566,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | ~ v2_tdlat_3(X1_50)
    | v2_tdlat_3(X0_50)
    | ~ l1_pre_topc(X1_50)
    | v2_struct_0(X1_50) ),
    inference(subtyping,[status(esa)],[c_1115])).

cnf(c_3287,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | v2_tdlat_3(X1_50) != iProver_top
    | v2_tdlat_3(X0_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2566])).

cnf(c_5414,plain,
    ( v2_tdlat_3(sK1(sK2,sK3)) = iProver_top
    | v2_tdlat_3(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4584,c_3287])).

cnf(c_18,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2584,plain,
    ( ~ v2_tex_2(X0_51,X0_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_50)))
    | ~ v2_pre_topc(X0_50)
    | ~ l1_pre_topc(X0_50)
    | v2_struct_0(X0_50)
    | v1_xboole_0(X0_51)
    | u1_struct_0(sK1(X0_50,X0_51)) = X0_51 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_3269,plain,
    ( u1_struct_0(sK1(X0_50,X0_51)) = X0_51
    | v2_tex_2(X0_51,X0_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_50))) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2584])).

cnf(c_4105,plain,
    ( u1_struct_0(sK1(sK2,sK3)) = sK3
    | v2_tex_2(sK3,sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3276,c_3269])).

cnf(c_37,plain,
    ( v2_tex_2(sK3,sK2) = iProver_top
    | v1_zfmisc_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_38,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | v1_zfmisc_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4391,plain,
    ( u1_struct_0(sK1(sK2,sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4105,c_31,c_32,c_34,c_35,c_36,c_37,c_38,c_2623,c_2660,c_3509,c_3547,c_3551,c_3639,c_3725,c_3857,c_3906,c_4275])).

cnf(c_14,plain,
    ( ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v7_struct_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_8,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_7,plain,
    ( ~ l1_struct_0(X0)
    | ~ v2_struct_0(X0)
    | v7_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_172,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X0)
    | v7_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_12,c_8,c_7])).

cnf(c_173,plain,
    ( ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | v7_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_172])).

cnf(c_10,plain,
    ( v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | ~ v7_struct_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_417,plain,
    ( v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | ~ v7_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_8,c_10])).

cnf(c_499,plain,
    ( ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_173,c_417])).

cnf(c_2567,plain,
    ( ~ v1_tdlat_3(X0_50)
    | ~ v2_tdlat_3(X0_50)
    | v1_zfmisc_1(u1_struct_0(X0_50))
    | ~ l1_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_499])).

cnf(c_3286,plain,
    ( v1_tdlat_3(X0_50) != iProver_top
    | v2_tdlat_3(X0_50) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0_50)) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2567])).

cnf(c_4399,plain,
    ( v1_tdlat_3(sK1(sK2,sK3)) != iProver_top
    | v2_tdlat_3(sK1(sK2,sK3)) != iProver_top
    | v1_zfmisc_1(sK3) = iProver_top
    | l1_pre_topc(sK1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4391,c_3286])).

cnf(c_20,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tdlat_3(sK1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_884,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tdlat_3(sK1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(sK3)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | sK2 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_230])).

cnf(c_885,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_tdlat_3(sK1(sK2,sK3))
    | ~ v2_pre_topc(sK2)
    | v1_zfmisc_1(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_884])).

cnf(c_887,plain,
    ( v1_zfmisc_1(sK3)
    | v1_tdlat_3(sK1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_885,c_30,c_29,c_27,c_26,c_25])).

cnf(c_888,plain,
    ( v1_tdlat_3(sK1(sK2,sK3))
    | v1_zfmisc_1(sK3) ),
    inference(renaming,[status(thm)],[c_887])).

cnf(c_889,plain,
    ( v1_tdlat_3(sK1(sK2,sK3)) = iProver_top
    | v1_zfmisc_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_888])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2587,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | ~ l1_pre_topc(X1_50)
    | l1_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_3266,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2587])).

cnf(c_4589,plain,
    ( l1_pre_topc(sK1(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4584,c_3266])).

cnf(c_4758,plain,
    ( v2_tdlat_3(sK1(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4399,c_31,c_32,c_34,c_35,c_36,c_38,c_889,c_2623,c_2660,c_3509,c_3547,c_3551,c_3639,c_3725,c_3857,c_3906,c_4275,c_4589])).

cnf(c_28,negated_conjecture,
    ( v2_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_33,plain,
    ( v2_tdlat_3(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5414,c_4758,c_34,c_33,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:57 EST 2020
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
% 2.33/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.33/0.99  
% 2.33/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.33/0.99  
% 2.33/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.33/0.99  ------ Proving...
% 2.33/0.99  ------ Problem Properties 
% 2.33/0.99  
% 2.33/0.99  
% 2.33/0.99  clauses                                 24
% 2.33/0.99  conjectures                             8
% 2.33/0.99  EPR                                     10
% 2.33/0.99  Horn                                    13
% 2.33/0.99  unary                                   7
% 2.33/0.99  binary                                  3
% 2.33/0.99  lits                                    77
% 2.33/0.99  lits eq                                 3
% 2.33/0.99  fd_pure                                 0
% 2.33/0.99  fd_pseudo                               0
% 2.33/0.99  fd_cond                                 0
% 2.33/0.99  fd_pseudo_cond                          1
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
% 2.33/0.99  --inst_lit_sel_side                     none
% 2.33/0.99  --inst_solver_per_active                1400
% 2.33/0.99  --inst_solver_calls_frac                1.
% 2.33/0.99  --inst_passive_queue_type               priority_queues
% 2.33/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
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
% 2.33/1.00  fof(f18,conjecture,(
% 2.33/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f19,negated_conjecture,(
% 2.33/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 2.33/1.00    inference(negated_conjecture,[],[f18])).
% 2.33/1.00  
% 2.33/1.00  fof(f47,plain,(
% 2.33/1.00    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.33/1.00    inference(ennf_transformation,[],[f19])).
% 2.33/1.00  
% 2.33/1.00  fof(f48,plain,(
% 2.33/1.00    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.33/1.00    inference(flattening,[],[f47])).
% 2.33/1.00  
% 2.33/1.00  fof(f55,plain,(
% 2.33/1.00    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.33/1.00    inference(nnf_transformation,[],[f48])).
% 2.33/1.00  
% 2.33/1.00  fof(f56,plain,(
% 2.33/1.00    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.33/1.00    inference(flattening,[],[f55])).
% 2.33/1.00  
% 2.33/1.00  fof(f58,plain,(
% 2.33/1.00    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK3) | ~v2_tex_2(sK3,X0)) & (v1_zfmisc_1(sK3) | v2_tex_2(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK3))) )),
% 2.33/1.00    introduced(choice_axiom,[])).
% 2.33/1.00  
% 2.33/1.00  fof(f57,plain,(
% 2.33/1.00    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK2)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.33/1.00    introduced(choice_axiom,[])).
% 2.33/1.00  
% 2.33/1.00  fof(f59,plain,(
% 2.33/1.00    ((~v1_zfmisc_1(sK3) | ~v2_tex_2(sK3,sK2)) & (v1_zfmisc_1(sK3) | v2_tex_2(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.33/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f56,f58,f57])).
% 2.33/1.00  
% 2.33/1.00  fof(f88,plain,(
% 2.33/1.00    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 2.33/1.00    inference(cnf_transformation,[],[f59])).
% 2.33/1.00  
% 2.33/1.00  fof(f16,axiom,(
% 2.33/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f21,plain,(
% 2.33/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 2.33/1.00    inference(pure_predicate_removal,[],[f16])).
% 2.33/1.00  
% 2.33/1.00  fof(f43,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.33/1.00    inference(ennf_transformation,[],[f21])).
% 2.33/1.00  
% 2.33/1.00  fof(f44,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/1.00    inference(flattening,[],[f43])).
% 2.33/1.00  
% 2.33/1.00  fof(f53,plain,(
% 2.33/1.00    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & v1_tdlat_3(sK1(X0,X1)) & ~v2_struct_0(sK1(X0,X1))))),
% 2.33/1.00    introduced(choice_axiom,[])).
% 2.33/1.00  
% 2.33/1.00  fof(f54,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : ((u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & v1_tdlat_3(sK1(X0,X1)) & ~v2_struct_0(sK1(X0,X1))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f53])).
% 2.33/1.00  
% 2.33/1.00  fof(f80,plain,(
% 2.33/1.00    ( ! [X0,X1] : (m1_pre_topc(sK1(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f54])).
% 2.33/1.00  
% 2.33/1.00  fof(f83,plain,(
% 2.33/1.00    ~v2_struct_0(sK2)),
% 2.33/1.00    inference(cnf_transformation,[],[f59])).
% 2.33/1.00  
% 2.33/1.00  fof(f84,plain,(
% 2.33/1.00    v2_pre_topc(sK2)),
% 2.33/1.00    inference(cnf_transformation,[],[f59])).
% 2.33/1.00  
% 2.33/1.00  fof(f86,plain,(
% 2.33/1.00    l1_pre_topc(sK2)),
% 2.33/1.00    inference(cnf_transformation,[],[f59])).
% 2.33/1.00  
% 2.33/1.00  fof(f87,plain,(
% 2.33/1.00    ~v1_xboole_0(sK3)),
% 2.33/1.00    inference(cnf_transformation,[],[f59])).
% 2.33/1.00  
% 2.33/1.00  fof(f89,plain,(
% 2.33/1.00    v1_zfmisc_1(sK3) | v2_tex_2(sK3,sK2)),
% 2.33/1.00    inference(cnf_transformation,[],[f59])).
% 2.33/1.00  
% 2.33/1.00  fof(f1,axiom,(
% 2.33/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f49,plain,(
% 2.33/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.33/1.00    inference(nnf_transformation,[],[f1])).
% 2.33/1.00  
% 2.33/1.00  fof(f50,plain,(
% 2.33/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.33/1.00    inference(rectify,[],[f49])).
% 2.33/1.00  
% 2.33/1.00  fof(f51,plain,(
% 2.33/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.33/1.00    introduced(choice_axiom,[])).
% 2.33/1.00  
% 2.33/1.00  fof(f52,plain,(
% 2.33/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.33/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f50,f51])).
% 2.33/1.00  
% 2.33/1.00  fof(f61,plain,(
% 2.33/1.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f52])).
% 2.33/1.00  
% 2.33/1.00  fof(f3,axiom,(
% 2.33/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f22,plain,(
% 2.33/1.00    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 2.33/1.00    inference(ennf_transformation,[],[f3])).
% 2.33/1.00  
% 2.33/1.00  fof(f63,plain,(
% 2.33/1.00    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f22])).
% 2.33/1.00  
% 2.33/1.00  fof(f6,axiom,(
% 2.33/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f25,plain,(
% 2.33/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.33/1.00    inference(ennf_transformation,[],[f6])).
% 2.33/1.00  
% 2.33/1.00  fof(f26,plain,(
% 2.33/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.33/1.00    inference(flattening,[],[f25])).
% 2.33/1.00  
% 2.33/1.00  fof(f66,plain,(
% 2.33/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f26])).
% 2.33/1.00  
% 2.33/1.00  fof(f17,axiom,(
% 2.33/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f45,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.33/1.00    inference(ennf_transformation,[],[f17])).
% 2.33/1.00  
% 2.33/1.00  fof(f46,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/1.00    inference(flattening,[],[f45])).
% 2.33/1.00  
% 2.33/1.00  fof(f82,plain,(
% 2.33/1.00    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f46])).
% 2.33/1.00  
% 2.33/1.00  fof(f11,axiom,(
% 2.33/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f33,plain,(
% 2.33/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.33/1.00    inference(ennf_transformation,[],[f11])).
% 2.33/1.00  
% 2.33/1.00  fof(f34,plain,(
% 2.33/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.33/1.00    inference(flattening,[],[f33])).
% 2.33/1.00  
% 2.33/1.00  fof(f71,plain,(
% 2.33/1.00    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f34])).
% 2.33/1.00  
% 2.33/1.00  fof(f4,axiom,(
% 2.33/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f23,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.33/1.00    inference(ennf_transformation,[],[f4])).
% 2.33/1.00  
% 2.33/1.00  fof(f64,plain,(
% 2.33/1.00    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f23])).
% 2.33/1.00  
% 2.33/1.00  fof(f2,axiom,(
% 2.33/1.00    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f62,plain,(
% 2.33/1.00    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 2.33/1.00    inference(cnf_transformation,[],[f2])).
% 2.33/1.00  
% 2.33/1.00  fof(f5,axiom,(
% 2.33/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f20,plain,(
% 2.33/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.33/1.00    inference(unused_predicate_definition_removal,[],[f5])).
% 2.33/1.00  
% 2.33/1.00  fof(f24,plain,(
% 2.33/1.00    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.33/1.00    inference(ennf_transformation,[],[f20])).
% 2.33/1.00  
% 2.33/1.00  fof(f65,plain,(
% 2.33/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.33/1.00    inference(cnf_transformation,[],[f24])).
% 2.33/1.00  
% 2.33/1.00  fof(f15,axiom,(
% 2.33/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f41,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 2.33/1.00    inference(ennf_transformation,[],[f15])).
% 2.33/1.00  
% 2.33/1.00  fof(f42,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.33/1.00    inference(flattening,[],[f41])).
% 2.33/1.00  
% 2.33/1.00  fof(f77,plain,(
% 2.33/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f42])).
% 2.33/1.00  
% 2.33/1.00  fof(f12,axiom,(
% 2.33/1.00    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f35,plain,(
% 2.33/1.00    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 2.33/1.00    inference(ennf_transformation,[],[f12])).
% 2.33/1.00  
% 2.33/1.00  fof(f36,plain,(
% 2.33/1.00    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 2.33/1.00    inference(flattening,[],[f35])).
% 2.33/1.00  
% 2.33/1.00  fof(f72,plain,(
% 2.33/1.00    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f36])).
% 2.33/1.00  
% 2.33/1.00  fof(f14,axiom,(
% 2.33/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f39,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.33/1.00    inference(ennf_transformation,[],[f14])).
% 2.33/1.00  
% 2.33/1.00  fof(f40,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/1.00    inference(flattening,[],[f39])).
% 2.33/1.00  
% 2.33/1.00  fof(f76,plain,(
% 2.33/1.00    ( ! [X0,X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f40])).
% 2.33/1.00  
% 2.33/1.00  fof(f81,plain,(
% 2.33/1.00    ( ! [X0,X1] : (u1_struct_0(sK1(X0,X1)) = X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f54])).
% 2.33/1.00  
% 2.33/1.00  fof(f90,plain,(
% 2.33/1.00    ~v1_zfmisc_1(sK3) | ~v2_tex_2(sK3,sK2)),
% 2.33/1.00    inference(cnf_transformation,[],[f59])).
% 2.33/1.00  
% 2.33/1.00  fof(f13,axiom,(
% 2.33/1.00    ! [X0] : (l1_pre_topc(X0) => ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0))))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f37,plain,(
% 2.33/1.00    ! [X0] : (((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | (~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.33/1.00    inference(ennf_transformation,[],[f13])).
% 2.33/1.00  
% 2.33/1.00  fof(f38,plain,(
% 2.33/1.00    ! [X0] : ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.33/1.00    inference(flattening,[],[f37])).
% 2.33/1.00  
% 2.33/1.00  fof(f74,plain,(
% 2.33/1.00    ( ! [X0] : (v7_struct_0(X0) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f38])).
% 2.33/1.00  
% 2.33/1.00  fof(f8,axiom,(
% 2.33/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f29,plain,(
% 2.33/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.33/1.00    inference(ennf_transformation,[],[f8])).
% 2.33/1.00  
% 2.33/1.00  fof(f68,plain,(
% 2.33/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f29])).
% 2.33/1.00  
% 2.33/1.00  fof(f7,axiom,(
% 2.33/1.00    ! [X0] : (l1_struct_0(X0) => (v2_struct_0(X0) => v7_struct_0(X0)))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f27,plain,(
% 2.33/1.00    ! [X0] : ((v7_struct_0(X0) | ~v2_struct_0(X0)) | ~l1_struct_0(X0))),
% 2.33/1.00    inference(ennf_transformation,[],[f7])).
% 2.33/1.00  
% 2.33/1.00  fof(f28,plain,(
% 2.33/1.00    ! [X0] : (v7_struct_0(X0) | ~v2_struct_0(X0) | ~l1_struct_0(X0))),
% 2.33/1.00    inference(flattening,[],[f27])).
% 2.33/1.00  
% 2.33/1.00  fof(f67,plain,(
% 2.33/1.00    ( ! [X0] : (v7_struct_0(X0) | ~v2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f28])).
% 2.33/1.00  
% 2.33/1.00  fof(f10,axiom,(
% 2.33/1.00    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f31,plain,(
% 2.33/1.00    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 2.33/1.00    inference(ennf_transformation,[],[f10])).
% 2.33/1.00  
% 2.33/1.00  fof(f32,plain,(
% 2.33/1.00    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 2.33/1.00    inference(flattening,[],[f31])).
% 2.33/1.00  
% 2.33/1.00  fof(f70,plain,(
% 2.33/1.00    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f32])).
% 2.33/1.00  
% 2.33/1.00  fof(f79,plain,(
% 2.33/1.00    ( ! [X0,X1] : (v1_tdlat_3(sK1(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f54])).
% 2.33/1.00  
% 2.33/1.00  fof(f9,axiom,(
% 2.33/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f30,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.33/1.00    inference(ennf_transformation,[],[f9])).
% 2.33/1.00  
% 2.33/1.00  fof(f69,plain,(
% 2.33/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f30])).
% 2.33/1.00  
% 2.33/1.00  fof(f85,plain,(
% 2.33/1.00    v2_tdlat_3(sK2)),
% 2.33/1.00    inference(cnf_transformation,[],[f59])).
% 2.33/1.00  
% 2.33/1.00  cnf(c_25,negated_conjecture,
% 2.33/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.33/1.00      inference(cnf_transformation,[],[f88]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2577,negated_conjecture,
% 2.33/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.33/1.00      inference(subtyping,[status(esa)],[c_25]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3276,plain,
% 2.33/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_2577]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_19,plain,
% 2.33/1.00      ( ~ v2_tex_2(X0,X1)
% 2.33/1.00      | m1_pre_topc(sK1(X1,X0),X1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | ~ v2_pre_topc(X1)
% 2.33/1.00      | ~ l1_pre_topc(X1)
% 2.33/1.00      | v2_struct_0(X1)
% 2.33/1.00      | v1_xboole_0(X0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2583,plain,
% 2.33/1.00      ( ~ v2_tex_2(X0_51,X0_50)
% 2.33/1.00      | m1_pre_topc(sK1(X0_50,X0_51),X0_50)
% 2.33/1.00      | ~ m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_50)))
% 2.33/1.00      | ~ v2_pre_topc(X0_50)
% 2.33/1.00      | ~ l1_pre_topc(X0_50)
% 2.33/1.00      | v2_struct_0(X0_50)
% 2.33/1.00      | v1_xboole_0(X0_51) ),
% 2.33/1.00      inference(subtyping,[status(esa)],[c_19]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3270,plain,
% 2.33/1.00      ( v2_tex_2(X0_51,X0_50) != iProver_top
% 2.33/1.00      | m1_pre_topc(sK1(X0_50,X0_51),X0_50) = iProver_top
% 2.33/1.00      | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_50))) != iProver_top
% 2.33/1.00      | v2_pre_topc(X0_50) != iProver_top
% 2.33/1.00      | l1_pre_topc(X0_50) != iProver_top
% 2.33/1.00      | v2_struct_0(X0_50) = iProver_top
% 2.33/1.00      | v1_xboole_0(X0_51) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_2583]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_4217,plain,
% 2.33/1.00      ( v2_tex_2(sK3,sK2) != iProver_top
% 2.33/1.00      | m1_pre_topc(sK1(sK2,sK3),sK2) = iProver_top
% 2.33/1.00      | v2_pre_topc(sK2) != iProver_top
% 2.33/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.33/1.00      | v2_struct_0(sK2) = iProver_top
% 2.33/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_3276,c_3270]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_30,negated_conjecture,
% 2.33/1.00      ( ~ v2_struct_0(sK2) ),
% 2.33/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_31,plain,
% 2.33/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_29,negated_conjecture,
% 2.33/1.00      ( v2_pre_topc(sK2) ),
% 2.33/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_32,plain,
% 2.33/1.00      ( v2_pre_topc(sK2) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_27,negated_conjecture,
% 2.33/1.00      ( l1_pre_topc(sK2) ),
% 2.33/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_34,plain,
% 2.33/1.00      ( l1_pre_topc(sK2) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_26,negated_conjecture,
% 2.33/1.00      ( ~ v1_xboole_0(sK3) ),
% 2.33/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_35,plain,
% 2.33/1.00      ( v1_xboole_0(sK3) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_36,plain,
% 2.33/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_24,negated_conjecture,
% 2.33/1.00      ( v2_tex_2(sK3,sK2) | v1_zfmisc_1(sK3) ),
% 2.33/1.00      inference(cnf_transformation,[],[f89]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_229,plain,
% 2.33/1.00      ( v1_zfmisc_1(sK3) | v2_tex_2(sK3,sK2) ),
% 2.33/1.00      inference(prop_impl,[status(thm)],[c_24]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_230,plain,
% 2.33/1.00      ( v2_tex_2(sK3,sK2) | v1_zfmisc_1(sK3) ),
% 2.33/1.00      inference(renaming,[status(thm)],[c_229]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_898,plain,
% 2.33/1.00      ( m1_pre_topc(sK1(X0,X1),X0)
% 2.33/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.33/1.00      | ~ v2_pre_topc(X0)
% 2.33/1.00      | v1_zfmisc_1(sK3)
% 2.33/1.00      | ~ l1_pre_topc(X0)
% 2.33/1.00      | v2_struct_0(X0)
% 2.33/1.00      | v1_xboole_0(X1)
% 2.33/1.00      | sK2 != X0
% 2.33/1.00      | sK3 != X1 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_230]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_899,plain,
% 2.33/1.00      ( m1_pre_topc(sK1(sK2,sK3),sK2)
% 2.33/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.33/1.00      | ~ v2_pre_topc(sK2)
% 2.33/1.00      | v1_zfmisc_1(sK3)
% 2.33/1.00      | ~ l1_pre_topc(sK2)
% 2.33/1.00      | v2_struct_0(sK2)
% 2.33/1.00      | v1_xboole_0(sK3) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_898]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_901,plain,
% 2.33/1.00      ( v1_zfmisc_1(sK3) | m1_pre_topc(sK1(sK2,sK3),sK2) ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_899,c_30,c_29,c_27,c_26,c_25]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_902,plain,
% 2.33/1.00      ( m1_pre_topc(sK1(sK2,sK3),sK2) | v1_zfmisc_1(sK3) ),
% 2.33/1.00      inference(renaming,[status(thm)],[c_901]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_903,plain,
% 2.33/1.00      ( m1_pre_topc(sK1(sK2,sK3),sK2) = iProver_top
% 2.33/1.00      | v1_zfmisc_1(sK3) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_902]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2591,plain,( X0_50 = X0_50 ),theory(equality) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2623,plain,
% 2.33/1.00      ( sK2 = sK2 ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_2591]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_0,plain,
% 2.33/1.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3,plain,
% 2.33/1.00      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~ r2_hidden(X0,X1) ),
% 2.33/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_451,plain,
% 2.33/1.00      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
% 2.33/1.00      | v1_xboole_0(X2)
% 2.33/1.00      | X1 != X2
% 2.33/1.00      | sK0(X2) != X0 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_3]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_452,plain,
% 2.33/1.00      ( m1_subset_1(k1_tarski(sK0(X0)),k1_zfmisc_1(X0))
% 2.33/1.00      | v1_xboole_0(X0) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_451]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2570,plain,
% 2.33/1.00      ( m1_subset_1(k1_tarski(sK0(X0_51)),k1_zfmisc_1(X0_51))
% 2.33/1.00      | v1_xboole_0(X0_51) ),
% 2.33/1.00      inference(subtyping,[status(esa)],[c_452]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2658,plain,
% 2.33/1.00      ( m1_subset_1(k1_tarski(sK0(X0_51)),k1_zfmisc_1(X0_51)) = iProver_top
% 2.33/1.00      | v1_xboole_0(X0_51) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_2570]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2660,plain,
% 2.33/1.00      ( m1_subset_1(k1_tarski(sK0(sK3)),k1_zfmisc_1(sK3)) = iProver_top
% 2.33/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_2658]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_6,plain,
% 2.33/1.00      ( m1_subset_1(X0,X1)
% 2.33/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.33/1.00      | ~ r2_hidden(X0,X2) ),
% 2.33/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_465,plain,
% 2.33/1.00      ( m1_subset_1(X0,X1)
% 2.33/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.33/1.00      | v1_xboole_0(X3)
% 2.33/1.00      | X2 != X3
% 2.33/1.00      | sK0(X3) != X0 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_6]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_466,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.33/1.00      | m1_subset_1(sK0(X0),X1)
% 2.33/1.00      | v1_xboole_0(X0) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_465]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2569,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
% 2.33/1.00      | m1_subset_1(sK0(X0_51),X1_51)
% 2.33/1.00      | v1_xboole_0(X0_51) ),
% 2.33/1.00      inference(subtyping,[status(esa)],[c_466]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3508,plain,
% 2.33/1.00      ( m1_subset_1(sK0(sK3),u1_struct_0(sK2))
% 2.33/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.33/1.00      | v1_xboole_0(sK3) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_2569]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3509,plain,
% 2.33/1.00      ( m1_subset_1(sK0(sK3),u1_struct_0(sK2)) = iProver_top
% 2.33/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.33/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_3508]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_22,plain,
% 2.33/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 2.33/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.33/1.00      | ~ v2_pre_topc(X0)
% 2.33/1.00      | ~ l1_pre_topc(X0)
% 2.33/1.00      | v2_struct_0(X0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2580,plain,
% 2.33/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(X0_50),X0_51),X0_50)
% 2.33/1.00      | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
% 2.33/1.00      | ~ v2_pre_topc(X0_50)
% 2.33/1.00      | ~ l1_pre_topc(X0_50)
% 2.33/1.00      | v2_struct_0(X0_50) ),
% 2.33/1.00      inference(subtyping,[status(esa)],[c_22]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3546,plain,
% 2.33/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),sK0(sK3)),sK2)
% 2.33/1.00      | ~ m1_subset_1(sK0(sK3),u1_struct_0(sK2))
% 2.33/1.00      | ~ v2_pre_topc(sK2)
% 2.33/1.00      | ~ l1_pre_topc(sK2)
% 2.33/1.00      | v2_struct_0(sK2) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_2580]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3547,plain,
% 2.33/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),sK0(sK3)),sK2) = iProver_top
% 2.33/1.00      | m1_subset_1(sK0(sK3),u1_struct_0(sK2)) != iProver_top
% 2.33/1.00      | v2_pre_topc(sK2) != iProver_top
% 2.33/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.33/1.00      | v2_struct_0(sK2) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_3546]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_11,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0,X1)
% 2.33/1.00      | v1_xboole_0(X1)
% 2.33/1.00      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2586,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0_51,X1_51)
% 2.33/1.00      | v1_xboole_0(X1_51)
% 2.33/1.00      | k6_domain_1(X1_51,X0_51) = k1_tarski(X0_51) ),
% 2.33/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3550,plain,
% 2.33/1.00      ( ~ m1_subset_1(sK0(sK3),u1_struct_0(sK2))
% 2.33/1.00      | v1_xboole_0(u1_struct_0(sK2))
% 2.33/1.00      | k6_domain_1(u1_struct_0(sK2),sK0(sK3)) = k1_tarski(sK0(sK3)) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_2586]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3551,plain,
% 2.33/1.00      ( k6_domain_1(u1_struct_0(sK2),sK0(sK3)) = k1_tarski(sK0(sK3))
% 2.33/1.00      | m1_subset_1(sK0(sK3),u1_struct_0(sK2)) != iProver_top
% 2.33/1.00      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_3550]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2607,plain,
% 2.33/1.00      ( ~ v2_tex_2(X0_51,X0_50)
% 2.33/1.00      | v2_tex_2(X1_51,X1_50)
% 2.33/1.00      | X1_51 != X0_51
% 2.33/1.00      | X1_50 != X0_50 ),
% 2.33/1.00      theory(equality) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3636,plain,
% 2.33/1.00      ( v2_tex_2(X0_51,X0_50)
% 2.33/1.00      | ~ v2_tex_2(k6_domain_1(u1_struct_0(sK2),sK0(sK3)),sK2)
% 2.33/1.00      | X0_51 != k6_domain_1(u1_struct_0(sK2),sK0(sK3))
% 2.33/1.00      | X0_50 != sK2 ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_2607]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3637,plain,
% 2.33/1.00      ( X0_51 != k6_domain_1(u1_struct_0(sK2),sK0(sK3))
% 2.33/1.00      | X0_50 != sK2
% 2.33/1.00      | v2_tex_2(X0_51,X0_50) = iProver_top
% 2.33/1.00      | v2_tex_2(k6_domain_1(u1_struct_0(sK2),sK0(sK3)),sK2) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_3636]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3639,plain,
% 2.33/1.00      ( sK3 != k6_domain_1(u1_struct_0(sK2),sK0(sK3))
% 2.33/1.00      | sK2 != sK2
% 2.33/1.00      | v2_tex_2(k6_domain_1(u1_struct_0(sK2),sK0(sK3)),sK2) != iProver_top
% 2.33/1.00      | v2_tex_2(sK3,sK2) = iProver_top ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_3637]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_4,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.33/1.00      | ~ v1_xboole_0(X1)
% 2.33/1.00      | v1_xboole_0(X0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2588,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
% 2.33/1.00      | ~ v1_xboole_0(X1_51)
% 2.33/1.00      | v1_xboole_0(X0_51) ),
% 2.33/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3265,plain,
% 2.33/1.00      ( m1_subset_1(X0_51,k1_zfmisc_1(X1_51)) != iProver_top
% 2.33/1.00      | v1_xboole_0(X1_51) != iProver_top
% 2.33/1.00      | v1_xboole_0(X0_51) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_2588]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3725,plain,
% 2.33/1.00      ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top
% 2.33/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_3276,c_3265]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2,plain,
% 2.33/1.00      ( ~ v1_xboole_0(k1_tarski(X0)) ),
% 2.33/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2589,plain,
% 2.33/1.00      ( ~ v1_xboole_0(k1_tarski(X0_51)) ),
% 2.33/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3854,plain,
% 2.33/1.00      ( ~ v1_xboole_0(k1_tarski(sK0(X0_51))) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_2589]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3855,plain,
% 2.33/1.00      ( v1_xboole_0(k1_tarski(sK0(X0_51))) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_3854]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3857,plain,
% 2.33/1.00      ( v1_xboole_0(k1_tarski(sK0(sK3))) != iProver_top ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_3855]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_5,plain,
% 2.33/1.00      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.33/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_17,plain,
% 2.33/1.00      ( ~ r1_tarski(X0,X1)
% 2.33/1.00      | ~ v1_zfmisc_1(X1)
% 2.33/1.00      | v1_xboole_0(X0)
% 2.33/1.00      | v1_xboole_0(X1)
% 2.33/1.00      | X1 = X0 ),
% 2.33/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_391,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.33/1.00      | ~ v1_zfmisc_1(X1)
% 2.33/1.00      | v1_xboole_0(X0)
% 2.33/1.00      | v1_xboole_0(X1)
% 2.33/1.00      | X1 = X0 ),
% 2.33/1.00      inference(resolution,[status(thm)],[c_5,c_17]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_395,plain,
% 2.33/1.00      ( v1_xboole_0(X0)
% 2.33/1.00      | ~ v1_zfmisc_1(X1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.33/1.00      | X1 = X0 ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_391,c_4]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_396,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.33/1.00      | ~ v1_zfmisc_1(X1)
% 2.33/1.00      | v1_xboole_0(X0)
% 2.33/1.00      | X1 = X0 ),
% 2.33/1.00      inference(renaming,[status(thm)],[c_395]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2571,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
% 2.33/1.00      | ~ v1_zfmisc_1(X1_51)
% 2.33/1.00      | v1_xboole_0(X0_51)
% 2.33/1.00      | X1_51 = X0_51 ),
% 2.33/1.00      inference(subtyping,[status(esa)],[c_396]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3903,plain,
% 2.33/1.00      ( ~ m1_subset_1(k1_tarski(sK0(X0_51)),k1_zfmisc_1(X1_51))
% 2.33/1.00      | ~ v1_zfmisc_1(X1_51)
% 2.33/1.00      | v1_xboole_0(k1_tarski(sK0(X0_51)))
% 2.33/1.00      | X1_51 = k1_tarski(sK0(X0_51)) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_2571]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3904,plain,
% 2.33/1.00      ( X0_51 = k1_tarski(sK0(X1_51))
% 2.33/1.00      | m1_subset_1(k1_tarski(sK0(X1_51)),k1_zfmisc_1(X0_51)) != iProver_top
% 2.33/1.00      | v1_zfmisc_1(X0_51) != iProver_top
% 2.33/1.00      | v1_xboole_0(k1_tarski(sK0(X1_51))) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_3903]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3906,plain,
% 2.33/1.00      ( sK3 = k1_tarski(sK0(sK3))
% 2.33/1.00      | m1_subset_1(k1_tarski(sK0(sK3)),k1_zfmisc_1(sK3)) != iProver_top
% 2.33/1.00      | v1_zfmisc_1(sK3) != iProver_top
% 2.33/1.00      | v1_xboole_0(k1_tarski(sK0(sK3))) = iProver_top ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_3904]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2593,plain,
% 2.33/1.00      ( X0_51 != X1_51 | X2_51 != X1_51 | X2_51 = X0_51 ),
% 2.33/1.00      theory(equality) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3792,plain,
% 2.33/1.00      ( X0_51 != X1_51
% 2.33/1.00      | X0_51 = k6_domain_1(u1_struct_0(sK2),sK0(sK3))
% 2.33/1.00      | k6_domain_1(u1_struct_0(sK2),sK0(sK3)) != X1_51 ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_2593]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_4274,plain,
% 2.33/1.00      ( X0_51 = k6_domain_1(u1_struct_0(sK2),sK0(sK3))
% 2.33/1.00      | X0_51 != k1_tarski(sK0(sK3))
% 2.33/1.00      | k6_domain_1(u1_struct_0(sK2),sK0(sK3)) != k1_tarski(sK0(sK3)) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_3792]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_4275,plain,
% 2.33/1.00      ( k6_domain_1(u1_struct_0(sK2),sK0(sK3)) != k1_tarski(sK0(sK3))
% 2.33/1.00      | sK3 = k6_domain_1(u1_struct_0(sK2),sK0(sK3))
% 2.33/1.00      | sK3 != k1_tarski(sK0(sK3)) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_4274]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_4584,plain,
% 2.33/1.00      ( m1_pre_topc(sK1(sK2,sK3),sK2) = iProver_top ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_4217,c_31,c_32,c_34,c_35,c_36,c_903,c_2623,c_2660,
% 2.33/1.00                 c_3509,c_3547,c_3551,c_3639,c_3725,c_3857,c_3906,c_4275]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_12,plain,
% 2.33/1.00      ( ~ v2_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_16,plain,
% 2.33/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.33/1.00      | ~ v2_tdlat_3(X1)
% 2.33/1.00      | v2_tdlat_3(X0)
% 2.33/1.00      | ~ v2_pre_topc(X1)
% 2.33/1.00      | ~ l1_pre_topc(X1)
% 2.33/1.00      | v2_struct_0(X1) ),
% 2.33/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1114,plain,
% 2.33/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.33/1.00      | ~ v2_tdlat_3(X2)
% 2.33/1.00      | ~ v2_tdlat_3(X1)
% 2.33/1.00      | v2_tdlat_3(X0)
% 2.33/1.00      | ~ l1_pre_topc(X2)
% 2.33/1.00      | ~ l1_pre_topc(X1)
% 2.33/1.00      | v2_struct_0(X1)
% 2.33/1.00      | X1 != X2 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_16]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1115,plain,
% 2.33/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.33/1.00      | ~ v2_tdlat_3(X1)
% 2.33/1.00      | v2_tdlat_3(X0)
% 2.33/1.00      | ~ l1_pre_topc(X1)
% 2.33/1.00      | v2_struct_0(X1) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_1114]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2566,plain,
% 2.33/1.00      ( ~ m1_pre_topc(X0_50,X1_50)
% 2.33/1.00      | ~ v2_tdlat_3(X1_50)
% 2.33/1.00      | v2_tdlat_3(X0_50)
% 2.33/1.00      | ~ l1_pre_topc(X1_50)
% 2.33/1.00      | v2_struct_0(X1_50) ),
% 2.33/1.00      inference(subtyping,[status(esa)],[c_1115]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3287,plain,
% 2.33/1.00      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 2.33/1.00      | v2_tdlat_3(X1_50) != iProver_top
% 2.33/1.00      | v2_tdlat_3(X0_50) = iProver_top
% 2.33/1.00      | l1_pre_topc(X1_50) != iProver_top
% 2.33/1.00      | v2_struct_0(X1_50) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_2566]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_5414,plain,
% 2.33/1.00      ( v2_tdlat_3(sK1(sK2,sK3)) = iProver_top
% 2.33/1.00      | v2_tdlat_3(sK2) != iProver_top
% 2.33/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.33/1.00      | v2_struct_0(sK2) = iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_4584,c_3287]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_18,plain,
% 2.33/1.00      ( ~ v2_tex_2(X0,X1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | ~ v2_pre_topc(X1)
% 2.33/1.00      | ~ l1_pre_topc(X1)
% 2.33/1.00      | v2_struct_0(X1)
% 2.33/1.00      | v1_xboole_0(X0)
% 2.33/1.00      | u1_struct_0(sK1(X1,X0)) = X0 ),
% 2.33/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2584,plain,
% 2.33/1.00      ( ~ v2_tex_2(X0_51,X0_50)
% 2.33/1.00      | ~ m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_50)))
% 2.33/1.00      | ~ v2_pre_topc(X0_50)
% 2.33/1.00      | ~ l1_pre_topc(X0_50)
% 2.33/1.00      | v2_struct_0(X0_50)
% 2.33/1.00      | v1_xboole_0(X0_51)
% 2.33/1.00      | u1_struct_0(sK1(X0_50,X0_51)) = X0_51 ),
% 2.33/1.00      inference(subtyping,[status(esa)],[c_18]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3269,plain,
% 2.33/1.00      ( u1_struct_0(sK1(X0_50,X0_51)) = X0_51
% 2.33/1.00      | v2_tex_2(X0_51,X0_50) != iProver_top
% 2.33/1.00      | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_50))) != iProver_top
% 2.33/1.00      | v2_pre_topc(X0_50) != iProver_top
% 2.33/1.00      | l1_pre_topc(X0_50) != iProver_top
% 2.33/1.00      | v2_struct_0(X0_50) = iProver_top
% 2.33/1.00      | v1_xboole_0(X0_51) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_2584]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_4105,plain,
% 2.33/1.00      ( u1_struct_0(sK1(sK2,sK3)) = sK3
% 2.33/1.00      | v2_tex_2(sK3,sK2) != iProver_top
% 2.33/1.00      | v2_pre_topc(sK2) != iProver_top
% 2.33/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.33/1.00      | v2_struct_0(sK2) = iProver_top
% 2.33/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_3276,c_3269]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_37,plain,
% 2.33/1.00      ( v2_tex_2(sK3,sK2) = iProver_top
% 2.33/1.00      | v1_zfmisc_1(sK3) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_23,negated_conjecture,
% 2.33/1.00      ( ~ v2_tex_2(sK3,sK2) | ~ v1_zfmisc_1(sK3) ),
% 2.33/1.00      inference(cnf_transformation,[],[f90]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_38,plain,
% 2.33/1.00      ( v2_tex_2(sK3,sK2) != iProver_top
% 2.33/1.00      | v1_zfmisc_1(sK3) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_4391,plain,
% 2.33/1.00      ( u1_struct_0(sK1(sK2,sK3)) = sK3 ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_4105,c_31,c_32,c_34,c_35,c_36,c_37,c_38,c_2623,c_2660,
% 2.33/1.00                 c_3509,c_3547,c_3551,c_3639,c_3725,c_3857,c_3906,c_4275]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_14,plain,
% 2.33/1.00      ( ~ v1_tdlat_3(X0)
% 2.33/1.00      | ~ v2_tdlat_3(X0)
% 2.33/1.00      | ~ v2_pre_topc(X0)
% 2.33/1.00      | ~ l1_pre_topc(X0)
% 2.33/1.00      | v2_struct_0(X0)
% 2.33/1.00      | v7_struct_0(X0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_8,plain,
% 2.33/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_7,plain,
% 2.33/1.00      ( ~ l1_struct_0(X0) | ~ v2_struct_0(X0) | v7_struct_0(X0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_172,plain,
% 2.33/1.00      ( ~ l1_pre_topc(X0)
% 2.33/1.00      | ~ v1_tdlat_3(X0)
% 2.33/1.00      | ~ v2_tdlat_3(X0)
% 2.33/1.00      | v7_struct_0(X0) ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_14,c_12,c_8,c_7]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_173,plain,
% 2.33/1.00      ( ~ v1_tdlat_3(X0)
% 2.33/1.00      | ~ v2_tdlat_3(X0)
% 2.33/1.00      | ~ l1_pre_topc(X0)
% 2.33/1.00      | v7_struct_0(X0) ),
% 2.33/1.00      inference(renaming,[status(thm)],[c_172]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_10,plain,
% 2.33/1.00      ( v1_zfmisc_1(u1_struct_0(X0))
% 2.33/1.00      | ~ l1_struct_0(X0)
% 2.33/1.00      | ~ v7_struct_0(X0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_417,plain,
% 2.33/1.00      ( v1_zfmisc_1(u1_struct_0(X0))
% 2.33/1.00      | ~ l1_pre_topc(X0)
% 2.33/1.00      | ~ v7_struct_0(X0) ),
% 2.33/1.00      inference(resolution,[status(thm)],[c_8,c_10]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_499,plain,
% 2.33/1.00      ( ~ v1_tdlat_3(X0)
% 2.33/1.00      | ~ v2_tdlat_3(X0)
% 2.33/1.00      | v1_zfmisc_1(u1_struct_0(X0))
% 2.33/1.00      | ~ l1_pre_topc(X0) ),
% 2.33/1.00      inference(resolution,[status(thm)],[c_173,c_417]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2567,plain,
% 2.33/1.00      ( ~ v1_tdlat_3(X0_50)
% 2.33/1.00      | ~ v2_tdlat_3(X0_50)
% 2.33/1.00      | v1_zfmisc_1(u1_struct_0(X0_50))
% 2.33/1.00      | ~ l1_pre_topc(X0_50) ),
% 2.33/1.00      inference(subtyping,[status(esa)],[c_499]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3286,plain,
% 2.33/1.00      ( v1_tdlat_3(X0_50) != iProver_top
% 2.33/1.00      | v2_tdlat_3(X0_50) != iProver_top
% 2.33/1.00      | v1_zfmisc_1(u1_struct_0(X0_50)) = iProver_top
% 2.33/1.00      | l1_pre_topc(X0_50) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_2567]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_4399,plain,
% 2.33/1.00      ( v1_tdlat_3(sK1(sK2,sK3)) != iProver_top
% 2.33/1.00      | v2_tdlat_3(sK1(sK2,sK3)) != iProver_top
% 2.33/1.00      | v1_zfmisc_1(sK3) = iProver_top
% 2.33/1.00      | l1_pre_topc(sK1(sK2,sK3)) != iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_4391,c_3286]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_20,plain,
% 2.33/1.00      ( ~ v2_tex_2(X0,X1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | v1_tdlat_3(sK1(X1,X0))
% 2.33/1.00      | ~ v2_pre_topc(X1)
% 2.33/1.00      | ~ l1_pre_topc(X1)
% 2.33/1.00      | v2_struct_0(X1)
% 2.33/1.00      | v1_xboole_0(X0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_884,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | v1_tdlat_3(sK1(X1,X0))
% 2.33/1.00      | ~ v2_pre_topc(X1)
% 2.33/1.00      | v1_zfmisc_1(sK3)
% 2.33/1.00      | ~ l1_pre_topc(X1)
% 2.33/1.00      | v2_struct_0(X1)
% 2.33/1.00      | v1_xboole_0(X0)
% 2.33/1.00      | sK2 != X1
% 2.33/1.00      | sK3 != X0 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_230]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_885,plain,
% 2.33/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.33/1.00      | v1_tdlat_3(sK1(sK2,sK3))
% 2.33/1.00      | ~ v2_pre_topc(sK2)
% 2.33/1.00      | v1_zfmisc_1(sK3)
% 2.33/1.00      | ~ l1_pre_topc(sK2)
% 2.33/1.00      | v2_struct_0(sK2)
% 2.33/1.00      | v1_xboole_0(sK3) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_884]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_887,plain,
% 2.33/1.00      ( v1_zfmisc_1(sK3) | v1_tdlat_3(sK1(sK2,sK3)) ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_885,c_30,c_29,c_27,c_26,c_25]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_888,plain,
% 2.33/1.00      ( v1_tdlat_3(sK1(sK2,sK3)) | v1_zfmisc_1(sK3) ),
% 2.33/1.00      inference(renaming,[status(thm)],[c_887]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_889,plain,
% 2.33/1.00      ( v1_tdlat_3(sK1(sK2,sK3)) = iProver_top
% 2.33/1.00      | v1_zfmisc_1(sK3) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_888]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_9,plain,
% 2.33/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2587,plain,
% 2.33/1.00      ( ~ m1_pre_topc(X0_50,X1_50)
% 2.33/1.00      | ~ l1_pre_topc(X1_50)
% 2.33/1.00      | l1_pre_topc(X0_50) ),
% 2.33/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3266,plain,
% 2.33/1.00      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 2.33/1.00      | l1_pre_topc(X1_50) != iProver_top
% 2.33/1.00      | l1_pre_topc(X0_50) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_2587]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_4589,plain,
% 2.33/1.00      ( l1_pre_topc(sK1(sK2,sK3)) = iProver_top
% 2.33/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_4584,c_3266]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_4758,plain,
% 2.33/1.00      ( v2_tdlat_3(sK1(sK2,sK3)) != iProver_top ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_4399,c_31,c_32,c_34,c_35,c_36,c_38,c_889,c_2623,
% 2.33/1.00                 c_2660,c_3509,c_3547,c_3551,c_3639,c_3725,c_3857,c_3906,
% 2.33/1.00                 c_4275,c_4589]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_28,negated_conjecture,
% 2.33/1.00      ( v2_tdlat_3(sK2) ),
% 2.33/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_33,plain,
% 2.33/1.00      ( v2_tdlat_3(sK2) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(contradiction,plain,
% 2.33/1.00      ( $false ),
% 2.33/1.00      inference(minisat,[status(thm)],[c_5414,c_4758,c_34,c_33,c_31]) ).
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
% 2.33/1.00  parsing_time:                           0.008
% 2.33/1.00  unif_index_cands_time:                  0.
% 2.33/1.00  unif_index_add_time:                    0.
% 2.33/1.00  orderings_time:                         0.
% 2.33/1.00  out_proof_time:                         0.009
% 2.33/1.00  total_time:                             0.164
% 2.33/1.00  num_of_symbols:                         55
% 2.33/1.00  num_of_terms:                           3033
% 2.33/1.00  
% 2.33/1.00  ------ Preprocessing
% 2.33/1.00  
% 2.33/1.00  num_of_splits:                          0
% 2.33/1.00  num_of_split_atoms:                     0
% 2.33/1.00  num_of_reused_defs:                     0
% 2.33/1.00  num_eq_ax_congr_red:                    21
% 2.33/1.00  num_of_sem_filtered_clauses:            1
% 2.33/1.00  num_of_subtypes:                        2
% 2.33/1.00  monotx_restored_types:                  0
% 2.33/1.00  sat_num_of_epr_types:                   0
% 2.33/1.00  sat_num_of_non_cyclic_types:            0
% 2.33/1.00  sat_guarded_non_collapsed_types:        1
% 2.33/1.00  num_pure_diseq_elim:                    0
% 2.33/1.00  simp_replaced_by:                       0
% 2.33/1.00  res_preprocessed:                       136
% 2.33/1.00  prep_upred:                             0
% 2.33/1.00  prep_unflattend:                        89
% 2.33/1.00  smt_new_axioms:                         0
% 2.33/1.00  pred_elim_cands:                        10
% 2.33/1.00  pred_elim:                              4
% 2.33/1.00  pred_elim_cl:                           5
% 2.33/1.00  pred_elim_cycles:                       16
% 2.33/1.00  merged_defs:                            8
% 2.33/1.00  merged_defs_ncl:                        0
% 2.33/1.00  bin_hyper_res:                          8
% 2.33/1.00  prep_cycles:                            4
% 2.33/1.00  pred_elim_time:                         0.032
% 2.33/1.00  splitting_time:                         0.
% 2.33/1.00  sem_filter_time:                        0.
% 2.33/1.00  monotx_time:                            0.
% 2.33/1.00  subtype_inf_time:                       0.
% 2.33/1.00  
% 2.33/1.00  ------ Problem properties
% 2.33/1.00  
% 2.33/1.00  clauses:                                24
% 2.33/1.00  conjectures:                            8
% 2.33/1.00  epr:                                    10
% 2.33/1.00  horn:                                   13
% 2.33/1.00  ground:                                 8
% 2.33/1.00  unary:                                  7
% 2.33/1.00  binary:                                 3
% 2.33/1.00  lits:                                   77
% 2.33/1.00  lits_eq:                                3
% 2.33/1.00  fd_pure:                                0
% 2.33/1.00  fd_pseudo:                              0
% 2.33/1.00  fd_cond:                                0
% 2.33/1.00  fd_pseudo_cond:                         1
% 2.33/1.00  ac_symbols:                             0
% 2.33/1.00  
% 2.33/1.00  ------ Propositional Solver
% 2.33/1.00  
% 2.33/1.00  prop_solver_calls:                      28
% 2.33/1.00  prop_fast_solver_calls:                 1606
% 2.33/1.00  smt_solver_calls:                       0
% 2.33/1.00  smt_fast_solver_calls:                  0
% 2.33/1.00  prop_num_of_clauses:                    1096
% 2.33/1.00  prop_preprocess_simplified:             5281
% 2.33/1.00  prop_fo_subsumed:                       133
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
% 2.33/1.00  inst_num_of_clauses:                    297
% 2.33/1.00  inst_num_in_passive:                    84
% 2.33/1.00  inst_num_in_active:                     195
% 2.33/1.00  inst_num_in_unprocessed:                18
% 2.33/1.00  inst_num_of_loops:                      220
% 2.33/1.00  inst_num_of_learning_restarts:          0
% 2.33/1.00  inst_num_moves_active_passive:          21
% 2.33/1.00  inst_lit_activity:                      0
% 2.33/1.00  inst_lit_activity_moves:                0
% 2.33/1.00  inst_num_tautologies:                   0
% 2.33/1.00  inst_num_prop_implied:                  0
% 2.33/1.00  inst_num_existing_simplified:           0
% 2.33/1.00  inst_num_eq_res_simplified:             0
% 2.33/1.00  inst_num_child_elim:                    0
% 2.33/1.00  inst_num_of_dismatching_blockings:      103
% 2.33/1.00  inst_num_of_non_proper_insts:           326
% 2.33/1.00  inst_num_of_duplicates:                 0
% 2.33/1.00  inst_inst_num_from_inst_to_res:         0
% 2.33/1.00  inst_dismatching_checking_time:         0.
% 2.33/1.00  
% 2.33/1.00  ------ Resolution
% 2.33/1.00  
% 2.33/1.00  res_num_of_clauses:                     0
% 2.33/1.00  res_num_in_passive:                     0
% 2.33/1.00  res_num_in_active:                      0
% 2.33/1.00  res_num_of_loops:                       140
% 2.33/1.00  res_forward_subset_subsumed:            54
% 2.33/1.00  res_backward_subset_subsumed:           0
% 2.33/1.00  res_forward_subsumed:                   0
% 2.33/1.00  res_backward_subsumed:                  1
% 2.33/1.00  res_forward_subsumption_resolution:     1
% 2.33/1.00  res_backward_subsumption_resolution:    0
% 2.33/1.00  res_clause_to_clause_subsumption:       82
% 2.33/1.00  res_orphan_elimination:                 0
% 2.33/1.00  res_tautology_del:                      79
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
% 2.33/1.00  sup_num_of_clauses:                     53
% 2.33/1.00  sup_num_in_active:                      44
% 2.33/1.00  sup_num_in_passive:                     9
% 2.33/1.00  sup_num_of_loops:                       43
% 2.33/1.00  sup_fw_superposition:                   21
% 2.33/1.00  sup_bw_superposition:                   15
% 2.33/1.00  sup_immediate_simplified:               4
% 2.33/1.00  sup_given_eliminated:                   0
% 2.33/1.00  comparisons_done:                       0
% 2.33/1.00  comparisons_avoided:                    0
% 2.33/1.00  
% 2.33/1.00  ------ Simplifications
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  sim_fw_subset_subsumed:                 3
% 2.33/1.00  sim_bw_subset_subsumed:                 1
% 2.33/1.00  sim_fw_subsumed:                        0
% 2.33/1.00  sim_bw_subsumed:                        0
% 2.33/1.00  sim_fw_subsumption_res:                 0
% 2.33/1.00  sim_bw_subsumption_res:                 0
% 2.33/1.00  sim_tautology_del:                      2
% 2.33/1.00  sim_eq_tautology_del:                   0
% 2.33/1.00  sim_eq_res_simp:                        0
% 2.33/1.00  sim_fw_demodulated:                     0
% 2.33/1.00  sim_bw_demodulated:                     0
% 2.33/1.00  sim_light_normalised:                   2
% 2.33/1.00  sim_joinable_taut:                      0
% 2.33/1.00  sim_joinable_simp:                      0
% 2.33/1.00  sim_ac_normalised:                      0
% 2.33/1.00  sim_smt_subsumption:                    0
% 2.33/1.00  
%------------------------------------------------------------------------------
