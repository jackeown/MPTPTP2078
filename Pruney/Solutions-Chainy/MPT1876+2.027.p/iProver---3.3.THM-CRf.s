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
% DateTime   : Thu Dec  3 12:26:52 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :  194 (2687 expanded)
%              Number of clauses        :  126 ( 655 expanded)
%              Number of leaves         :   19 ( 621 expanded)
%              Depth                    :   32
%              Number of atoms          :  797 (20596 expanded)
%              Number of equality atoms :  159 ( 735 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f45,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f42,f44,f43])).

fof(f69,plain,
    ( v1_zfmisc_1(sK3)
    | v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
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

fof(f14,plain,(
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
    inference(pure_predicate_removal,[],[f10])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f39])).

fof(f61,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK1(X0,X1)) = X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f63,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f66,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK1(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK1(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK1(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) )
           => ( v7_struct_0(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
          | ~ v1_tdlat_3(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
          | ~ v1_tdlat_3(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v7_struct_0(X1)
      | ~ v1_tdlat_3(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,(
    v2_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f51,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK0(X0)) = X0
        & m1_subset_1(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK0(X0)) = X0
            & m1_subset_1(sK0(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f55,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK0(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,
    ( ~ v1_zfmisc_1(sK3)
    | ~ v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_18,negated_conjecture,
    ( v2_tex_2(sK3,sK2)
    | v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1392,negated_conjecture,
    ( v2_tex_2(sK3,sK2)
    | v1_zfmisc_1(sK3) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1783,plain,
    ( v2_tex_2(sK3,sK2) = iProver_top
    | v1_zfmisc_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1392])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1391,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1784,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1391])).

cnf(c_12,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_654,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK1(X1,X0)) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_23])).

cnf(c_655,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | v1_xboole_0(X0)
    | u1_struct_0(sK1(sK2,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_654])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_659,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | u1_struct_0(sK1(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_655,c_24,c_21])).

cnf(c_1388,plain,
    ( ~ v2_tex_2(X0_49,sK2)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0_49)
    | u1_struct_0(sK1(sK2,X0_49)) = X0_49 ),
    inference(subtyping,[status(esa)],[c_659])).

cnf(c_1787,plain,
    ( u1_struct_0(sK1(sK2,X0_49)) = X0_49
    | v2_tex_2(X0_49,sK2) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1388])).

cnf(c_1975,plain,
    ( u1_struct_0(sK1(sK2,sK3)) = sK3
    | v2_tex_2(sK3,sK2) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1784,c_1787])).

cnf(c_20,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_29,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2002,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | u1_struct_0(sK1(sK2,sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1975,c_29])).

cnf(c_2003,plain,
    ( u1_struct_0(sK1(sK2,sK3)) = sK3
    | v2_tex_2(sK3,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2002])).

cnf(c_2008,plain,
    ( u1_struct_0(sK1(sK2,sK3)) = sK3
    | v1_zfmisc_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1783,c_2003])).

cnf(c_181,plain,
    ( v1_zfmisc_1(sK3)
    | v2_tex_2(sK3,sK2) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_182,plain,
    ( v2_tex_2(sK3,sK2)
    | v1_zfmisc_1(sK3) ),
    inference(renaming,[status(thm)],[c_181])).

cnf(c_14,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v1_tdlat_3(sK1(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_630,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v1_tdlat_3(sK1(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_631,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | v1_tdlat_3(sK1(sK2,X0))
    | ~ l1_pre_topc(sK2)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_630])).

cnf(c_635,plain,
    ( v1_tdlat_3(sK1(sK2,X0))
    | ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_631,c_24,c_21])).

cnf(c_636,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_tdlat_3(sK1(sK2,X0))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_635])).

cnf(c_15,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK1(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_606,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK1(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_23])).

cnf(c_607,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_struct_0(sK1(sK2,X0))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_606])).

cnf(c_611,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_struct_0(sK1(sK2,X0))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_607,c_24,c_21])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_13,plain,
    ( ~ v2_tex_2(X0,X1)
    | m1_pre_topc(sK1(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_462,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X3)
    | v1_xboole_0(X0)
    | X1 != X2
    | sK1(X1,X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_13])).

cnf(c_463,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(sK1(X1,X0))
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_462])).

cnf(c_582,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(sK1(X1,X0))
    | v1_xboole_0(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_463,c_23])).

cnf(c_583,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | l1_pre_topc(sK1(sK2,X0))
    | ~ l1_pre_topc(sK2)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_582])).

cnf(c_587,plain,
    ( l1_pre_topc(sK1(sK2,X0))
    | ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_583,c_24,c_21])).

cnf(c_588,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | l1_pre_topc(sK1(sK2,X0))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_587])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_22,negated_conjecture,
    ( v2_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_359,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_22])).

cnf(c_360,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ v1_tdlat_3(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_364,plain,
    ( v7_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | ~ m1_pre_topc(X0,sK2)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_360,c_24,c_23,c_21])).

cnf(c_365,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | v7_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_364])).

cnf(c_3,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_5,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_321,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_3,c_5])).

cnf(c_388,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_365,c_321])).

cnf(c_489,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_tdlat_3(X2)
    | v1_zfmisc_1(u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v1_xboole_0(X0)
    | sK1(X1,X0) != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_388])).

cnf(c_490,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK1(sK2,X0))
    | v2_struct_0(sK2)
    | ~ v1_tdlat_3(sK1(sK2,X0))
    | v1_zfmisc_1(u1_struct_0(sK1(sK2,X0)))
    | ~ l1_pre_topc(sK1(sK2,X0))
    | ~ l1_pre_topc(sK2)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_489])).

cnf(c_494,plain,
    ( ~ l1_pre_topc(sK1(sK2,X0))
    | v1_zfmisc_1(u1_struct_0(sK1(sK2,X0)))
    | ~ v1_tdlat_3(sK1(sK2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | v2_struct_0(sK1(sK2,X0))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_490,c_24,c_23,c_21])).

cnf(c_495,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK1(sK2,X0))
    | ~ v1_tdlat_3(sK1(sK2,X0))
    | v1_zfmisc_1(u1_struct_0(sK1(sK2,X0)))
    | ~ l1_pre_topc(sK1(sK2,X0))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_494])).

cnf(c_699,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK1(sK2,X0))
    | ~ v1_tdlat_3(sK1(sK2,X0))
    | v1_zfmisc_1(u1_struct_0(sK1(sK2,X0)))
    | v1_xboole_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_588,c_495])).

cnf(c_708,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_tdlat_3(sK1(sK2,X0))
    | v1_zfmisc_1(u1_struct_0(sK1(sK2,X0)))
    | v1_xboole_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_611,c_699])).

cnf(c_717,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_zfmisc_1(u1_struct_0(sK1(sK2,X0)))
    | v1_xboole_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_636,c_708])).

cnf(c_732,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_zfmisc_1(u1_struct_0(sK1(sK2,X0)))
    | v1_zfmisc_1(sK3)
    | v1_xboole_0(X0)
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_182,c_717])).

cnf(c_733,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_zfmisc_1(u1_struct_0(sK1(sK2,sK3)))
    | v1_zfmisc_1(sK3)
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_732])).

cnf(c_735,plain,
    ( v1_zfmisc_1(sK3)
    | v1_zfmisc_1(u1_struct_0(sK1(sK2,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_733,c_20,c_19])).

cnf(c_736,plain,
    ( v1_zfmisc_1(u1_struct_0(sK1(sK2,sK3)))
    | v1_zfmisc_1(sK3) ),
    inference(renaming,[status(thm)],[c_735])).

cnf(c_737,plain,
    ( v1_zfmisc_1(u1_struct_0(sK1(sK2,sK3))) = iProver_top
    | v1_zfmisc_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_736])).

cnf(c_1400,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_1420,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1400])).

cnf(c_1407,plain,
    ( ~ v1_zfmisc_1(X0_49)
    | v1_zfmisc_1(X1_49)
    | X1_49 != X0_49 ),
    theory(equality)).

cnf(c_1990,plain,
    ( v1_zfmisc_1(X0_49)
    | ~ v1_zfmisc_1(u1_struct_0(sK1(sK2,X1_49)))
    | X0_49 != u1_struct_0(sK1(sK2,X1_49)) ),
    inference(instantiation,[status(thm)],[c_1407])).

cnf(c_1991,plain,
    ( X0_49 != u1_struct_0(sK1(sK2,X1_49))
    | v1_zfmisc_1(X0_49) = iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1(sK2,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1990])).

cnf(c_1993,plain,
    ( sK3 != u1_struct_0(sK1(sK2,sK3))
    | v1_zfmisc_1(u1_struct_0(sK1(sK2,sK3))) != iProver_top
    | v1_zfmisc_1(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1991])).

cnf(c_1402,plain,
    ( X0_49 != X1_49
    | X2_49 != X1_49
    | X2_49 = X0_49 ),
    theory(equality)).

cnf(c_2203,plain,
    ( X0_49 != X1_49
    | X0_49 = u1_struct_0(sK1(sK2,X2_49))
    | u1_struct_0(sK1(sK2,X2_49)) != X1_49 ),
    inference(instantiation,[status(thm)],[c_1402])).

cnf(c_2204,plain,
    ( u1_struct_0(sK1(sK2,sK3)) != sK3
    | sK3 = u1_struct_0(sK1(sK2,sK3))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2203])).

cnf(c_2227,plain,
    ( v1_zfmisc_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2008,c_737,c_1420,c_1993,c_2204])).

cnf(c_11,plain,
    ( m1_subset_1(sK0(X0),X0)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1394,plain,
    ( m1_subset_1(sK0(X0_49),X0_49)
    | ~ v1_zfmisc_1(X0_49)
    | v1_xboole_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1781,plain,
    ( m1_subset_1(sK0(X0_49),X0_49) = iProver_top
    | v1_zfmisc_1(X0_49) != iProver_top
    | v1_xboole_0(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1394])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1397,plain,
    ( ~ m1_subset_1(X0_49,X1_49)
    | v1_xboole_0(X1_49)
    | k6_domain_1(X1_49,X0_49) = k1_tarski(X0_49) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1778,plain,
    ( k6_domain_1(X0_49,X1_49) = k1_tarski(X1_49)
    | m1_subset_1(X1_49,X0_49) != iProver_top
    | v1_xboole_0(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1397])).

cnf(c_2138,plain,
    ( k6_domain_1(X0_49,sK0(X0_49)) = k1_tarski(sK0(X0_49))
    | v1_zfmisc_1(X0_49) != iProver_top
    | v1_xboole_0(X0_49) = iProver_top ),
    inference(superposition,[status(thm)],[c_1781,c_1778])).

cnf(c_2577,plain,
    ( k6_domain_1(sK3,sK0(sK3)) = k1_tarski(sK0(sK3))
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2227,c_2138])).

cnf(c_10,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | k6_domain_1(X0,sK0(X0)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1395,plain,
    ( ~ v1_zfmisc_1(X0_49)
    | v1_xboole_0(X0_49)
    | k6_domain_1(X0_49,sK0(X0_49)) = X0_49 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1780,plain,
    ( k6_domain_1(X0_49,sK0(X0_49)) = X0_49
    | v1_zfmisc_1(X0_49) != iProver_top
    | v1_xboole_0(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1395])).

cnf(c_2232,plain,
    ( k6_domain_1(sK3,sK0(sK3)) = sK3
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2227,c_1780])).

cnf(c_1429,plain,
    ( k6_domain_1(X0_49,sK0(X0_49)) = X0_49
    | v1_zfmisc_1(X0_49) != iProver_top
    | v1_xboole_0(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1395])).

cnf(c_1431,plain,
    ( k6_domain_1(sK3,sK0(sK3)) = sK3
    | v1_zfmisc_1(sK3) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1429])).

cnf(c_2264,plain,
    ( k6_domain_1(sK3,sK0(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2232,c_29,c_737,c_1420,c_1431,c_1993,c_2008,c_2204])).

cnf(c_2593,plain,
    ( k1_tarski(sK0(sK3)) = sK3
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2577,c_2264])).

cnf(c_2832,plain,
    ( k1_tarski(sK0(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2593,c_29])).

cnf(c_1,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_339,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_1,c_2])).

cnf(c_1389,plain,
    ( ~ m1_subset_1(X0_49,X1_49)
    | m1_subset_1(X0_49,X2_49)
    | ~ m1_subset_1(X1_49,k1_zfmisc_1(X2_49))
    | v1_xboole_0(X1_49) ),
    inference(subtyping,[status(esa)],[c_339])).

cnf(c_1786,plain,
    ( m1_subset_1(X0_49,X1_49) != iProver_top
    | m1_subset_1(X0_49,X2_49) = iProver_top
    | m1_subset_1(X1_49,k1_zfmisc_1(X2_49)) != iProver_top
    | v1_xboole_0(X1_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1389])).

cnf(c_2464,plain,
    ( m1_subset_1(X0_49,u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(X0_49,sK3) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1784,c_1786])).

cnf(c_2489,plain,
    ( m1_subset_1(X0_49,sK3) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2464,c_29])).

cnf(c_2490,plain,
    ( m1_subset_1(X0_49,u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(X0_49,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2489])).

cnf(c_2497,plain,
    ( k6_domain_1(u1_struct_0(sK2),X0_49) = k1_tarski(X0_49)
    | m1_subset_1(X0_49,sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2490,c_1778])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1398,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(X1_49))
    | ~ v1_xboole_0(X1_49)
    | v1_xboole_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1777,plain,
    ( m1_subset_1(X0_49,k1_zfmisc_1(X1_49)) != iProver_top
    | v1_xboole_0(X1_49) != iProver_top
    | v1_xboole_0(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1398])).

cnf(c_2014,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1784,c_1777])).

cnf(c_2599,plain,
    ( m1_subset_1(X0_49,sK3) != iProver_top
    | k6_domain_1(u1_struct_0(sK2),X0_49) = k1_tarski(X0_49) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2497,c_29,c_2014])).

cnf(c_2600,plain,
    ( k6_domain_1(u1_struct_0(sK2),X0_49) = k1_tarski(X0_49)
    | m1_subset_1(X0_49,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2599])).

cnf(c_2607,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK0(sK3)) = k1_tarski(sK0(sK3))
    | v1_zfmisc_1(sK3) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1781,c_2600])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1432,plain,
    ( m1_subset_1(sK0(X0_49),X0_49) = iProver_top
    | v1_zfmisc_1(X0_49) != iProver_top
    | v1_xboole_0(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1394])).

cnf(c_1434,plain,
    ( m1_subset_1(sK0(sK3),sK3) = iProver_top
    | v1_zfmisc_1(sK3) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1432])).

cnf(c_1915,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(X1_49))
    | ~ m1_subset_1(sK0(X0_49),X0_49)
    | m1_subset_1(sK0(X0_49),X1_49)
    | v1_xboole_0(X0_49) ),
    inference(instantiation,[status(thm)],[c_1389])).

cnf(c_1998,plain,
    ( m1_subset_1(sK0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1915])).

cnf(c_1999,plain,
    ( m1_subset_1(sK0(sK3),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK0(sK3),sK3) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1998])).

cnf(c_2030,plain,
    ( ~ m1_subset_1(sK0(sK3),u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK0(sK3)) = k1_tarski(sK0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1397])).

cnf(c_2031,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK0(sK3)) = k1_tarski(sK0(sK3))
    | m1_subset_1(sK0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2030])).

cnf(c_2674,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK0(sK3)) = k1_tarski(sK0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2607,c_29,c_30,c_737,c_1420,c_1434,c_1993,c_1999,c_2008,c_2014,c_2031,c_2204])).

cnf(c_16,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_678,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_679,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_678])).

cnf(c_683,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_679,c_24,c_21])).

cnf(c_1387,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0_49),sK2)
    | ~ m1_subset_1(X0_49,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_683])).

cnf(c_1788,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0_49),sK2) = iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1387])).

cnf(c_2677,plain,
    ( v2_tex_2(k1_tarski(sK0(sK3)),sK2) = iProver_top
    | m1_subset_1(sK0(sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2674,c_1788])).

cnf(c_2694,plain,
    ( v2_tex_2(k1_tarski(sK0(sK3)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2677,c_29,c_30,c_737,c_1420,c_1434,c_1993,c_1999,c_2008,c_2204])).

cnf(c_2835,plain,
    ( v2_tex_2(sK3,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2832,c_2694])).

cnf(c_17,negated_conjecture,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_32,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | v1_zfmisc_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2835,c_2227,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:55:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.13/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/0.99  
% 2.13/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.13/0.99  
% 2.13/0.99  ------  iProver source info
% 2.13/0.99  
% 2.13/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.13/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.13/0.99  git: non_committed_changes: false
% 2.13/0.99  git: last_make_outside_of_git: false
% 2.13/0.99  
% 2.13/0.99  ------ 
% 2.13/0.99  
% 2.13/0.99  ------ Input Options
% 2.13/0.99  
% 2.13/0.99  --out_options                           all
% 2.13/0.99  --tptp_safe_out                         true
% 2.13/0.99  --problem_path                          ""
% 2.13/0.99  --include_path                          ""
% 2.13/0.99  --clausifier                            res/vclausify_rel
% 2.13/0.99  --clausifier_options                    --mode clausify
% 2.13/0.99  --stdin                                 false
% 2.13/0.99  --stats_out                             all
% 2.13/0.99  
% 2.13/0.99  ------ General Options
% 2.13/0.99  
% 2.13/0.99  --fof                                   false
% 2.13/0.99  --time_out_real                         305.
% 2.13/0.99  --time_out_virtual                      -1.
% 2.13/0.99  --symbol_type_check                     false
% 2.13/0.99  --clausify_out                          false
% 2.13/0.99  --sig_cnt_out                           false
% 2.13/0.99  --trig_cnt_out                          false
% 2.13/0.99  --trig_cnt_out_tolerance                1.
% 2.13/0.99  --trig_cnt_out_sk_spl                   false
% 2.13/0.99  --abstr_cl_out                          false
% 2.13/0.99  
% 2.13/0.99  ------ Global Options
% 2.13/0.99  
% 2.13/0.99  --schedule                              default
% 2.13/0.99  --add_important_lit                     false
% 2.13/0.99  --prop_solver_per_cl                    1000
% 2.13/0.99  --min_unsat_core                        false
% 2.13/0.99  --soft_assumptions                      false
% 2.13/0.99  --soft_lemma_size                       3
% 2.13/0.99  --prop_impl_unit_size                   0
% 2.13/0.99  --prop_impl_unit                        []
% 2.13/0.99  --share_sel_clauses                     true
% 2.13/0.99  --reset_solvers                         false
% 2.13/0.99  --bc_imp_inh                            [conj_cone]
% 2.13/0.99  --conj_cone_tolerance                   3.
% 2.13/0.99  --extra_neg_conj                        none
% 2.13/0.99  --large_theory_mode                     true
% 2.13/0.99  --prolific_symb_bound                   200
% 2.13/0.99  --lt_threshold                          2000
% 2.13/0.99  --clause_weak_htbl                      true
% 2.13/0.99  --gc_record_bc_elim                     false
% 2.13/0.99  
% 2.13/0.99  ------ Preprocessing Options
% 2.13/0.99  
% 2.13/0.99  --preprocessing_flag                    true
% 2.13/0.99  --time_out_prep_mult                    0.1
% 2.13/0.99  --splitting_mode                        input
% 2.13/0.99  --splitting_grd                         true
% 2.13/0.99  --splitting_cvd                         false
% 2.13/0.99  --splitting_cvd_svl                     false
% 2.13/0.99  --splitting_nvd                         32
% 2.13/0.99  --sub_typing                            true
% 2.13/0.99  --prep_gs_sim                           true
% 2.13/0.99  --prep_unflatten                        true
% 2.13/0.99  --prep_res_sim                          true
% 2.13/0.99  --prep_upred                            true
% 2.13/0.99  --prep_sem_filter                       exhaustive
% 2.13/0.99  --prep_sem_filter_out                   false
% 2.13/0.99  --pred_elim                             true
% 2.13/0.99  --res_sim_input                         true
% 2.13/0.99  --eq_ax_congr_red                       true
% 2.13/0.99  --pure_diseq_elim                       true
% 2.13/0.99  --brand_transform                       false
% 2.13/0.99  --non_eq_to_eq                          false
% 2.13/0.99  --prep_def_merge                        true
% 2.13/0.99  --prep_def_merge_prop_impl              false
% 2.13/0.99  --prep_def_merge_mbd                    true
% 2.13/0.99  --prep_def_merge_tr_red                 false
% 2.13/0.99  --prep_def_merge_tr_cl                  false
% 2.13/0.99  --smt_preprocessing                     true
% 2.13/0.99  --smt_ac_axioms                         fast
% 2.13/0.99  --preprocessed_out                      false
% 2.13/0.99  --preprocessed_stats                    false
% 2.13/0.99  
% 2.13/0.99  ------ Abstraction refinement Options
% 2.13/0.99  
% 2.13/0.99  --abstr_ref                             []
% 2.13/0.99  --abstr_ref_prep                        false
% 2.13/0.99  --abstr_ref_until_sat                   false
% 2.13/0.99  --abstr_ref_sig_restrict                funpre
% 2.13/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.13/0.99  --abstr_ref_under                       []
% 2.13/0.99  
% 2.13/0.99  ------ SAT Options
% 2.13/0.99  
% 2.13/0.99  --sat_mode                              false
% 2.13/0.99  --sat_fm_restart_options                ""
% 2.13/0.99  --sat_gr_def                            false
% 2.13/0.99  --sat_epr_types                         true
% 2.13/0.99  --sat_non_cyclic_types                  false
% 2.13/0.99  --sat_finite_models                     false
% 2.13/0.99  --sat_fm_lemmas                         false
% 2.13/0.99  --sat_fm_prep                           false
% 2.13/0.99  --sat_fm_uc_incr                        true
% 2.13/0.99  --sat_out_model                         small
% 2.13/0.99  --sat_out_clauses                       false
% 2.13/0.99  
% 2.13/0.99  ------ QBF Options
% 2.13/0.99  
% 2.13/0.99  --qbf_mode                              false
% 2.13/0.99  --qbf_elim_univ                         false
% 2.13/0.99  --qbf_dom_inst                          none
% 2.13/0.99  --qbf_dom_pre_inst                      false
% 2.13/0.99  --qbf_sk_in                             false
% 2.13/0.99  --qbf_pred_elim                         true
% 2.13/0.99  --qbf_split                             512
% 2.13/0.99  
% 2.13/0.99  ------ BMC1 Options
% 2.13/0.99  
% 2.13/0.99  --bmc1_incremental                      false
% 2.13/0.99  --bmc1_axioms                           reachable_all
% 2.13/0.99  --bmc1_min_bound                        0
% 2.13/0.99  --bmc1_max_bound                        -1
% 2.13/0.99  --bmc1_max_bound_default                -1
% 2.13/0.99  --bmc1_symbol_reachability              true
% 2.13/0.99  --bmc1_property_lemmas                  false
% 2.13/0.99  --bmc1_k_induction                      false
% 2.13/0.99  --bmc1_non_equiv_states                 false
% 2.13/0.99  --bmc1_deadlock                         false
% 2.13/0.99  --bmc1_ucm                              false
% 2.13/0.99  --bmc1_add_unsat_core                   none
% 2.13/0.99  --bmc1_unsat_core_children              false
% 2.13/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.13/0.99  --bmc1_out_stat                         full
% 2.13/0.99  --bmc1_ground_init                      false
% 2.13/0.99  --bmc1_pre_inst_next_state              false
% 2.13/0.99  --bmc1_pre_inst_state                   false
% 2.13/0.99  --bmc1_pre_inst_reach_state             false
% 2.13/0.99  --bmc1_out_unsat_core                   false
% 2.13/0.99  --bmc1_aig_witness_out                  false
% 2.13/0.99  --bmc1_verbose                          false
% 2.13/0.99  --bmc1_dump_clauses_tptp                false
% 2.13/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.13/0.99  --bmc1_dump_file                        -
% 2.13/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.13/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.13/0.99  --bmc1_ucm_extend_mode                  1
% 2.13/0.99  --bmc1_ucm_init_mode                    2
% 2.13/0.99  --bmc1_ucm_cone_mode                    none
% 2.13/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.13/0.99  --bmc1_ucm_relax_model                  4
% 2.13/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.13/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.13/0.99  --bmc1_ucm_layered_model                none
% 2.13/0.99  --bmc1_ucm_max_lemma_size               10
% 2.13/0.99  
% 2.13/0.99  ------ AIG Options
% 2.13/0.99  
% 2.13/0.99  --aig_mode                              false
% 2.13/0.99  
% 2.13/0.99  ------ Instantiation Options
% 2.13/0.99  
% 2.13/0.99  --instantiation_flag                    true
% 2.13/0.99  --inst_sos_flag                         false
% 2.13/0.99  --inst_sos_phase                        true
% 2.13/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.13/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.13/0.99  --inst_lit_sel_side                     num_symb
% 2.13/0.99  --inst_solver_per_active                1400
% 2.13/0.99  --inst_solver_calls_frac                1.
% 2.13/0.99  --inst_passive_queue_type               priority_queues
% 2.13/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.13/0.99  --inst_passive_queues_freq              [25;2]
% 2.13/0.99  --inst_dismatching                      true
% 2.13/0.99  --inst_eager_unprocessed_to_passive     true
% 2.13/0.99  --inst_prop_sim_given                   true
% 2.13/0.99  --inst_prop_sim_new                     false
% 2.13/0.99  --inst_subs_new                         false
% 2.13/0.99  --inst_eq_res_simp                      false
% 2.13/0.99  --inst_subs_given                       false
% 2.13/0.99  --inst_orphan_elimination               true
% 2.13/0.99  --inst_learning_loop_flag               true
% 2.13/0.99  --inst_learning_start                   3000
% 2.13/0.99  --inst_learning_factor                  2
% 2.13/0.99  --inst_start_prop_sim_after_learn       3
% 2.13/0.99  --inst_sel_renew                        solver
% 2.13/0.99  --inst_lit_activity_flag                true
% 2.13/0.99  --inst_restr_to_given                   false
% 2.13/0.99  --inst_activity_threshold               500
% 2.13/0.99  --inst_out_proof                        true
% 2.13/0.99  
% 2.13/0.99  ------ Resolution Options
% 2.13/0.99  
% 2.13/0.99  --resolution_flag                       true
% 2.13/0.99  --res_lit_sel                           adaptive
% 2.13/0.99  --res_lit_sel_side                      none
% 2.13/0.99  --res_ordering                          kbo
% 2.13/0.99  --res_to_prop_solver                    active
% 2.13/0.99  --res_prop_simpl_new                    false
% 2.13/0.99  --res_prop_simpl_given                  true
% 2.13/0.99  --res_passive_queue_type                priority_queues
% 2.13/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.13/0.99  --res_passive_queues_freq               [15;5]
% 2.13/0.99  --res_forward_subs                      full
% 2.13/0.99  --res_backward_subs                     full
% 2.13/0.99  --res_forward_subs_resolution           true
% 2.13/0.99  --res_backward_subs_resolution          true
% 2.13/0.99  --res_orphan_elimination                true
% 2.13/0.99  --res_time_limit                        2.
% 2.13/0.99  --res_out_proof                         true
% 2.13/0.99  
% 2.13/0.99  ------ Superposition Options
% 2.13/0.99  
% 2.13/0.99  --superposition_flag                    true
% 2.13/0.99  --sup_passive_queue_type                priority_queues
% 2.13/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.13/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.13/0.99  --demod_completeness_check              fast
% 2.13/0.99  --demod_use_ground                      true
% 2.13/0.99  --sup_to_prop_solver                    passive
% 2.13/0.99  --sup_prop_simpl_new                    true
% 2.13/0.99  --sup_prop_simpl_given                  true
% 2.13/0.99  --sup_fun_splitting                     false
% 2.13/0.99  --sup_smt_interval                      50000
% 2.13/0.99  
% 2.13/0.99  ------ Superposition Simplification Setup
% 2.13/0.99  
% 2.13/0.99  --sup_indices_passive                   []
% 2.13/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.13/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/0.99  --sup_full_bw                           [BwDemod]
% 2.13/0.99  --sup_immed_triv                        [TrivRules]
% 2.13/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.13/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/0.99  --sup_immed_bw_main                     []
% 2.13/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.13/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/0.99  
% 2.13/0.99  ------ Combination Options
% 2.13/0.99  
% 2.13/0.99  --comb_res_mult                         3
% 2.13/0.99  --comb_sup_mult                         2
% 2.13/0.99  --comb_inst_mult                        10
% 2.13/0.99  
% 2.13/0.99  ------ Debug Options
% 2.13/0.99  
% 2.13/0.99  --dbg_backtrace                         false
% 2.13/0.99  --dbg_dump_prop_clauses                 false
% 2.13/0.99  --dbg_dump_prop_clauses_file            -
% 2.13/0.99  --dbg_out_stat                          false
% 2.13/0.99  ------ Parsing...
% 2.13/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.13/0.99  
% 2.13/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.13/0.99  
% 2.13/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.13/0.99  
% 2.13/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.13/0.99  ------ Proving...
% 2.13/0.99  ------ Problem Properties 
% 2.13/0.99  
% 2.13/0.99  
% 2.13/0.99  clauses                                 13
% 2.13/0.99  conjectures                             4
% 2.13/0.99  EPR                                     3
% 2.13/0.99  Horn                                    5
% 2.13/0.99  unary                                   2
% 2.13/0.99  binary                                  3
% 2.13/0.99  lits                                    36
% 2.13/0.99  lits eq                                 4
% 2.13/0.99  fd_pure                                 0
% 2.13/0.99  fd_pseudo                               0
% 2.13/0.99  fd_cond                                 0
% 2.13/0.99  fd_pseudo_cond                          0
% 2.13/0.99  AC symbols                              0
% 2.13/0.99  
% 2.13/0.99  ------ Schedule dynamic 5 is on 
% 2.13/0.99  
% 2.13/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.13/0.99  
% 2.13/0.99  
% 2.13/0.99  ------ 
% 2.13/0.99  Current options:
% 2.13/0.99  ------ 
% 2.13/0.99  
% 2.13/0.99  ------ Input Options
% 2.13/0.99  
% 2.13/0.99  --out_options                           all
% 2.13/0.99  --tptp_safe_out                         true
% 2.13/0.99  --problem_path                          ""
% 2.13/0.99  --include_path                          ""
% 2.13/0.99  --clausifier                            res/vclausify_rel
% 2.13/0.99  --clausifier_options                    --mode clausify
% 2.13/0.99  --stdin                                 false
% 2.13/0.99  --stats_out                             all
% 2.13/0.99  
% 2.13/0.99  ------ General Options
% 2.13/0.99  
% 2.13/0.99  --fof                                   false
% 2.13/0.99  --time_out_real                         305.
% 2.13/0.99  --time_out_virtual                      -1.
% 2.13/0.99  --symbol_type_check                     false
% 2.13/0.99  --clausify_out                          false
% 2.13/0.99  --sig_cnt_out                           false
% 2.13/0.99  --trig_cnt_out                          false
% 2.13/0.99  --trig_cnt_out_tolerance                1.
% 2.13/0.99  --trig_cnt_out_sk_spl                   false
% 2.13/0.99  --abstr_cl_out                          false
% 2.13/0.99  
% 2.13/0.99  ------ Global Options
% 2.13/0.99  
% 2.13/0.99  --schedule                              default
% 2.13/0.99  --add_important_lit                     false
% 2.13/0.99  --prop_solver_per_cl                    1000
% 2.13/0.99  --min_unsat_core                        false
% 2.13/0.99  --soft_assumptions                      false
% 2.13/0.99  --soft_lemma_size                       3
% 2.13/0.99  --prop_impl_unit_size                   0
% 2.13/0.99  --prop_impl_unit                        []
% 2.13/0.99  --share_sel_clauses                     true
% 2.13/0.99  --reset_solvers                         false
% 2.13/0.99  --bc_imp_inh                            [conj_cone]
% 2.13/0.99  --conj_cone_tolerance                   3.
% 2.13/0.99  --extra_neg_conj                        none
% 2.13/0.99  --large_theory_mode                     true
% 2.13/0.99  --prolific_symb_bound                   200
% 2.13/0.99  --lt_threshold                          2000
% 2.13/0.99  --clause_weak_htbl                      true
% 2.13/0.99  --gc_record_bc_elim                     false
% 2.13/0.99  
% 2.13/0.99  ------ Preprocessing Options
% 2.13/0.99  
% 2.13/0.99  --preprocessing_flag                    true
% 2.13/0.99  --time_out_prep_mult                    0.1
% 2.13/0.99  --splitting_mode                        input
% 2.13/0.99  --splitting_grd                         true
% 2.13/0.99  --splitting_cvd                         false
% 2.13/0.99  --splitting_cvd_svl                     false
% 2.13/0.99  --splitting_nvd                         32
% 2.13/0.99  --sub_typing                            true
% 2.13/0.99  --prep_gs_sim                           true
% 2.13/0.99  --prep_unflatten                        true
% 2.13/0.99  --prep_res_sim                          true
% 2.13/0.99  --prep_upred                            true
% 2.13/0.99  --prep_sem_filter                       exhaustive
% 2.13/0.99  --prep_sem_filter_out                   false
% 2.13/0.99  --pred_elim                             true
% 2.13/0.99  --res_sim_input                         true
% 2.13/0.99  --eq_ax_congr_red                       true
% 2.13/0.99  --pure_diseq_elim                       true
% 2.13/0.99  --brand_transform                       false
% 2.13/0.99  --non_eq_to_eq                          false
% 2.13/0.99  --prep_def_merge                        true
% 2.13/0.99  --prep_def_merge_prop_impl              false
% 2.13/0.99  --prep_def_merge_mbd                    true
% 2.13/0.99  --prep_def_merge_tr_red                 false
% 2.13/0.99  --prep_def_merge_tr_cl                  false
% 2.13/0.99  --smt_preprocessing                     true
% 2.13/0.99  --smt_ac_axioms                         fast
% 2.13/0.99  --preprocessed_out                      false
% 2.13/0.99  --preprocessed_stats                    false
% 2.13/0.99  
% 2.13/0.99  ------ Abstraction refinement Options
% 2.13/0.99  
% 2.13/0.99  --abstr_ref                             []
% 2.13/0.99  --abstr_ref_prep                        false
% 2.13/0.99  --abstr_ref_until_sat                   false
% 2.13/0.99  --abstr_ref_sig_restrict                funpre
% 2.13/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.13/0.99  --abstr_ref_under                       []
% 2.13/0.99  
% 2.13/0.99  ------ SAT Options
% 2.13/0.99  
% 2.13/0.99  --sat_mode                              false
% 2.13/0.99  --sat_fm_restart_options                ""
% 2.13/0.99  --sat_gr_def                            false
% 2.13/0.99  --sat_epr_types                         true
% 2.13/0.99  --sat_non_cyclic_types                  false
% 2.13/0.99  --sat_finite_models                     false
% 2.13/0.99  --sat_fm_lemmas                         false
% 2.13/0.99  --sat_fm_prep                           false
% 2.13/0.99  --sat_fm_uc_incr                        true
% 2.13/0.99  --sat_out_model                         small
% 2.13/0.99  --sat_out_clauses                       false
% 2.13/0.99  
% 2.13/0.99  ------ QBF Options
% 2.13/0.99  
% 2.13/0.99  --qbf_mode                              false
% 2.13/0.99  --qbf_elim_univ                         false
% 2.13/0.99  --qbf_dom_inst                          none
% 2.13/0.99  --qbf_dom_pre_inst                      false
% 2.13/0.99  --qbf_sk_in                             false
% 2.13/0.99  --qbf_pred_elim                         true
% 2.13/0.99  --qbf_split                             512
% 2.13/0.99  
% 2.13/0.99  ------ BMC1 Options
% 2.13/0.99  
% 2.13/0.99  --bmc1_incremental                      false
% 2.13/0.99  --bmc1_axioms                           reachable_all
% 2.13/0.99  --bmc1_min_bound                        0
% 2.13/0.99  --bmc1_max_bound                        -1
% 2.13/0.99  --bmc1_max_bound_default                -1
% 2.13/0.99  --bmc1_symbol_reachability              true
% 2.13/0.99  --bmc1_property_lemmas                  false
% 2.13/0.99  --bmc1_k_induction                      false
% 2.13/0.99  --bmc1_non_equiv_states                 false
% 2.13/0.99  --bmc1_deadlock                         false
% 2.13/0.99  --bmc1_ucm                              false
% 2.13/0.99  --bmc1_add_unsat_core                   none
% 2.13/0.99  --bmc1_unsat_core_children              false
% 2.13/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.13/0.99  --bmc1_out_stat                         full
% 2.13/0.99  --bmc1_ground_init                      false
% 2.13/0.99  --bmc1_pre_inst_next_state              false
% 2.13/0.99  --bmc1_pre_inst_state                   false
% 2.13/0.99  --bmc1_pre_inst_reach_state             false
% 2.13/0.99  --bmc1_out_unsat_core                   false
% 2.13/0.99  --bmc1_aig_witness_out                  false
% 2.13/0.99  --bmc1_verbose                          false
% 2.13/0.99  --bmc1_dump_clauses_tptp                false
% 2.13/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.13/0.99  --bmc1_dump_file                        -
% 2.13/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.13/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.13/0.99  --bmc1_ucm_extend_mode                  1
% 2.13/0.99  --bmc1_ucm_init_mode                    2
% 2.13/0.99  --bmc1_ucm_cone_mode                    none
% 2.13/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.13/0.99  --bmc1_ucm_relax_model                  4
% 2.13/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.13/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.13/0.99  --bmc1_ucm_layered_model                none
% 2.13/0.99  --bmc1_ucm_max_lemma_size               10
% 2.13/0.99  
% 2.13/0.99  ------ AIG Options
% 2.13/0.99  
% 2.13/0.99  --aig_mode                              false
% 2.13/0.99  
% 2.13/0.99  ------ Instantiation Options
% 2.13/0.99  
% 2.13/0.99  --instantiation_flag                    true
% 2.13/0.99  --inst_sos_flag                         false
% 2.13/0.99  --inst_sos_phase                        true
% 2.13/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.13/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.13/0.99  --inst_lit_sel_side                     none
% 2.13/0.99  --inst_solver_per_active                1400
% 2.13/0.99  --inst_solver_calls_frac                1.
% 2.13/0.99  --inst_passive_queue_type               priority_queues
% 2.13/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.13/0.99  --inst_passive_queues_freq              [25;2]
% 2.13/0.99  --inst_dismatching                      true
% 2.13/0.99  --inst_eager_unprocessed_to_passive     true
% 2.13/0.99  --inst_prop_sim_given                   true
% 2.13/0.99  --inst_prop_sim_new                     false
% 2.13/0.99  --inst_subs_new                         false
% 2.13/0.99  --inst_eq_res_simp                      false
% 2.13/0.99  --inst_subs_given                       false
% 2.13/0.99  --inst_orphan_elimination               true
% 2.13/0.99  --inst_learning_loop_flag               true
% 2.13/0.99  --inst_learning_start                   3000
% 2.13/0.99  --inst_learning_factor                  2
% 2.13/0.99  --inst_start_prop_sim_after_learn       3
% 2.13/0.99  --inst_sel_renew                        solver
% 2.13/0.99  --inst_lit_activity_flag                true
% 2.13/0.99  --inst_restr_to_given                   false
% 2.13/0.99  --inst_activity_threshold               500
% 2.13/0.99  --inst_out_proof                        true
% 2.13/0.99  
% 2.13/0.99  ------ Resolution Options
% 2.13/0.99  
% 2.13/0.99  --resolution_flag                       false
% 2.13/0.99  --res_lit_sel                           adaptive
% 2.13/0.99  --res_lit_sel_side                      none
% 2.13/0.99  --res_ordering                          kbo
% 2.13/0.99  --res_to_prop_solver                    active
% 2.13/0.99  --res_prop_simpl_new                    false
% 2.13/0.99  --res_prop_simpl_given                  true
% 2.13/0.99  --res_passive_queue_type                priority_queues
% 2.13/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.13/0.99  --res_passive_queues_freq               [15;5]
% 2.13/0.99  --res_forward_subs                      full
% 2.13/0.99  --res_backward_subs                     full
% 2.13/0.99  --res_forward_subs_resolution           true
% 2.13/0.99  --res_backward_subs_resolution          true
% 2.13/0.99  --res_orphan_elimination                true
% 2.13/0.99  --res_time_limit                        2.
% 2.13/0.99  --res_out_proof                         true
% 2.13/0.99  
% 2.13/0.99  ------ Superposition Options
% 2.13/0.99  
% 2.13/0.99  --superposition_flag                    true
% 2.13/0.99  --sup_passive_queue_type                priority_queues
% 2.13/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.13/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.13/0.99  --demod_completeness_check              fast
% 2.13/0.99  --demod_use_ground                      true
% 2.13/0.99  --sup_to_prop_solver                    passive
% 2.13/0.99  --sup_prop_simpl_new                    true
% 2.13/0.99  --sup_prop_simpl_given                  true
% 2.13/0.99  --sup_fun_splitting                     false
% 2.13/0.99  --sup_smt_interval                      50000
% 2.13/0.99  
% 2.13/0.99  ------ Superposition Simplification Setup
% 2.13/0.99  
% 2.13/0.99  --sup_indices_passive                   []
% 2.13/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.13/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/0.99  --sup_full_bw                           [BwDemod]
% 2.13/0.99  --sup_immed_triv                        [TrivRules]
% 2.13/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.13/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/0.99  --sup_immed_bw_main                     []
% 2.13/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.13/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/0.99  
% 2.13/0.99  ------ Combination Options
% 2.13/0.99  
% 2.13/0.99  --comb_res_mult                         3
% 2.13/0.99  --comb_sup_mult                         2
% 2.13/0.99  --comb_inst_mult                        10
% 2.13/0.99  
% 2.13/0.99  ------ Debug Options
% 2.13/0.99  
% 2.13/0.99  --dbg_backtrace                         false
% 2.13/0.99  --dbg_dump_prop_clauses                 false
% 2.13/0.99  --dbg_dump_prop_clauses_file            -
% 2.13/0.99  --dbg_out_stat                          false
% 2.13/0.99  
% 2.13/0.99  
% 2.13/0.99  
% 2.13/0.99  
% 2.13/0.99  ------ Proving...
% 2.13/0.99  
% 2.13/0.99  
% 2.13/0.99  % SZS status Theorem for theBenchmark.p
% 2.13/0.99  
% 2.13/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.13/0.99  
% 2.13/0.99  fof(f12,conjecture,(
% 2.13/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 2.13/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f13,negated_conjecture,(
% 2.13/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 2.13/0.99    inference(negated_conjecture,[],[f12])).
% 2.13/0.99  
% 2.13/0.99  fof(f33,plain,(
% 2.13/0.99    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.13/0.99    inference(ennf_transformation,[],[f13])).
% 2.13/0.99  
% 2.13/0.99  fof(f34,plain,(
% 2.13/0.99    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.13/0.99    inference(flattening,[],[f33])).
% 2.13/0.99  
% 2.13/0.99  fof(f41,plain,(
% 2.13/0.99    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.13/0.99    inference(nnf_transformation,[],[f34])).
% 2.13/0.99  
% 2.13/0.99  fof(f42,plain,(
% 2.13/0.99    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.13/0.99    inference(flattening,[],[f41])).
% 2.13/0.99  
% 2.13/0.99  fof(f44,plain,(
% 2.13/0.99    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK3) | ~v2_tex_2(sK3,X0)) & (v1_zfmisc_1(sK3) | v2_tex_2(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK3))) )),
% 2.13/0.99    introduced(choice_axiom,[])).
% 2.13/0.99  
% 2.13/0.99  fof(f43,plain,(
% 2.13/0.99    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK2)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.13/0.99    introduced(choice_axiom,[])).
% 2.13/0.99  
% 2.13/0.99  fof(f45,plain,(
% 2.13/0.99    ((~v1_zfmisc_1(sK3) | ~v2_tex_2(sK3,sK2)) & (v1_zfmisc_1(sK3) | v2_tex_2(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.13/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f42,f44,f43])).
% 2.13/0.99  
% 2.13/0.99  fof(f69,plain,(
% 2.13/0.99    v1_zfmisc_1(sK3) | v2_tex_2(sK3,sK2)),
% 2.13/0.99    inference(cnf_transformation,[],[f45])).
% 2.13/0.99  
% 2.13/0.99  fof(f68,plain,(
% 2.13/0.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 2.13/0.99    inference(cnf_transformation,[],[f45])).
% 2.13/0.99  
% 2.13/0.99  fof(f10,axiom,(
% 2.13/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 2.13/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f14,plain,(
% 2.13/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 2.13/0.99    inference(pure_predicate_removal,[],[f10])).
% 2.13/0.99  
% 2.13/0.99  fof(f29,plain,(
% 2.13/0.99    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.13/0.99    inference(ennf_transformation,[],[f14])).
% 2.13/0.99  
% 2.13/0.99  fof(f30,plain,(
% 2.13/0.99    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/0.99    inference(flattening,[],[f29])).
% 2.13/0.99  
% 2.13/0.99  fof(f39,plain,(
% 2.13/0.99    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & v1_tdlat_3(sK1(X0,X1)) & ~v2_struct_0(sK1(X0,X1))))),
% 2.13/0.99    introduced(choice_axiom,[])).
% 2.13/0.99  
% 2.13/0.99  fof(f40,plain,(
% 2.13/0.99    ! [X0] : (! [X1] : ((u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & v1_tdlat_3(sK1(X0,X1)) & ~v2_struct_0(sK1(X0,X1))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f39])).
% 2.13/0.99  
% 2.13/0.99  fof(f61,plain,(
% 2.13/0.99    ( ! [X0,X1] : (u1_struct_0(sK1(X0,X1)) = X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/0.99    inference(cnf_transformation,[],[f40])).
% 2.13/0.99  
% 2.13/0.99  fof(f64,plain,(
% 2.13/0.99    v2_pre_topc(sK2)),
% 2.13/0.99    inference(cnf_transformation,[],[f45])).
% 2.13/0.99  
% 2.13/0.99  fof(f63,plain,(
% 2.13/0.99    ~v2_struct_0(sK2)),
% 2.13/0.99    inference(cnf_transformation,[],[f45])).
% 2.13/0.99  
% 2.13/0.99  fof(f66,plain,(
% 2.13/0.99    l1_pre_topc(sK2)),
% 2.13/0.99    inference(cnf_transformation,[],[f45])).
% 2.13/0.99  
% 2.13/0.99  fof(f67,plain,(
% 2.13/0.99    ~v1_xboole_0(sK3)),
% 2.13/0.99    inference(cnf_transformation,[],[f45])).
% 2.13/0.99  
% 2.13/0.99  fof(f59,plain,(
% 2.13/0.99    ( ! [X0,X1] : (v1_tdlat_3(sK1(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/0.99    inference(cnf_transformation,[],[f40])).
% 2.13/0.99  
% 2.13/0.99  fof(f58,plain,(
% 2.13/0.99    ( ! [X0,X1] : (~v2_struct_0(sK1(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/0.99    inference(cnf_transformation,[],[f40])).
% 2.13/0.99  
% 2.13/0.99  fof(f5,axiom,(
% 2.13/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.13/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f21,plain,(
% 2.13/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.13/0.99    inference(ennf_transformation,[],[f5])).
% 2.13/0.99  
% 2.13/0.99  fof(f50,plain,(
% 2.13/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.13/0.99    inference(cnf_transformation,[],[f21])).
% 2.13/0.99  
% 2.13/0.99  fof(f60,plain,(
% 2.13/0.99    ( ! [X0,X1] : (m1_pre_topc(sK1(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/0.99    inference(cnf_transformation,[],[f40])).
% 2.13/0.99  
% 2.13/0.99  fof(f8,axiom,(
% 2.13/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((v1_tdlat_3(X1) & ~v2_struct_0(X1)) => (v7_struct_0(X1) & ~v2_struct_0(X1)))))),
% 2.13/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f26,plain,(
% 2.13/0.99    ! [X0] : (! [X1] : (((v7_struct_0(X1) & ~v2_struct_0(X1)) | (~v1_tdlat_3(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.13/0.99    inference(ennf_transformation,[],[f8])).
% 2.13/0.99  
% 2.13/0.99  fof(f27,plain,(
% 2.13/0.99    ! [X0] : (! [X1] : ((v7_struct_0(X1) & ~v2_struct_0(X1)) | ~v1_tdlat_3(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/0.99    inference(flattening,[],[f26])).
% 2.13/0.99  
% 2.13/0.99  fof(f54,plain,(
% 2.13/0.99    ( ! [X0,X1] : (v7_struct_0(X1) | ~v1_tdlat_3(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/0.99    inference(cnf_transformation,[],[f27])).
% 2.13/0.99  
% 2.13/0.99  fof(f65,plain,(
% 2.13/0.99    v2_tdlat_3(sK2)),
% 2.13/0.99    inference(cnf_transformation,[],[f45])).
% 2.13/0.99  
% 2.13/0.99  fof(f4,axiom,(
% 2.13/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.13/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f20,plain,(
% 2.13/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.13/0.99    inference(ennf_transformation,[],[f4])).
% 2.13/0.99  
% 2.13/0.99  fof(f49,plain,(
% 2.13/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.13/0.99    inference(cnf_transformation,[],[f20])).
% 2.13/0.99  
% 2.13/0.99  fof(f6,axiom,(
% 2.13/0.99    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 2.13/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f22,plain,(
% 2.13/0.99    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 2.13/0.99    inference(ennf_transformation,[],[f6])).
% 2.13/0.99  
% 2.13/0.99  fof(f23,plain,(
% 2.13/0.99    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 2.13/0.99    inference(flattening,[],[f22])).
% 2.13/0.99  
% 2.13/0.99  fof(f51,plain,(
% 2.13/0.99    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 2.13/0.99    inference(cnf_transformation,[],[f23])).
% 2.13/0.99  
% 2.13/0.99  fof(f9,axiom,(
% 2.13/0.99    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 2.13/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f28,plain,(
% 2.13/0.99    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 2.13/0.99    inference(ennf_transformation,[],[f9])).
% 2.13/0.99  
% 2.13/0.99  fof(f35,plain,(
% 2.13/0.99    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.13/0.99    inference(nnf_transformation,[],[f28])).
% 2.13/0.99  
% 2.13/0.99  fof(f36,plain,(
% 2.13/0.99    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.13/0.99    inference(rectify,[],[f35])).
% 2.13/0.99  
% 2.13/0.99  fof(f37,plain,(
% 2.13/0.99    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK0(X0)) = X0 & m1_subset_1(sK0(X0),X0)))),
% 2.13/0.99    introduced(choice_axiom,[])).
% 2.13/0.99  
% 2.13/0.99  fof(f38,plain,(
% 2.13/0.99    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK0(X0)) = X0 & m1_subset_1(sK0(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.13/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 2.13/0.99  
% 2.13/0.99  fof(f55,plain,(
% 2.13/0.99    ( ! [X0] : (m1_subset_1(sK0(X0),X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 2.13/0.99    inference(cnf_transformation,[],[f38])).
% 2.13/0.99  
% 2.13/0.99  fof(f7,axiom,(
% 2.13/0.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 2.13/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f24,plain,(
% 2.13/0.99    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.13/0.99    inference(ennf_transformation,[],[f7])).
% 2.13/0.99  
% 2.13/0.99  fof(f25,plain,(
% 2.13/0.99    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.13/0.99    inference(flattening,[],[f24])).
% 2.13/0.99  
% 2.13/0.99  fof(f52,plain,(
% 2.13/0.99    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.13/0.99    inference(cnf_transformation,[],[f25])).
% 2.13/0.99  
% 2.13/0.99  fof(f56,plain,(
% 2.13/0.99    ( ! [X0] : (k6_domain_1(X0,sK0(X0)) = X0 | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 2.13/0.99    inference(cnf_transformation,[],[f38])).
% 2.13/0.99  
% 2.13/0.99  fof(f2,axiom,(
% 2.13/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.13/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f16,plain,(
% 2.13/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.13/0.99    inference(ennf_transformation,[],[f2])).
% 2.13/0.99  
% 2.13/0.99  fof(f17,plain,(
% 2.13/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.13/0.99    inference(flattening,[],[f16])).
% 2.13/0.99  
% 2.13/0.99  fof(f47,plain,(
% 2.13/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.13/0.99    inference(cnf_transformation,[],[f17])).
% 2.13/0.99  
% 2.13/0.99  fof(f3,axiom,(
% 2.13/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.13/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f18,plain,(
% 2.13/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.13/0.99    inference(ennf_transformation,[],[f3])).
% 2.13/0.99  
% 2.13/0.99  fof(f19,plain,(
% 2.13/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.13/0.99    inference(flattening,[],[f18])).
% 2.13/0.99  
% 2.13/0.99  fof(f48,plain,(
% 2.13/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.13/0.99    inference(cnf_transformation,[],[f19])).
% 2.13/0.99  
% 2.13/0.99  fof(f1,axiom,(
% 2.13/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.13/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f15,plain,(
% 2.13/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.13/0.99    inference(ennf_transformation,[],[f1])).
% 2.13/0.99  
% 2.13/0.99  fof(f46,plain,(
% 2.13/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.13/0.99    inference(cnf_transformation,[],[f15])).
% 2.13/0.99  
% 2.13/0.99  fof(f11,axiom,(
% 2.13/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 2.13/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f31,plain,(
% 2.13/0.99    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.13/0.99    inference(ennf_transformation,[],[f11])).
% 2.13/0.99  
% 2.13/0.99  fof(f32,plain,(
% 2.13/0.99    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/0.99    inference(flattening,[],[f31])).
% 2.13/0.99  
% 2.13/0.99  fof(f62,plain,(
% 2.13/0.99    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/0.99    inference(cnf_transformation,[],[f32])).
% 2.13/0.99  
% 2.13/0.99  fof(f70,plain,(
% 2.13/0.99    ~v1_zfmisc_1(sK3) | ~v2_tex_2(sK3,sK2)),
% 2.13/0.99    inference(cnf_transformation,[],[f45])).
% 2.13/0.99  
% 2.13/0.99  cnf(c_18,negated_conjecture,
% 2.13/0.99      ( v2_tex_2(sK3,sK2) | v1_zfmisc_1(sK3) ),
% 2.13/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1392,negated_conjecture,
% 2.13/0.99      ( v2_tex_2(sK3,sK2) | v1_zfmisc_1(sK3) ),
% 2.13/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1783,plain,
% 2.13/0.99      ( v2_tex_2(sK3,sK2) = iProver_top
% 2.13/0.99      | v1_zfmisc_1(sK3) = iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_1392]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_19,negated_conjecture,
% 2.13/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.13/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1391,negated_conjecture,
% 2.13/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.13/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1784,plain,
% 2.13/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_1391]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_12,plain,
% 2.13/0.99      ( ~ v2_tex_2(X0,X1)
% 2.13/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/0.99      | ~ v2_pre_topc(X1)
% 2.13/0.99      | v2_struct_0(X1)
% 2.13/0.99      | ~ l1_pre_topc(X1)
% 2.13/0.99      | v1_xboole_0(X0)
% 2.13/0.99      | u1_struct_0(sK1(X1,X0)) = X0 ),
% 2.13/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_23,negated_conjecture,
% 2.13/0.99      ( v2_pre_topc(sK2) ),
% 2.13/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_654,plain,
% 2.13/0.99      ( ~ v2_tex_2(X0,X1)
% 2.13/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/0.99      | v2_struct_0(X1)
% 2.13/0.99      | ~ l1_pre_topc(X1)
% 2.13/0.99      | v1_xboole_0(X0)
% 2.13/0.99      | u1_struct_0(sK1(X1,X0)) = X0
% 2.13/0.99      | sK2 != X1 ),
% 2.13/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_23]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_655,plain,
% 2.13/0.99      ( ~ v2_tex_2(X0,sK2)
% 2.13/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.13/0.99      | v2_struct_0(sK2)
% 2.13/0.99      | ~ l1_pre_topc(sK2)
% 2.13/0.99      | v1_xboole_0(X0)
% 2.13/0.99      | u1_struct_0(sK1(sK2,X0)) = X0 ),
% 2.13/0.99      inference(unflattening,[status(thm)],[c_654]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_24,negated_conjecture,
% 2.13/0.99      ( ~ v2_struct_0(sK2) ),
% 2.13/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_21,negated_conjecture,
% 2.13/0.99      ( l1_pre_topc(sK2) ),
% 2.13/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_659,plain,
% 2.13/0.99      ( ~ v2_tex_2(X0,sK2)
% 2.13/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.13/0.99      | v1_xboole_0(X0)
% 2.13/0.99      | u1_struct_0(sK1(sK2,X0)) = X0 ),
% 2.13/0.99      inference(global_propositional_subsumption,
% 2.13/0.99                [status(thm)],
% 2.13/0.99                [c_655,c_24,c_21]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1388,plain,
% 2.13/0.99      ( ~ v2_tex_2(X0_49,sK2)
% 2.13/0.99      | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.13/0.99      | v1_xboole_0(X0_49)
% 2.13/0.99      | u1_struct_0(sK1(sK2,X0_49)) = X0_49 ),
% 2.13/0.99      inference(subtyping,[status(esa)],[c_659]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1787,plain,
% 2.13/0.99      ( u1_struct_0(sK1(sK2,X0_49)) = X0_49
% 2.13/0.99      | v2_tex_2(X0_49,sK2) != iProver_top
% 2.13/0.99      | m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.13/0.99      | v1_xboole_0(X0_49) = iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_1388]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1975,plain,
% 2.13/0.99      ( u1_struct_0(sK1(sK2,sK3)) = sK3
% 2.13/0.99      | v2_tex_2(sK3,sK2) != iProver_top
% 2.13/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 2.13/0.99      inference(superposition,[status(thm)],[c_1784,c_1787]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_20,negated_conjecture,
% 2.13/0.99      ( ~ v1_xboole_0(sK3) ),
% 2.13/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_29,plain,
% 2.13/0.99      ( v1_xboole_0(sK3) != iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2002,plain,
% 2.13/0.99      ( v2_tex_2(sK3,sK2) != iProver_top
% 2.13/0.99      | u1_struct_0(sK1(sK2,sK3)) = sK3 ),
% 2.13/0.99      inference(global_propositional_subsumption,
% 2.13/0.99                [status(thm)],
% 2.13/0.99                [c_1975,c_29]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2003,plain,
% 2.13/0.99      ( u1_struct_0(sK1(sK2,sK3)) = sK3
% 2.13/0.99      | v2_tex_2(sK3,sK2) != iProver_top ),
% 2.13/0.99      inference(renaming,[status(thm)],[c_2002]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2008,plain,
% 2.13/0.99      ( u1_struct_0(sK1(sK2,sK3)) = sK3
% 2.13/0.99      | v1_zfmisc_1(sK3) = iProver_top ),
% 2.13/0.99      inference(superposition,[status(thm)],[c_1783,c_2003]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_181,plain,
% 2.13/0.99      ( v1_zfmisc_1(sK3) | v2_tex_2(sK3,sK2) ),
% 2.13/0.99      inference(prop_impl,[status(thm)],[c_18]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_182,plain,
% 2.13/0.99      ( v2_tex_2(sK3,sK2) | v1_zfmisc_1(sK3) ),
% 2.13/0.99      inference(renaming,[status(thm)],[c_181]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_14,plain,
% 2.13/0.99      ( ~ v2_tex_2(X0,X1)
% 2.13/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/0.99      | ~ v2_pre_topc(X1)
% 2.13/0.99      | v2_struct_0(X1)
% 2.13/0.99      | v1_tdlat_3(sK1(X1,X0))
% 2.13/0.99      | ~ l1_pre_topc(X1)
% 2.13/0.99      | v1_xboole_0(X0) ),
% 2.13/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_630,plain,
% 2.13/0.99      ( ~ v2_tex_2(X0,X1)
% 2.13/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/0.99      | v2_struct_0(X1)
% 2.13/0.99      | v1_tdlat_3(sK1(X1,X0))
% 2.13/0.99      | ~ l1_pre_topc(X1)
% 2.13/0.99      | v1_xboole_0(X0)
% 2.13/0.99      | sK2 != X1 ),
% 2.13/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_631,plain,
% 2.13/0.99      ( ~ v2_tex_2(X0,sK2)
% 2.13/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.13/0.99      | v2_struct_0(sK2)
% 2.13/0.99      | v1_tdlat_3(sK1(sK2,X0))
% 2.13/0.99      | ~ l1_pre_topc(sK2)
% 2.13/0.99      | v1_xboole_0(X0) ),
% 2.13/0.99      inference(unflattening,[status(thm)],[c_630]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_635,plain,
% 2.13/0.99      ( v1_tdlat_3(sK1(sK2,X0))
% 2.13/0.99      | ~ v2_tex_2(X0,sK2)
% 2.13/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.13/0.99      | v1_xboole_0(X0) ),
% 2.13/0.99      inference(global_propositional_subsumption,
% 2.13/0.99                [status(thm)],
% 2.13/0.99                [c_631,c_24,c_21]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_636,plain,
% 2.13/0.99      ( ~ v2_tex_2(X0,sK2)
% 2.13/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.13/0.99      | v1_tdlat_3(sK1(sK2,X0))
% 2.13/0.99      | v1_xboole_0(X0) ),
% 2.13/0.99      inference(renaming,[status(thm)],[c_635]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_15,plain,
% 2.13/0.99      ( ~ v2_tex_2(X0,X1)
% 2.13/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/0.99      | ~ v2_pre_topc(X1)
% 2.13/0.99      | v2_struct_0(X1)
% 2.13/0.99      | ~ v2_struct_0(sK1(X1,X0))
% 2.13/0.99      | ~ l1_pre_topc(X1)
% 2.13/0.99      | v1_xboole_0(X0) ),
% 2.13/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_606,plain,
% 2.13/0.99      ( ~ v2_tex_2(X0,X1)
% 2.13/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/0.99      | v2_struct_0(X1)
% 2.13/0.99      | ~ v2_struct_0(sK1(X1,X0))
% 2.13/0.99      | ~ l1_pre_topc(X1)
% 2.13/0.99      | v1_xboole_0(X0)
% 2.13/0.99      | sK2 != X1 ),
% 2.13/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_23]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_607,plain,
% 2.13/0.99      ( ~ v2_tex_2(X0,sK2)
% 2.13/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.13/0.99      | ~ v2_struct_0(sK1(sK2,X0))
% 2.13/0.99      | v2_struct_0(sK2)
% 2.13/0.99      | ~ l1_pre_topc(sK2)
% 2.13/0.99      | v1_xboole_0(X0) ),
% 2.13/0.99      inference(unflattening,[status(thm)],[c_606]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_611,plain,
% 2.13/0.99      ( ~ v2_tex_2(X0,sK2)
% 2.13/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.13/0.99      | ~ v2_struct_0(sK1(sK2,X0))
% 2.13/0.99      | v1_xboole_0(X0) ),
% 2.13/0.99      inference(global_propositional_subsumption,
% 2.13/0.99                [status(thm)],
% 2.13/0.99                [c_607,c_24,c_21]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_4,plain,
% 2.13/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.13/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_13,plain,
% 2.13/0.99      ( ~ v2_tex_2(X0,X1)
% 2.13/0.99      | m1_pre_topc(sK1(X1,X0),X1)
% 2.13/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/0.99      | ~ v2_pre_topc(X1)
% 2.13/0.99      | v2_struct_0(X1)
% 2.13/0.99      | ~ l1_pre_topc(X1)
% 2.13/0.99      | v1_xboole_0(X0) ),
% 2.13/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_462,plain,
% 2.13/0.99      ( ~ v2_tex_2(X0,X1)
% 2.13/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/0.99      | ~ v2_pre_topc(X1)
% 2.13/0.99      | v2_struct_0(X1)
% 2.13/0.99      | ~ l1_pre_topc(X2)
% 2.13/0.99      | ~ l1_pre_topc(X1)
% 2.13/0.99      | l1_pre_topc(X3)
% 2.13/0.99      | v1_xboole_0(X0)
% 2.13/0.99      | X1 != X2
% 2.13/0.99      | sK1(X1,X0) != X3 ),
% 2.13/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_13]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_463,plain,
% 2.13/0.99      ( ~ v2_tex_2(X0,X1)
% 2.13/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/0.99      | ~ v2_pre_topc(X1)
% 2.13/0.99      | v2_struct_0(X1)
% 2.13/0.99      | ~ l1_pre_topc(X1)
% 2.13/0.99      | l1_pre_topc(sK1(X1,X0))
% 2.13/0.99      | v1_xboole_0(X0) ),
% 2.13/0.99      inference(unflattening,[status(thm)],[c_462]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_582,plain,
% 2.13/0.99      ( ~ v2_tex_2(X0,X1)
% 2.13/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/0.99      | v2_struct_0(X1)
% 2.13/0.99      | ~ l1_pre_topc(X1)
% 2.13/0.99      | l1_pre_topc(sK1(X1,X0))
% 2.13/0.99      | v1_xboole_0(X0)
% 2.13/0.99      | sK2 != X1 ),
% 2.13/0.99      inference(resolution_lifted,[status(thm)],[c_463,c_23]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_583,plain,
% 2.13/0.99      ( ~ v2_tex_2(X0,sK2)
% 2.13/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.13/0.99      | v2_struct_0(sK2)
% 2.13/0.99      | l1_pre_topc(sK1(sK2,X0))
% 2.13/0.99      | ~ l1_pre_topc(sK2)
% 2.13/0.99      | v1_xboole_0(X0) ),
% 2.13/0.99      inference(unflattening,[status(thm)],[c_582]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_587,plain,
% 2.13/0.99      ( l1_pre_topc(sK1(sK2,X0))
% 2.13/0.99      | ~ v2_tex_2(X0,sK2)
% 2.13/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.13/0.99      | v1_xboole_0(X0) ),
% 2.13/0.99      inference(global_propositional_subsumption,
% 2.13/0.99                [status(thm)],
% 2.13/0.99                [c_583,c_24,c_21]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_588,plain,
% 2.13/0.99      ( ~ v2_tex_2(X0,sK2)
% 2.13/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.13/0.99      | l1_pre_topc(sK1(sK2,X0))
% 2.13/0.99      | v1_xboole_0(X0) ),
% 2.13/0.99      inference(renaming,[status(thm)],[c_587]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_7,plain,
% 2.13/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.13/0.99      | ~ v2_pre_topc(X1)
% 2.13/0.99      | ~ v2_tdlat_3(X1)
% 2.13/0.99      | v2_struct_0(X1)
% 2.13/0.99      | v2_struct_0(X0)
% 2.13/0.99      | ~ v1_tdlat_3(X0)
% 2.13/0.99      | v7_struct_0(X0)
% 2.13/0.99      | ~ l1_pre_topc(X1) ),
% 2.13/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_22,negated_conjecture,
% 2.13/0.99      ( v2_tdlat_3(sK2) ),
% 2.13/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_359,plain,
% 2.13/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.13/0.99      | ~ v2_pre_topc(X1)
% 2.13/0.99      | v2_struct_0(X1)
% 2.13/0.99      | v2_struct_0(X0)
% 2.13/0.99      | ~ v1_tdlat_3(X0)
% 2.13/0.99      | v7_struct_0(X0)
% 2.13/0.99      | ~ l1_pre_topc(X1)
% 2.13/0.99      | sK2 != X1 ),
% 2.13/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_22]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_360,plain,
% 2.13/0.99      ( ~ m1_pre_topc(X0,sK2)
% 2.13/0.99      | ~ v2_pre_topc(sK2)
% 2.13/0.99      | v2_struct_0(X0)
% 2.13/0.99      | v2_struct_0(sK2)
% 2.13/0.99      | ~ v1_tdlat_3(X0)
% 2.13/0.99      | v7_struct_0(X0)
% 2.13/0.99      | ~ l1_pre_topc(sK2) ),
% 2.13/0.99      inference(unflattening,[status(thm)],[c_359]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_364,plain,
% 2.13/0.99      ( v7_struct_0(X0)
% 2.13/0.99      | ~ v1_tdlat_3(X0)
% 2.13/0.99      | ~ m1_pre_topc(X0,sK2)
% 2.13/0.99      | v2_struct_0(X0) ),
% 2.13/0.99      inference(global_propositional_subsumption,
% 2.13/0.99                [status(thm)],
% 2.13/0.99                [c_360,c_24,c_23,c_21]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_365,plain,
% 2.13/0.99      ( ~ m1_pre_topc(X0,sK2)
% 2.13/0.99      | v2_struct_0(X0)
% 2.13/0.99      | ~ v1_tdlat_3(X0)
% 2.13/0.99      | v7_struct_0(X0) ),
% 2.13/0.99      inference(renaming,[status(thm)],[c_364]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_3,plain,
% 2.13/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.13/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_5,plain,
% 2.13/0.99      ( ~ v7_struct_0(X0)
% 2.13/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 2.13/0.99      | ~ l1_struct_0(X0) ),
% 2.13/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_321,plain,
% 2.13/0.99      ( ~ v7_struct_0(X0)
% 2.13/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 2.13/0.99      | ~ l1_pre_topc(X0) ),
% 2.13/0.99      inference(resolution,[status(thm)],[c_3,c_5]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_388,plain,
% 2.13/0.99      ( ~ m1_pre_topc(X0,sK2)
% 2.13/0.99      | v2_struct_0(X0)
% 2.13/0.99      | ~ v1_tdlat_3(X0)
% 2.13/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 2.13/0.99      | ~ l1_pre_topc(X0) ),
% 2.13/0.99      inference(resolution,[status(thm)],[c_365,c_321]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_489,plain,
% 2.13/0.99      ( ~ v2_tex_2(X0,X1)
% 2.13/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/0.99      | ~ v2_pre_topc(X1)
% 2.13/0.99      | v2_struct_0(X1)
% 2.13/0.99      | v2_struct_0(X2)
% 2.13/0.99      | ~ v1_tdlat_3(X2)
% 2.13/0.99      | v1_zfmisc_1(u1_struct_0(X2))
% 2.13/0.99      | ~ l1_pre_topc(X1)
% 2.13/0.99      | ~ l1_pre_topc(X2)
% 2.13/0.99      | v1_xboole_0(X0)
% 2.13/0.99      | sK1(X1,X0) != X2
% 2.13/0.99      | sK2 != X1 ),
% 2.13/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_388]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_490,plain,
% 2.13/0.99      ( ~ v2_tex_2(X0,sK2)
% 2.13/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.13/0.99      | ~ v2_pre_topc(sK2)
% 2.13/0.99      | v2_struct_0(sK1(sK2,X0))
% 2.13/0.99      | v2_struct_0(sK2)
% 2.13/0.99      | ~ v1_tdlat_3(sK1(sK2,X0))
% 2.13/0.99      | v1_zfmisc_1(u1_struct_0(sK1(sK2,X0)))
% 2.13/0.99      | ~ l1_pre_topc(sK1(sK2,X0))
% 2.13/0.99      | ~ l1_pre_topc(sK2)
% 2.13/0.99      | v1_xboole_0(X0) ),
% 2.13/0.99      inference(unflattening,[status(thm)],[c_489]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_494,plain,
% 2.13/0.99      ( ~ l1_pre_topc(sK1(sK2,X0))
% 2.13/0.99      | v1_zfmisc_1(u1_struct_0(sK1(sK2,X0)))
% 2.13/0.99      | ~ v1_tdlat_3(sK1(sK2,X0))
% 2.13/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.13/0.99      | ~ v2_tex_2(X0,sK2)
% 2.13/0.99      | v2_struct_0(sK1(sK2,X0))
% 2.13/0.99      | v1_xboole_0(X0) ),
% 2.13/0.99      inference(global_propositional_subsumption,
% 2.13/0.99                [status(thm)],
% 2.13/0.99                [c_490,c_24,c_23,c_21]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_495,plain,
% 2.13/0.99      ( ~ v2_tex_2(X0,sK2)
% 2.13/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.13/0.99      | v2_struct_0(sK1(sK2,X0))
% 2.13/0.99      | ~ v1_tdlat_3(sK1(sK2,X0))
% 2.13/0.99      | v1_zfmisc_1(u1_struct_0(sK1(sK2,X0)))
% 2.13/0.99      | ~ l1_pre_topc(sK1(sK2,X0))
% 2.13/0.99      | v1_xboole_0(X0) ),
% 2.13/0.99      inference(renaming,[status(thm)],[c_494]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_699,plain,
% 2.13/0.99      ( ~ v2_tex_2(X0,sK2)
% 2.13/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.13/0.99      | v2_struct_0(sK1(sK2,X0))
% 2.13/0.99      | ~ v1_tdlat_3(sK1(sK2,X0))
% 2.13/0.99      | v1_zfmisc_1(u1_struct_0(sK1(sK2,X0)))
% 2.13/0.99      | v1_xboole_0(X0) ),
% 2.13/0.99      inference(backward_subsumption_resolution,
% 2.13/0.99                [status(thm)],
% 2.13/0.99                [c_588,c_495]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_708,plain,
% 2.13/0.99      ( ~ v2_tex_2(X0,sK2)
% 2.13/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.13/0.99      | ~ v1_tdlat_3(sK1(sK2,X0))
% 2.13/0.99      | v1_zfmisc_1(u1_struct_0(sK1(sK2,X0)))
% 2.13/0.99      | v1_xboole_0(X0) ),
% 2.13/0.99      inference(backward_subsumption_resolution,
% 2.13/0.99                [status(thm)],
% 2.13/0.99                [c_611,c_699]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_717,plain,
% 2.13/0.99      ( ~ v2_tex_2(X0,sK2)
% 2.13/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.13/0.99      | v1_zfmisc_1(u1_struct_0(sK1(sK2,X0)))
% 2.13/0.99      | v1_xboole_0(X0) ),
% 2.13/0.99      inference(backward_subsumption_resolution,
% 2.13/0.99                [status(thm)],
% 2.13/0.99                [c_636,c_708]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_732,plain,
% 2.13/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.13/0.99      | v1_zfmisc_1(u1_struct_0(sK1(sK2,X0)))
% 2.13/0.99      | v1_zfmisc_1(sK3)
% 2.13/0.99      | v1_xboole_0(X0)
% 2.13/0.99      | sK2 != sK2
% 2.13/0.99      | sK3 != X0 ),
% 2.13/0.99      inference(resolution_lifted,[status(thm)],[c_182,c_717]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_733,plain,
% 2.13/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.13/0.99      | v1_zfmisc_1(u1_struct_0(sK1(sK2,sK3)))
% 2.13/0.99      | v1_zfmisc_1(sK3)
% 2.13/0.99      | v1_xboole_0(sK3) ),
% 2.13/0.99      inference(unflattening,[status(thm)],[c_732]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_735,plain,
% 2.13/0.99      ( v1_zfmisc_1(sK3) | v1_zfmisc_1(u1_struct_0(sK1(sK2,sK3))) ),
% 2.13/0.99      inference(global_propositional_subsumption,
% 2.13/0.99                [status(thm)],
% 2.13/0.99                [c_733,c_20,c_19]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_736,plain,
% 2.13/0.99      ( v1_zfmisc_1(u1_struct_0(sK1(sK2,sK3))) | v1_zfmisc_1(sK3) ),
% 2.13/0.99      inference(renaming,[status(thm)],[c_735]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_737,plain,
% 2.13/0.99      ( v1_zfmisc_1(u1_struct_0(sK1(sK2,sK3))) = iProver_top
% 2.13/0.99      | v1_zfmisc_1(sK3) = iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_736]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1400,plain,( X0_49 = X0_49 ),theory(equality) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1420,plain,
% 2.13/0.99      ( sK3 = sK3 ),
% 2.13/0.99      inference(instantiation,[status(thm)],[c_1400]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1407,plain,
% 2.13/0.99      ( ~ v1_zfmisc_1(X0_49) | v1_zfmisc_1(X1_49) | X1_49 != X0_49 ),
% 2.13/0.99      theory(equality) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1990,plain,
% 2.13/0.99      ( v1_zfmisc_1(X0_49)
% 2.13/0.99      | ~ v1_zfmisc_1(u1_struct_0(sK1(sK2,X1_49)))
% 2.13/0.99      | X0_49 != u1_struct_0(sK1(sK2,X1_49)) ),
% 2.13/0.99      inference(instantiation,[status(thm)],[c_1407]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1991,plain,
% 2.13/0.99      ( X0_49 != u1_struct_0(sK1(sK2,X1_49))
% 2.13/0.99      | v1_zfmisc_1(X0_49) = iProver_top
% 2.13/0.99      | v1_zfmisc_1(u1_struct_0(sK1(sK2,X1_49))) != iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_1990]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1993,plain,
% 2.13/0.99      ( sK3 != u1_struct_0(sK1(sK2,sK3))
% 2.13/0.99      | v1_zfmisc_1(u1_struct_0(sK1(sK2,sK3))) != iProver_top
% 2.13/0.99      | v1_zfmisc_1(sK3) = iProver_top ),
% 2.13/0.99      inference(instantiation,[status(thm)],[c_1991]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1402,plain,
% 2.13/0.99      ( X0_49 != X1_49 | X2_49 != X1_49 | X2_49 = X0_49 ),
% 2.13/0.99      theory(equality) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2203,plain,
% 2.13/0.99      ( X0_49 != X1_49
% 2.13/0.99      | X0_49 = u1_struct_0(sK1(sK2,X2_49))
% 2.13/0.99      | u1_struct_0(sK1(sK2,X2_49)) != X1_49 ),
% 2.13/0.99      inference(instantiation,[status(thm)],[c_1402]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2204,plain,
% 2.13/0.99      ( u1_struct_0(sK1(sK2,sK3)) != sK3
% 2.13/0.99      | sK3 = u1_struct_0(sK1(sK2,sK3))
% 2.13/0.99      | sK3 != sK3 ),
% 2.13/0.99      inference(instantiation,[status(thm)],[c_2203]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2227,plain,
% 2.13/0.99      ( v1_zfmisc_1(sK3) = iProver_top ),
% 2.13/0.99      inference(global_propositional_subsumption,
% 2.13/0.99                [status(thm)],
% 2.13/0.99                [c_2008,c_737,c_1420,c_1993,c_2204]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_11,plain,
% 2.13/0.99      ( m1_subset_1(sK0(X0),X0) | ~ v1_zfmisc_1(X0) | v1_xboole_0(X0) ),
% 2.13/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1394,plain,
% 2.13/0.99      ( m1_subset_1(sK0(X0_49),X0_49)
% 2.13/0.99      | ~ v1_zfmisc_1(X0_49)
% 2.13/0.99      | v1_xboole_0(X0_49) ),
% 2.13/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1781,plain,
% 2.13/0.99      ( m1_subset_1(sK0(X0_49),X0_49) = iProver_top
% 2.13/0.99      | v1_zfmisc_1(X0_49) != iProver_top
% 2.13/0.99      | v1_xboole_0(X0_49) = iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_1394]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_6,plain,
% 2.13/0.99      ( ~ m1_subset_1(X0,X1)
% 2.13/0.99      | v1_xboole_0(X1)
% 2.13/0.99      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 2.13/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1397,plain,
% 2.13/0.99      ( ~ m1_subset_1(X0_49,X1_49)
% 2.13/0.99      | v1_xboole_0(X1_49)
% 2.13/0.99      | k6_domain_1(X1_49,X0_49) = k1_tarski(X0_49) ),
% 2.13/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1778,plain,
% 2.13/0.99      ( k6_domain_1(X0_49,X1_49) = k1_tarski(X1_49)
% 2.13/0.99      | m1_subset_1(X1_49,X0_49) != iProver_top
% 2.13/0.99      | v1_xboole_0(X0_49) = iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_1397]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2138,plain,
% 2.13/0.99      ( k6_domain_1(X0_49,sK0(X0_49)) = k1_tarski(sK0(X0_49))
% 2.13/0.99      | v1_zfmisc_1(X0_49) != iProver_top
% 2.13/0.99      | v1_xboole_0(X0_49) = iProver_top ),
% 2.13/0.99      inference(superposition,[status(thm)],[c_1781,c_1778]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2577,plain,
% 2.13/0.99      ( k6_domain_1(sK3,sK0(sK3)) = k1_tarski(sK0(sK3))
% 2.13/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 2.13/0.99      inference(superposition,[status(thm)],[c_2227,c_2138]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_10,plain,
% 2.13/0.99      ( ~ v1_zfmisc_1(X0)
% 2.13/0.99      | v1_xboole_0(X0)
% 2.13/0.99      | k6_domain_1(X0,sK0(X0)) = X0 ),
% 2.13/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1395,plain,
% 2.13/0.99      ( ~ v1_zfmisc_1(X0_49)
% 2.13/0.99      | v1_xboole_0(X0_49)
% 2.13/0.99      | k6_domain_1(X0_49,sK0(X0_49)) = X0_49 ),
% 2.13/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1780,plain,
% 2.13/0.99      ( k6_domain_1(X0_49,sK0(X0_49)) = X0_49
% 2.13/0.99      | v1_zfmisc_1(X0_49) != iProver_top
% 2.13/0.99      | v1_xboole_0(X0_49) = iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_1395]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2232,plain,
% 2.13/0.99      ( k6_domain_1(sK3,sK0(sK3)) = sK3
% 2.13/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 2.13/0.99      inference(superposition,[status(thm)],[c_2227,c_1780]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1429,plain,
% 2.13/0.99      ( k6_domain_1(X0_49,sK0(X0_49)) = X0_49
% 2.13/0.99      | v1_zfmisc_1(X0_49) != iProver_top
% 2.13/0.99      | v1_xboole_0(X0_49) = iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_1395]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1431,plain,
% 2.13/0.99      ( k6_domain_1(sK3,sK0(sK3)) = sK3
% 2.13/0.99      | v1_zfmisc_1(sK3) != iProver_top
% 2.13/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 2.13/0.99      inference(instantiation,[status(thm)],[c_1429]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2264,plain,
% 2.13/0.99      ( k6_domain_1(sK3,sK0(sK3)) = sK3 ),
% 2.13/0.99      inference(global_propositional_subsumption,
% 2.13/0.99                [status(thm)],
% 2.13/0.99                [c_2232,c_29,c_737,c_1420,c_1431,c_1993,c_2008,c_2204]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2593,plain,
% 2.13/0.99      ( k1_tarski(sK0(sK3)) = sK3 | v1_xboole_0(sK3) = iProver_top ),
% 2.13/0.99      inference(light_normalisation,[status(thm)],[c_2577,c_2264]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2832,plain,
% 2.13/0.99      ( k1_tarski(sK0(sK3)) = sK3 ),
% 2.13/0.99      inference(global_propositional_subsumption,
% 2.13/0.99                [status(thm)],
% 2.13/0.99                [c_2593,c_29]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1,plain,
% 2.13/0.99      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 2.13/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2,plain,
% 2.13/0.99      ( ~ r2_hidden(X0,X1)
% 2.13/0.99      | m1_subset_1(X0,X2)
% 2.13/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 2.13/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_339,plain,
% 2.13/0.99      ( ~ m1_subset_1(X0,X1)
% 2.13/0.99      | m1_subset_1(X0,X2)
% 2.13/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 2.13/0.99      | v1_xboole_0(X1) ),
% 2.13/0.99      inference(resolution,[status(thm)],[c_1,c_2]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1389,plain,
% 2.13/0.99      ( ~ m1_subset_1(X0_49,X1_49)
% 2.13/0.99      | m1_subset_1(X0_49,X2_49)
% 2.13/0.99      | ~ m1_subset_1(X1_49,k1_zfmisc_1(X2_49))
% 2.13/0.99      | v1_xboole_0(X1_49) ),
% 2.13/0.99      inference(subtyping,[status(esa)],[c_339]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1786,plain,
% 2.13/0.99      ( m1_subset_1(X0_49,X1_49) != iProver_top
% 2.13/0.99      | m1_subset_1(X0_49,X2_49) = iProver_top
% 2.13/0.99      | m1_subset_1(X1_49,k1_zfmisc_1(X2_49)) != iProver_top
% 2.13/0.99      | v1_xboole_0(X1_49) = iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_1389]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2464,plain,
% 2.13/0.99      ( m1_subset_1(X0_49,u1_struct_0(sK2)) = iProver_top
% 2.13/0.99      | m1_subset_1(X0_49,sK3) != iProver_top
% 2.13/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 2.13/0.99      inference(superposition,[status(thm)],[c_1784,c_1786]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2489,plain,
% 2.13/0.99      ( m1_subset_1(X0_49,sK3) != iProver_top
% 2.13/0.99      | m1_subset_1(X0_49,u1_struct_0(sK2)) = iProver_top ),
% 2.13/0.99      inference(global_propositional_subsumption,
% 2.13/0.99                [status(thm)],
% 2.13/0.99                [c_2464,c_29]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2490,plain,
% 2.13/0.99      ( m1_subset_1(X0_49,u1_struct_0(sK2)) = iProver_top
% 2.13/0.99      | m1_subset_1(X0_49,sK3) != iProver_top ),
% 2.13/0.99      inference(renaming,[status(thm)],[c_2489]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2497,plain,
% 2.13/0.99      ( k6_domain_1(u1_struct_0(sK2),X0_49) = k1_tarski(X0_49)
% 2.13/0.99      | m1_subset_1(X0_49,sK3) != iProver_top
% 2.13/0.99      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.13/0.99      inference(superposition,[status(thm)],[c_2490,c_1778]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_0,plain,
% 2.13/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.13/0.99      | ~ v1_xboole_0(X1)
% 2.13/0.99      | v1_xboole_0(X0) ),
% 2.13/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1398,plain,
% 2.13/0.99      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(X1_49))
% 2.13/0.99      | ~ v1_xboole_0(X1_49)
% 2.13/0.99      | v1_xboole_0(X0_49) ),
% 2.13/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1777,plain,
% 2.13/0.99      ( m1_subset_1(X0_49,k1_zfmisc_1(X1_49)) != iProver_top
% 2.13/0.99      | v1_xboole_0(X1_49) != iProver_top
% 2.13/0.99      | v1_xboole_0(X0_49) = iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_1398]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2014,plain,
% 2.13/0.99      ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top
% 2.13/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 2.13/0.99      inference(superposition,[status(thm)],[c_1784,c_1777]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2599,plain,
% 2.13/0.99      ( m1_subset_1(X0_49,sK3) != iProver_top
% 2.13/0.99      | k6_domain_1(u1_struct_0(sK2),X0_49) = k1_tarski(X0_49) ),
% 2.13/0.99      inference(global_propositional_subsumption,
% 2.13/0.99                [status(thm)],
% 2.13/0.99                [c_2497,c_29,c_2014]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2600,plain,
% 2.13/0.99      ( k6_domain_1(u1_struct_0(sK2),X0_49) = k1_tarski(X0_49)
% 2.13/0.99      | m1_subset_1(X0_49,sK3) != iProver_top ),
% 2.13/0.99      inference(renaming,[status(thm)],[c_2599]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2607,plain,
% 2.13/0.99      ( k6_domain_1(u1_struct_0(sK2),sK0(sK3)) = k1_tarski(sK0(sK3))
% 2.13/0.99      | v1_zfmisc_1(sK3) != iProver_top
% 2.13/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 2.13/0.99      inference(superposition,[status(thm)],[c_1781,c_2600]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_30,plain,
% 2.13/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1432,plain,
% 2.13/0.99      ( m1_subset_1(sK0(X0_49),X0_49) = iProver_top
% 2.13/0.99      | v1_zfmisc_1(X0_49) != iProver_top
% 2.13/0.99      | v1_xboole_0(X0_49) = iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_1394]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1434,plain,
% 2.13/0.99      ( m1_subset_1(sK0(sK3),sK3) = iProver_top
% 2.13/0.99      | v1_zfmisc_1(sK3) != iProver_top
% 2.13/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 2.13/0.99      inference(instantiation,[status(thm)],[c_1432]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1915,plain,
% 2.13/0.99      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(X1_49))
% 2.13/0.99      | ~ m1_subset_1(sK0(X0_49),X0_49)
% 2.13/0.99      | m1_subset_1(sK0(X0_49),X1_49)
% 2.13/0.99      | v1_xboole_0(X0_49) ),
% 2.13/0.99      inference(instantiation,[status(thm)],[c_1389]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1998,plain,
% 2.13/0.99      ( m1_subset_1(sK0(sK3),u1_struct_0(sK2))
% 2.13/0.99      | ~ m1_subset_1(sK0(sK3),sK3)
% 2.13/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.13/0.99      | v1_xboole_0(sK3) ),
% 2.13/0.99      inference(instantiation,[status(thm)],[c_1915]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1999,plain,
% 2.13/0.99      ( m1_subset_1(sK0(sK3),u1_struct_0(sK2)) = iProver_top
% 2.13/0.99      | m1_subset_1(sK0(sK3),sK3) != iProver_top
% 2.13/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.13/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_1998]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2030,plain,
% 2.13/0.99      ( ~ m1_subset_1(sK0(sK3),u1_struct_0(sK2))
% 2.13/0.99      | v1_xboole_0(u1_struct_0(sK2))
% 2.13/0.99      | k6_domain_1(u1_struct_0(sK2),sK0(sK3)) = k1_tarski(sK0(sK3)) ),
% 2.13/0.99      inference(instantiation,[status(thm)],[c_1397]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2031,plain,
% 2.13/0.99      ( k6_domain_1(u1_struct_0(sK2),sK0(sK3)) = k1_tarski(sK0(sK3))
% 2.13/0.99      | m1_subset_1(sK0(sK3),u1_struct_0(sK2)) != iProver_top
% 2.13/0.99      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_2030]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2674,plain,
% 2.13/0.99      ( k6_domain_1(u1_struct_0(sK2),sK0(sK3)) = k1_tarski(sK0(sK3)) ),
% 2.13/0.99      inference(global_propositional_subsumption,
% 2.13/0.99                [status(thm)],
% 2.13/0.99                [c_2607,c_29,c_30,c_737,c_1420,c_1434,c_1993,c_1999,
% 2.13/0.99                 c_2008,c_2014,c_2031,c_2204]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_16,plain,
% 2.13/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 2.13/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.13/0.99      | ~ v2_pre_topc(X0)
% 2.13/0.99      | v2_struct_0(X0)
% 2.13/0.99      | ~ l1_pre_topc(X0) ),
% 2.13/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_678,plain,
% 2.13/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 2.13/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.13/0.99      | v2_struct_0(X0)
% 2.13/0.99      | ~ l1_pre_topc(X0)
% 2.13/0.99      | sK2 != X0 ),
% 2.13/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_679,plain,
% 2.13/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
% 2.13/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.13/0.99      | v2_struct_0(sK2)
% 2.13/0.99      | ~ l1_pre_topc(sK2) ),
% 2.13/0.99      inference(unflattening,[status(thm)],[c_678]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_683,plain,
% 2.13/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
% 2.13/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 2.13/0.99      inference(global_propositional_subsumption,
% 2.13/0.99                [status(thm)],
% 2.13/0.99                [c_679,c_24,c_21]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1387,plain,
% 2.13/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0_49),sK2)
% 2.13/0.99      | ~ m1_subset_1(X0_49,u1_struct_0(sK2)) ),
% 2.13/0.99      inference(subtyping,[status(esa)],[c_683]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1788,plain,
% 2.13/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0_49),sK2) = iProver_top
% 2.13/0.99      | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_1387]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2677,plain,
% 2.13/0.99      ( v2_tex_2(k1_tarski(sK0(sK3)),sK2) = iProver_top
% 2.13/0.99      | m1_subset_1(sK0(sK3),u1_struct_0(sK2)) != iProver_top ),
% 2.13/0.99      inference(superposition,[status(thm)],[c_2674,c_1788]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2694,plain,
% 2.13/0.99      ( v2_tex_2(k1_tarski(sK0(sK3)),sK2) = iProver_top ),
% 2.13/0.99      inference(global_propositional_subsumption,
% 2.13/0.99                [status(thm)],
% 2.13/0.99                [c_2677,c_29,c_30,c_737,c_1420,c_1434,c_1993,c_1999,
% 2.13/0.99                 c_2008,c_2204]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2835,plain,
% 2.13/0.99      ( v2_tex_2(sK3,sK2) = iProver_top ),
% 2.13/0.99      inference(demodulation,[status(thm)],[c_2832,c_2694]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_17,negated_conjecture,
% 2.13/0.99      ( ~ v2_tex_2(sK3,sK2) | ~ v1_zfmisc_1(sK3) ),
% 2.13/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_32,plain,
% 2.13/0.99      ( v2_tex_2(sK3,sK2) != iProver_top
% 2.13/0.99      | v1_zfmisc_1(sK3) != iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(contradiction,plain,
% 2.13/0.99      ( $false ),
% 2.13/0.99      inference(minisat,[status(thm)],[c_2835,c_2227,c_32]) ).
% 2.13/0.99  
% 2.13/0.99  
% 2.13/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.13/0.99  
% 2.13/0.99  ------                               Statistics
% 2.13/0.99  
% 2.13/0.99  ------ General
% 2.13/0.99  
% 2.13/0.99  abstr_ref_over_cycles:                  0
% 2.13/0.99  abstr_ref_under_cycles:                 0
% 2.13/0.99  gc_basic_clause_elim:                   0
% 2.13/0.99  forced_gc_time:                         0
% 2.13/0.99  parsing_time:                           0.007
% 2.13/0.99  unif_index_cands_time:                  0.
% 2.13/0.99  unif_index_add_time:                    0.
% 2.13/0.99  orderings_time:                         0.
% 2.13/0.99  out_proof_time:                         0.013
% 2.13/0.99  total_time:                             0.086
% 2.13/0.99  num_of_symbols:                         54
% 2.13/0.99  num_of_terms:                           1995
% 2.13/0.99  
% 2.13/0.99  ------ Preprocessing
% 2.13/0.99  
% 2.13/0.99  num_of_splits:                          0
% 2.13/0.99  num_of_split_atoms:                     0
% 2.13/0.99  num_of_reused_defs:                     0
% 2.13/0.99  num_eq_ax_congr_red:                    15
% 2.13/0.99  num_of_sem_filtered_clauses:            1
% 2.13/0.99  num_of_subtypes:                        2
% 2.13/0.99  monotx_restored_types:                  1
% 2.13/0.99  sat_num_of_epr_types:                   0
% 2.13/0.99  sat_num_of_non_cyclic_types:            0
% 2.13/0.99  sat_guarded_non_collapsed_types:        1
% 2.13/0.99  num_pure_diseq_elim:                    0
% 2.13/0.99  simp_replaced_by:                       0
% 2.13/0.99  res_preprocessed:                       86
% 2.13/0.99  prep_upred:                             0
% 2.13/0.99  prep_unflattend:                        33
% 2.13/0.99  smt_new_axioms:                         0
% 2.13/0.99  pred_elim_cands:                        4
% 2.13/0.99  pred_elim:                              9
% 2.13/0.99  pred_elim_cl:                           11
% 2.13/0.99  pred_elim_cycles:                       15
% 2.13/0.99  merged_defs:                            8
% 2.13/0.99  merged_defs_ncl:                        0
% 2.13/0.99  bin_hyper_res:                          8
% 2.13/0.99  prep_cycles:                            4
% 2.13/0.99  pred_elim_time:                         0.012
% 2.13/0.99  splitting_time:                         0.
% 2.13/0.99  sem_filter_time:                        0.
% 2.13/0.99  monotx_time:                            0.
% 2.13/0.99  subtype_inf_time:                       0.
% 2.13/0.99  
% 2.13/0.99  ------ Problem properties
% 2.13/0.99  
% 2.13/0.99  clauses:                                13
% 2.13/0.99  conjectures:                            4
% 2.13/0.99  epr:                                    3
% 2.13/0.99  horn:                                   5
% 2.13/0.99  ground:                                 4
% 2.13/0.99  unary:                                  2
% 2.13/0.99  binary:                                 3
% 2.13/0.99  lits:                                   36
% 2.13/0.99  lits_eq:                                4
% 2.13/0.99  fd_pure:                                0
% 2.13/0.99  fd_pseudo:                              0
% 2.13/0.99  fd_cond:                                0
% 2.13/0.99  fd_pseudo_cond:                         0
% 2.13/0.99  ac_symbols:                             0
% 2.13/0.99  
% 2.13/0.99  ------ Propositional Solver
% 2.13/0.99  
% 2.13/0.99  prop_solver_calls:                      26
% 2.13/0.99  prop_fast_solver_calls:                 834
% 2.13/0.99  smt_solver_calls:                       0
% 2.13/0.99  smt_fast_solver_calls:                  0
% 2.13/0.99  prop_num_of_clauses:                    713
% 2.13/0.99  prop_preprocess_simplified:             3052
% 2.13/0.99  prop_fo_subsumed:                       43
% 2.13/0.99  prop_solver_time:                       0.
% 2.13/0.99  smt_solver_time:                        0.
% 2.13/0.99  smt_fast_solver_time:                   0.
% 2.13/0.99  prop_fast_solver_time:                  0.
% 2.13/0.99  prop_unsat_core_time:                   0.
% 2.13/0.99  
% 2.13/0.99  ------ QBF
% 2.13/0.99  
% 2.13/0.99  qbf_q_res:                              0
% 2.13/0.99  qbf_num_tautologies:                    0
% 2.13/0.99  qbf_prep_cycles:                        0
% 2.13/0.99  
% 2.13/0.99  ------ BMC1
% 2.13/0.99  
% 2.13/0.99  bmc1_current_bound:                     -1
% 2.13/0.99  bmc1_last_solved_bound:                 -1
% 2.13/0.99  bmc1_unsat_core_size:                   -1
% 2.13/0.99  bmc1_unsat_core_parents_size:           -1
% 2.13/0.99  bmc1_merge_next_fun:                    0
% 2.13/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.13/0.99  
% 2.13/0.99  ------ Instantiation
% 2.13/0.99  
% 2.13/0.99  inst_num_of_clauses:                    174
% 2.13/0.99  inst_num_in_passive:                    1
% 2.13/0.99  inst_num_in_active:                     109
% 2.13/0.99  inst_num_in_unprocessed:                64
% 2.13/0.99  inst_num_of_loops:                      140
% 2.13/0.99  inst_num_of_learning_restarts:          0
% 2.13/0.99  inst_num_moves_active_passive:          28
% 2.13/0.99  inst_lit_activity:                      0
% 2.13/0.99  inst_lit_activity_moves:                0
% 2.13/0.99  inst_num_tautologies:                   0
% 2.13/0.99  inst_num_prop_implied:                  0
% 2.13/0.99  inst_num_existing_simplified:           0
% 2.13/0.99  inst_num_eq_res_simplified:             0
% 2.13/0.99  inst_num_child_elim:                    0
% 2.13/0.99  inst_num_of_dismatching_blockings:      35
% 2.13/0.99  inst_num_of_non_proper_insts:           126
% 2.13/0.99  inst_num_of_duplicates:                 0
% 2.13/0.99  inst_inst_num_from_inst_to_res:         0
% 2.13/0.99  inst_dismatching_checking_time:         0.
% 2.13/0.99  
% 2.13/0.99  ------ Resolution
% 2.13/0.99  
% 2.13/0.99  res_num_of_clauses:                     0
% 2.13/0.99  res_num_in_passive:                     0
% 2.13/0.99  res_num_in_active:                      0
% 2.13/0.99  res_num_of_loops:                       90
% 2.13/0.99  res_forward_subset_subsumed:            10
% 2.13/0.99  res_backward_subset_subsumed:           0
% 2.13/0.99  res_forward_subsumed:                   0
% 2.13/0.99  res_backward_subsumed:                  0
% 2.13/0.99  res_forward_subsumption_resolution:     0
% 2.13/0.99  res_backward_subsumption_resolution:    3
% 2.13/0.99  res_clause_to_clause_subsumption:       83
% 2.13/0.99  res_orphan_elimination:                 0
% 2.13/0.99  res_tautology_del:                      37
% 2.13/0.99  res_num_eq_res_simplified:              0
% 2.13/0.99  res_num_sel_changes:                    0
% 2.13/0.99  res_moves_from_active_to_pass:          0
% 2.13/0.99  
% 2.13/0.99  ------ Superposition
% 2.13/0.99  
% 2.13/0.99  sup_time_total:                         0.
% 2.13/0.99  sup_time_generating:                    0.
% 2.13/0.99  sup_time_sim_full:                      0.
% 2.13/0.99  sup_time_sim_immed:                     0.
% 2.13/0.99  
% 2.13/0.99  sup_num_of_clauses:                     30
% 2.13/0.99  sup_num_in_active:                      22
% 2.13/0.99  sup_num_in_passive:                     8
% 2.13/0.99  sup_num_of_loops:                       26
% 2.13/0.99  sup_fw_superposition:                   13
% 2.13/0.99  sup_bw_superposition:                   9
% 2.13/0.99  sup_immediate_simplified:               2
% 2.13/0.99  sup_given_eliminated:                   0
% 2.13/0.99  comparisons_done:                       0
% 2.13/0.99  comparisons_avoided:                    0
% 2.13/0.99  
% 2.13/0.99  ------ Simplifications
% 2.13/0.99  
% 2.13/0.99  
% 2.13/0.99  sim_fw_subset_subsumed:                 1
% 2.13/0.99  sim_bw_subset_subsumed:                 2
% 2.13/0.99  sim_fw_subsumed:                        0
% 2.13/0.99  sim_bw_subsumed:                        0
% 2.13/0.99  sim_fw_subsumption_res:                 0
% 2.13/0.99  sim_bw_subsumption_res:                 0
% 2.13/0.99  sim_tautology_del:                      1
% 2.13/0.99  sim_eq_tautology_del:                   0
% 2.13/0.99  sim_eq_res_simp:                        0
% 2.13/0.99  sim_fw_demodulated:                     0
% 2.13/0.99  sim_bw_demodulated:                     2
% 2.13/0.99  sim_light_normalised:                   1
% 2.13/0.99  sim_joinable_taut:                      0
% 2.13/0.99  sim_joinable_simp:                      0
% 2.13/0.99  sim_ac_normalised:                      0
% 2.13/0.99  sim_smt_subsumption:                    0
% 2.13/0.99  
%------------------------------------------------------------------------------
