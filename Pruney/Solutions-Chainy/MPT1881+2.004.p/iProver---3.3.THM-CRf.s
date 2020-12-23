%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:10 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :  262 (2098 expanded)
%              Number of clauses        :  142 ( 555 expanded)
%              Number of leaves         :   30 ( 455 expanded)
%              Depth                    :   30
%              Number of atoms          : 1045 (12381 expanded)
%              Number of equality atoms :  186 ( 821 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,conjecture,(
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

fof(f28,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f66,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f67,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f80,plain,(
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
    inference(nnf_transformation,[],[f67])).

fof(f81,plain,(
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
    inference(flattening,[],[f80])).

fof(f83,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( v1_subset_1(sK4,u1_struct_0(X0))
          | ~ v3_tex_2(sK4,X0) )
        & ( ~ v1_subset_1(sK4,u1_struct_0(X0))
          | v3_tex_2(sK4,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,
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
          ( ( v1_subset_1(X1,u1_struct_0(sK3))
            | ~ v3_tex_2(X1,sK3) )
          & ( ~ v1_subset_1(X1,u1_struct_0(sK3))
            | v3_tex_2(X1,sK3) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_pre_topc(sK3)
      & v1_tdlat_3(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,
    ( ( v1_subset_1(sK4,u1_struct_0(sK3))
      | ~ v3_tex_2(sK4,sK3) )
    & ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
      | v3_tex_2(sK4,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK3)
    & v1_tdlat_3(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f81,f83,f82])).

fof(f128,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f84])).

fof(f21,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(pure_predicate_removal,[],[f21])).

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f30])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f74,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK1(X0,X1)) = X1
        & m1_pre_topc(sK1(X0,X1),X0)
        & ~ v2_struct_0(sK1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK1(X0,X1)) = X1
            & m1_pre_topc(sK1(X0,X1),X0)
            & ~ v2_struct_0(sK1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f55,f74])).

fof(f115,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f127,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f84])).

fof(f124,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f84])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v1_borsuk_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                <=> v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> v4_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> v4_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                  | ~ v4_pre_topc(X2,X0) )
                & ( v4_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                  | ~ v4_pre_topc(X2,X0) )
                & ( v4_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f70])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f137,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f102])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f105,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f106,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f126,plain,(
    v1_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f84])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f112,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f129,plain,
    ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
    | v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f84])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f125,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f84])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f130,plain,
    ( v1_subset_1(sK4,u1_struct_0(sK3))
    | ~ v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f84])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f11])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f32])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f133,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f89,f87])).

fof(f116,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f111,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f138,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f111])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f110,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f120,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f26,axiom,(
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

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f64])).

fof(f123,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f92,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f131,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f92,f87])).

fof(f134,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f90,f131])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f132,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f88,f131])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f57,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f76,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f77,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f76])).

fof(f78,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK2(X0),X0)
            & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f77,f78])).

fof(f117,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f122,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f109,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_subset_1(X1,X0)
           => ~ v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f68,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v4_pre_topc(sK0(X0),X0)
        & v3_pre_topc(sK0(X0),X0)
        & ~ v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0] :
      ( ( v4_pre_topc(sK0(X0),X0)
        & v3_pre_topc(sK0(X0),X0)
        & ~ v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f68])).

fof(f98,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f99,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_3529,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_28,plain,
    ( m1_pre_topc(sK1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_40,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_1176,plain,
    ( m1_pre_topc(sK1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_40])).

cnf(c_1177,plain,
    ( m1_pre_topc(sK1(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_1176])).

cnf(c_43,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_1181,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_pre_topc(sK1(sK3,X0),sK3)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1177,c_43])).

cnf(c_1182,plain,
    ( m1_pre_topc(sK1(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_1181])).

cnf(c_3524,plain,
    ( m1_pre_topc(sK1(sK3,X0),sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1182])).

cnf(c_4435,plain,
    ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3529,c_3524])).

cnf(c_10,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_21,plain,
    ( v1_borsuk_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_17,plain,
    ( ~ v1_borsuk_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v4_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_263,plain,
    ( v4_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_borsuk_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_18])).

cnf(c_264,plain,
    ( ~ v1_borsuk_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v4_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_263])).

cnf(c_622,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v4_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_21,c_264])).

cnf(c_19,plain,
    ( ~ v1_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_638,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v4_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_622,c_19])).

cnf(c_678,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | X1 != X3
    | k2_pre_topc(X3,X2) = X2
    | u1_struct_0(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_638])).

cnf(c_679,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,u1_struct_0(X0)) = u1_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_678])).

cnf(c_683,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,u1_struct_0(X0)) = u1_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_679,c_18])).

cnf(c_1263,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | k2_pre_topc(X1,u1_struct_0(X0)) = u1_struct_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_683,c_40])).

cnf(c_1264,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | ~ v1_tdlat_3(sK3)
    | v2_struct_0(sK3)
    | k2_pre_topc(sK3,u1_struct_0(X0)) = u1_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_1263])).

cnf(c_41,negated_conjecture,
    ( v1_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_1268,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | k2_pre_topc(sK3,u1_struct_0(X0)) = u1_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1264,c_43,c_41])).

cnf(c_3521,plain,
    ( k2_pre_topc(sK3,u1_struct_0(X0)) = u1_struct_0(X0)
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1268])).

cnf(c_4468,plain,
    ( k2_pre_topc(sK3,u1_struct_0(sK1(sK3,sK4))) = u1_struct_0(sK1(sK3,sK4))
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4435,c_3521])).

cnf(c_24,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_38,negated_conjecture,
    ( v3_tex_2(sK4,sK3)
    | ~ v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_337,plain,
    ( v3_tex_2(sK4,sK3)
    | ~ v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(prop_impl,[status(thm)],[c_38])).

cnf(c_951,plain,
    ( v3_tex_2(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 = X0
    | u1_struct_0(sK3) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_337])).

cnf(c_952,plain,
    ( v3_tex_2(sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(sK3) = sK4 ),
    inference(unflattening,[status(thm)],[c_951])).

cnf(c_954,plain,
    ( v3_tex_2(sK4,sK3)
    | u1_struct_0(sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_952,c_39])).

cnf(c_34,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1281,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_40])).

cnf(c_1282,plain,
    ( ~ v3_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_1281])).

cnf(c_42,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_1286,plain,
    ( ~ v3_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1282,c_43,c_42])).

cnf(c_1556,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(X0)
    | u1_struct_0(sK3) = sK4
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_954,c_1286])).

cnf(c_1557,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(sK4)
    | u1_struct_0(sK3) = sK4 ),
    inference(unflattening,[status(thm)],[c_1556])).

cnf(c_1559,plain,
    ( ~ v1_xboole_0(sK4)
    | u1_struct_0(sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1557,c_39])).

cnf(c_3514,plain,
    ( u1_struct_0(sK3) = sK4
    | v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1559])).

cnf(c_5738,plain,
    ( k2_pre_topc(sK3,u1_struct_0(sK1(sK3,sK4))) = u1_struct_0(sK1(sK3,sK4))
    | u1_struct_0(sK3) = sK4 ),
    inference(superposition,[status(thm)],[c_4468,c_3514])).

cnf(c_7,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_37,negated_conjecture,
    ( ~ v3_tex_2(sK4,sK3)
    | v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_339,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(prop_impl,[status(thm)],[c_37])).

cnf(c_996,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | u1_struct_0(sK3) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_339])).

cnf(c_997,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_996])).

cnf(c_999,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_997,c_39])).

cnf(c_1476,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(sK3) = sK4 ),
    inference(resolution,[status(thm)],[c_954,c_999])).

cnf(c_1477,plain,
    ( u1_struct_0(sK3) = sK4
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1476])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_556,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_557,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_556])).

cnf(c_571,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(X2)
    | X2 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_557])).

cnf(c_572,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_3731,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_572])).

cnf(c_3733,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3731])).

cnf(c_3,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_3732,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3735,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3732])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1323,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK1(X1,X0)) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_40])).

cnf(c_1324,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | v1_xboole_0(X0)
    | u1_struct_0(sK1(sK3,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_1323])).

cnf(c_1328,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(X0)
    | u1_struct_0(sK1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1324,c_43])).

cnf(c_3520,plain,
    ( u1_struct_0(sK1(sK3,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1328])).

cnf(c_4358,plain,
    ( u1_struct_0(sK1(sK3,sK4)) = sK4
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3529,c_3520])).

cnf(c_3532,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_916,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_24,c_7])).

cnf(c_3526,plain,
    ( X0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_916])).

cnf(c_5384,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3532,c_3526])).

cnf(c_5516,plain,
    ( u1_struct_0(sK1(sK3,sK4)) = sK4
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4358,c_5384])).

cnf(c_5737,plain,
    ( k2_pre_topc(sK3,u1_struct_0(sK1(sK3,sK4))) = u1_struct_0(sK1(sK3,sK4))
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4468,c_5384])).

cnf(c_7334,plain,
    ( u1_struct_0(sK1(sK3,sK4)) = k2_pre_topc(sK3,sK4)
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5516,c_5737])).

cnf(c_7567,plain,
    ( k2_pre_topc(sK3,sK4) = sK4
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7334,c_5516])).

cnf(c_25,plain,
    ( ~ v1_subset_1(X0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_1010,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | u1_struct_0(sK3) != X0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_339])).

cnf(c_1011,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | sK4 != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1010])).

cnf(c_22,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_33,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_36,plain,
    ( v3_tex_2(X0,X1)
    | ~ v2_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_586,plain,
    ( v3_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_33,c_36])).

cnf(c_604,plain,
    ( v3_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_586,c_19])).

cnf(c_1077,plain,
    ( v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != u1_struct_0(X1) ),
    inference(resolution,[status(thm)],[c_22,c_604])).

cnf(c_1221,plain,
    ( v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | k2_pre_topc(X1,X0) != u1_struct_0(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1077,c_40])).

cnf(c_1222,plain,
    ( v3_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tdlat_3(sK3)
    | v2_struct_0(sK3)
    | k2_pre_topc(sK3,X0) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1221])).

cnf(c_1226,plain,
    ( v3_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,X0) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1222,c_43,c_41])).

cnf(c_1581,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,X0) != u1_struct_0(sK3)
    | u1_struct_0(sK3) != sK4
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1011,c_1226])).

cnf(c_1582,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,sK4) != u1_struct_0(sK3)
    | u1_struct_0(sK3) != sK4 ),
    inference(unflattening,[status(thm)],[c_1581])).

cnf(c_1584,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,sK4) != u1_struct_0(sK3)
    | u1_struct_0(sK3) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1582,c_39])).

cnf(c_3513,plain,
    ( k2_pre_topc(sK3,sK4) != u1_struct_0(sK3)
    | u1_struct_0(sK3) != sK4
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1584])).

cnf(c_4,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_3531,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f132])).

cnf(c_3545,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3531,c_2])).

cnf(c_3632,plain,
    ( k2_pre_topc(sK3,sK4) != u1_struct_0(sK3)
    | u1_struct_0(sK3) != sK4 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3513,c_3545])).

cnf(c_9297,plain,
    ( u1_struct_0(sK3) != sK4
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7567,c_3632])).

cnf(c_32,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_35,plain,
    ( ~ v3_tex_2(X0,X1)
    | v1_tops_1(X0,X1)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_807,plain,
    ( ~ v3_tex_2(X0,X1)
    | v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_32,c_35])).

cnf(c_825,plain,
    ( ~ v3_tex_2(X0,X1)
    | v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_807,c_19])).

cnf(c_23,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1054,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
    inference(resolution,[status(thm)],[c_825,c_23])).

cnf(c_1242,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1054,c_40])).

cnf(c_1243,plain,
    ( ~ v3_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tdlat_3(sK3)
    | v2_struct_0(sK3)
    | k2_pre_topc(sK3,X0) = u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1242])).

cnf(c_1247,plain,
    ( ~ v3_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,X0) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1243,c_43,c_41])).

cnf(c_1570,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,X0) = u1_struct_0(sK3)
    | u1_struct_0(sK3) = sK4
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_954,c_1247])).

cnf(c_1571,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,sK4) = u1_struct_0(sK3)
    | u1_struct_0(sK3) = sK4 ),
    inference(unflattening,[status(thm)],[c_1570])).

cnf(c_1573,plain,
    ( k2_pre_topc(sK3,sK4) = u1_struct_0(sK3)
    | u1_struct_0(sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1571,c_39])).

cnf(c_9300,plain,
    ( u1_struct_0(sK3) = sK4
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7567,c_1573])).

cnf(c_9307,plain,
    ( sK4 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9297,c_9300])).

cnf(c_6,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_965,plain,
    ( v3_tex_2(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(sK3) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_337])).

cnf(c_966,plain,
    ( v3_tex_2(sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_965])).

cnf(c_968,plain,
    ( v3_tex_2(sK4,sK3)
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ v1_xboole_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_966,c_39])).

cnf(c_1540,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ v1_xboole_0(sK4)
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_968,c_1286])).

cnf(c_1541,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1540])).

cnf(c_1543,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ v1_xboole_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1541,c_39])).

cnf(c_3515,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1543])).

cnf(c_9341,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9307,c_3515])).

cnf(c_9447,plain,
    ( u1_struct_0(sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5738,c_1477,c_3733,c_3735,c_9341])).

cnf(c_9449,plain,
    ( u1_struct_0(sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9447,c_9307])).

cnf(c_14,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1199,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_40])).

cnf(c_1200,plain,
    ( m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1199])).

cnf(c_108,plain,
    ( m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1202,plain,
    ( m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1200,c_43,c_42,c_40,c_108])).

cnf(c_3523,plain,
    ( m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1202])).

cnf(c_9472,plain,
    ( m1_subset_1(sK0(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9449,c_3523])).

cnf(c_3528,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_572])).

cnf(c_9735,plain,
    ( v1_xboole_0(sK0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9472,c_3528])).

cnf(c_13,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_xboole_0(sK0(X0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_110,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_xboole_0(sK0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_112,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_110])).

cnf(c_47,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_45,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_44,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9735,c_112,c_47,c_45,c_44])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:24:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.19/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/0.98  
% 3.19/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.19/0.98  
% 3.19/0.98  ------  iProver source info
% 3.19/0.98  
% 3.19/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.19/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.19/0.98  git: non_committed_changes: false
% 3.19/0.98  git: last_make_outside_of_git: false
% 3.19/0.98  
% 3.19/0.98  ------ 
% 3.19/0.98  
% 3.19/0.98  ------ Input Options
% 3.19/0.98  
% 3.19/0.98  --out_options                           all
% 3.19/0.98  --tptp_safe_out                         true
% 3.19/0.98  --problem_path                          ""
% 3.19/0.98  --include_path                          ""
% 3.19/0.98  --clausifier                            res/vclausify_rel
% 3.19/0.98  --clausifier_options                    --mode clausify
% 3.19/0.98  --stdin                                 false
% 3.19/0.98  --stats_out                             all
% 3.19/0.98  
% 3.19/0.98  ------ General Options
% 3.19/0.98  
% 3.19/0.98  --fof                                   false
% 3.19/0.98  --time_out_real                         305.
% 3.19/0.98  --time_out_virtual                      -1.
% 3.19/0.98  --symbol_type_check                     false
% 3.19/0.98  --clausify_out                          false
% 3.19/0.98  --sig_cnt_out                           false
% 3.19/0.98  --trig_cnt_out                          false
% 3.19/0.98  --trig_cnt_out_tolerance                1.
% 3.19/0.98  --trig_cnt_out_sk_spl                   false
% 3.19/0.98  --abstr_cl_out                          false
% 3.19/0.98  
% 3.19/0.98  ------ Global Options
% 3.19/0.98  
% 3.19/0.98  --schedule                              default
% 3.19/0.98  --add_important_lit                     false
% 3.19/0.98  --prop_solver_per_cl                    1000
% 3.19/0.98  --min_unsat_core                        false
% 3.19/0.98  --soft_assumptions                      false
% 3.19/0.98  --soft_lemma_size                       3
% 3.19/0.98  --prop_impl_unit_size                   0
% 3.19/0.98  --prop_impl_unit                        []
% 3.19/0.98  --share_sel_clauses                     true
% 3.19/0.98  --reset_solvers                         false
% 3.19/0.98  --bc_imp_inh                            [conj_cone]
% 3.19/0.98  --conj_cone_tolerance                   3.
% 3.19/0.98  --extra_neg_conj                        none
% 3.19/0.98  --large_theory_mode                     true
% 3.19/0.98  --prolific_symb_bound                   200
% 3.19/0.98  --lt_threshold                          2000
% 3.19/0.98  --clause_weak_htbl                      true
% 3.19/0.98  --gc_record_bc_elim                     false
% 3.19/0.98  
% 3.19/0.98  ------ Preprocessing Options
% 3.19/0.98  
% 3.19/0.98  --preprocessing_flag                    true
% 3.19/0.98  --time_out_prep_mult                    0.1
% 3.19/0.98  --splitting_mode                        input
% 3.19/0.98  --splitting_grd                         true
% 3.19/0.98  --splitting_cvd                         false
% 3.19/0.98  --splitting_cvd_svl                     false
% 3.19/0.98  --splitting_nvd                         32
% 3.19/0.98  --sub_typing                            true
% 3.19/0.98  --prep_gs_sim                           true
% 3.19/0.98  --prep_unflatten                        true
% 3.19/0.98  --prep_res_sim                          true
% 3.19/0.98  --prep_upred                            true
% 3.19/0.98  --prep_sem_filter                       exhaustive
% 3.19/0.98  --prep_sem_filter_out                   false
% 3.19/0.98  --pred_elim                             true
% 3.19/0.98  --res_sim_input                         true
% 3.19/0.98  --eq_ax_congr_red                       true
% 3.19/0.98  --pure_diseq_elim                       true
% 3.19/0.98  --brand_transform                       false
% 3.19/0.98  --non_eq_to_eq                          false
% 3.19/0.98  --prep_def_merge                        true
% 3.19/0.98  --prep_def_merge_prop_impl              false
% 3.19/0.98  --prep_def_merge_mbd                    true
% 3.19/0.98  --prep_def_merge_tr_red                 false
% 3.19/0.98  --prep_def_merge_tr_cl                  false
% 3.19/0.98  --smt_preprocessing                     true
% 3.19/0.98  --smt_ac_axioms                         fast
% 3.19/0.98  --preprocessed_out                      false
% 3.19/0.98  --preprocessed_stats                    false
% 3.19/0.98  
% 3.19/0.98  ------ Abstraction refinement Options
% 3.19/0.98  
% 3.19/0.98  --abstr_ref                             []
% 3.19/0.98  --abstr_ref_prep                        false
% 3.19/0.98  --abstr_ref_until_sat                   false
% 3.19/0.98  --abstr_ref_sig_restrict                funpre
% 3.19/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.19/0.98  --abstr_ref_under                       []
% 3.19/0.98  
% 3.19/0.98  ------ SAT Options
% 3.19/0.98  
% 3.19/0.98  --sat_mode                              false
% 3.19/0.98  --sat_fm_restart_options                ""
% 3.19/0.98  --sat_gr_def                            false
% 3.19/0.98  --sat_epr_types                         true
% 3.19/0.98  --sat_non_cyclic_types                  false
% 3.19/0.98  --sat_finite_models                     false
% 3.19/0.98  --sat_fm_lemmas                         false
% 3.19/0.98  --sat_fm_prep                           false
% 3.19/0.98  --sat_fm_uc_incr                        true
% 3.19/0.98  --sat_out_model                         small
% 3.19/0.98  --sat_out_clauses                       false
% 3.19/0.98  
% 3.19/0.98  ------ QBF Options
% 3.19/0.98  
% 3.19/0.98  --qbf_mode                              false
% 3.19/0.98  --qbf_elim_univ                         false
% 3.19/0.98  --qbf_dom_inst                          none
% 3.19/0.98  --qbf_dom_pre_inst                      false
% 3.19/0.98  --qbf_sk_in                             false
% 3.19/0.98  --qbf_pred_elim                         true
% 3.19/0.98  --qbf_split                             512
% 3.19/0.98  
% 3.19/0.98  ------ BMC1 Options
% 3.19/0.98  
% 3.19/0.98  --bmc1_incremental                      false
% 3.19/0.98  --bmc1_axioms                           reachable_all
% 3.19/0.98  --bmc1_min_bound                        0
% 3.19/0.98  --bmc1_max_bound                        -1
% 3.19/0.98  --bmc1_max_bound_default                -1
% 3.19/0.98  --bmc1_symbol_reachability              true
% 3.19/0.98  --bmc1_property_lemmas                  false
% 3.19/0.98  --bmc1_k_induction                      false
% 3.19/0.98  --bmc1_non_equiv_states                 false
% 3.19/0.98  --bmc1_deadlock                         false
% 3.19/0.98  --bmc1_ucm                              false
% 3.19/0.98  --bmc1_add_unsat_core                   none
% 3.19/0.98  --bmc1_unsat_core_children              false
% 3.19/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.19/0.98  --bmc1_out_stat                         full
% 3.19/0.98  --bmc1_ground_init                      false
% 3.19/0.98  --bmc1_pre_inst_next_state              false
% 3.19/0.98  --bmc1_pre_inst_state                   false
% 3.19/0.98  --bmc1_pre_inst_reach_state             false
% 3.19/0.98  --bmc1_out_unsat_core                   false
% 3.19/0.98  --bmc1_aig_witness_out                  false
% 3.19/0.98  --bmc1_verbose                          false
% 3.19/0.98  --bmc1_dump_clauses_tptp                false
% 3.19/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.19/0.98  --bmc1_dump_file                        -
% 3.19/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.19/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.19/0.98  --bmc1_ucm_extend_mode                  1
% 3.19/0.98  --bmc1_ucm_init_mode                    2
% 3.19/0.98  --bmc1_ucm_cone_mode                    none
% 3.19/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.19/0.98  --bmc1_ucm_relax_model                  4
% 3.19/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.19/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.19/0.98  --bmc1_ucm_layered_model                none
% 3.19/0.98  --bmc1_ucm_max_lemma_size               10
% 3.19/0.98  
% 3.19/0.98  ------ AIG Options
% 3.19/0.98  
% 3.19/0.98  --aig_mode                              false
% 3.19/0.98  
% 3.19/0.98  ------ Instantiation Options
% 3.19/0.98  
% 3.19/0.98  --instantiation_flag                    true
% 3.19/0.98  --inst_sos_flag                         false
% 3.19/0.98  --inst_sos_phase                        true
% 3.19/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.19/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.19/0.98  --inst_lit_sel_side                     num_symb
% 3.19/0.98  --inst_solver_per_active                1400
% 3.19/0.98  --inst_solver_calls_frac                1.
% 3.19/0.98  --inst_passive_queue_type               priority_queues
% 3.19/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.19/0.98  --inst_passive_queues_freq              [25;2]
% 3.19/0.98  --inst_dismatching                      true
% 3.19/0.98  --inst_eager_unprocessed_to_passive     true
% 3.19/0.98  --inst_prop_sim_given                   true
% 3.19/0.98  --inst_prop_sim_new                     false
% 3.19/0.98  --inst_subs_new                         false
% 3.19/0.98  --inst_eq_res_simp                      false
% 3.19/0.98  --inst_subs_given                       false
% 3.19/0.98  --inst_orphan_elimination               true
% 3.19/0.98  --inst_learning_loop_flag               true
% 3.19/0.98  --inst_learning_start                   3000
% 3.19/0.98  --inst_learning_factor                  2
% 3.19/0.98  --inst_start_prop_sim_after_learn       3
% 3.19/0.98  --inst_sel_renew                        solver
% 3.19/0.98  --inst_lit_activity_flag                true
% 3.19/0.98  --inst_restr_to_given                   false
% 3.19/0.98  --inst_activity_threshold               500
% 3.19/0.98  --inst_out_proof                        true
% 3.19/0.98  
% 3.19/0.98  ------ Resolution Options
% 3.19/0.98  
% 3.19/0.98  --resolution_flag                       true
% 3.19/0.98  --res_lit_sel                           adaptive
% 3.19/0.98  --res_lit_sel_side                      none
% 3.19/0.98  --res_ordering                          kbo
% 3.19/0.98  --res_to_prop_solver                    active
% 3.19/0.98  --res_prop_simpl_new                    false
% 3.19/0.98  --res_prop_simpl_given                  true
% 3.19/0.98  --res_passive_queue_type                priority_queues
% 3.19/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.19/0.98  --res_passive_queues_freq               [15;5]
% 3.19/0.98  --res_forward_subs                      full
% 3.19/0.98  --res_backward_subs                     full
% 3.19/0.98  --res_forward_subs_resolution           true
% 3.19/0.98  --res_backward_subs_resolution          true
% 3.19/0.98  --res_orphan_elimination                true
% 3.19/0.98  --res_time_limit                        2.
% 3.19/0.98  --res_out_proof                         true
% 3.19/0.98  
% 3.19/0.98  ------ Superposition Options
% 3.19/0.98  
% 3.19/0.98  --superposition_flag                    true
% 3.19/0.98  --sup_passive_queue_type                priority_queues
% 3.19/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.19/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.19/0.98  --demod_completeness_check              fast
% 3.19/0.98  --demod_use_ground                      true
% 3.19/0.98  --sup_to_prop_solver                    passive
% 3.19/0.98  --sup_prop_simpl_new                    true
% 3.19/0.98  --sup_prop_simpl_given                  true
% 3.19/0.98  --sup_fun_splitting                     false
% 3.19/0.98  --sup_smt_interval                      50000
% 3.19/0.98  
% 3.19/0.98  ------ Superposition Simplification Setup
% 3.19/0.98  
% 3.19/0.98  --sup_indices_passive                   []
% 3.19/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.19/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.98  --sup_full_bw                           [BwDemod]
% 3.19/0.98  --sup_immed_triv                        [TrivRules]
% 3.19/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.19/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.98  --sup_immed_bw_main                     []
% 3.19/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.19/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/0.98  
% 3.19/0.98  ------ Combination Options
% 3.19/0.98  
% 3.19/0.98  --comb_res_mult                         3
% 3.19/0.98  --comb_sup_mult                         2
% 3.19/0.98  --comb_inst_mult                        10
% 3.19/0.98  
% 3.19/0.98  ------ Debug Options
% 3.19/0.98  
% 3.19/0.98  --dbg_backtrace                         false
% 3.19/0.98  --dbg_dump_prop_clauses                 false
% 3.19/0.98  --dbg_dump_prop_clauses_file            -
% 3.19/0.98  --dbg_out_stat                          false
% 3.19/0.98  ------ Parsing...
% 3.19/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.19/0.98  
% 3.19/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 10 0s  sf_e  pe_s  pe_e 
% 3.19/0.98  
% 3.19/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.19/0.98  
% 3.19/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.19/0.98  ------ Proving...
% 3.19/0.98  ------ Problem Properties 
% 3.19/0.98  
% 3.19/0.98  
% 3.19/0.98  clauses                                 26
% 3.19/0.98  conjectures                             1
% 3.19/0.98  EPR                                     0
% 3.19/0.98  Horn                                    22
% 3.19/0.98  unary                                   7
% 3.19/0.98  binary                                  11
% 3.19/0.98  lits                                    54
% 3.19/0.98  lits eq                                 20
% 3.19/0.98  fd_pure                                 0
% 3.19/0.98  fd_pseudo                               0
% 3.19/0.98  fd_cond                                 0
% 3.19/0.98  fd_pseudo_cond                          2
% 3.19/0.98  AC symbols                              0
% 3.19/0.98  
% 3.19/0.98  ------ Schedule dynamic 5 is on 
% 3.19/0.98  
% 3.19/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.19/0.98  
% 3.19/0.98  
% 3.19/0.98  ------ 
% 3.19/0.98  Current options:
% 3.19/0.98  ------ 
% 3.19/0.98  
% 3.19/0.98  ------ Input Options
% 3.19/0.98  
% 3.19/0.98  --out_options                           all
% 3.19/0.98  --tptp_safe_out                         true
% 3.19/0.98  --problem_path                          ""
% 3.19/0.98  --include_path                          ""
% 3.19/0.98  --clausifier                            res/vclausify_rel
% 3.19/0.98  --clausifier_options                    --mode clausify
% 3.19/0.98  --stdin                                 false
% 3.19/0.98  --stats_out                             all
% 3.19/0.98  
% 3.19/0.98  ------ General Options
% 3.19/0.98  
% 3.19/0.98  --fof                                   false
% 3.19/0.98  --time_out_real                         305.
% 3.19/0.98  --time_out_virtual                      -1.
% 3.19/0.98  --symbol_type_check                     false
% 3.19/0.98  --clausify_out                          false
% 3.19/0.98  --sig_cnt_out                           false
% 3.19/0.98  --trig_cnt_out                          false
% 3.19/0.98  --trig_cnt_out_tolerance                1.
% 3.19/0.98  --trig_cnt_out_sk_spl                   false
% 3.19/0.98  --abstr_cl_out                          false
% 3.19/0.98  
% 3.19/0.98  ------ Global Options
% 3.19/0.98  
% 3.19/0.98  --schedule                              default
% 3.19/0.98  --add_important_lit                     false
% 3.19/0.98  --prop_solver_per_cl                    1000
% 3.19/0.98  --min_unsat_core                        false
% 3.19/0.98  --soft_assumptions                      false
% 3.19/0.98  --soft_lemma_size                       3
% 3.19/0.98  --prop_impl_unit_size                   0
% 3.19/0.98  --prop_impl_unit                        []
% 3.19/0.98  --share_sel_clauses                     true
% 3.19/0.98  --reset_solvers                         false
% 3.19/0.98  --bc_imp_inh                            [conj_cone]
% 3.19/0.98  --conj_cone_tolerance                   3.
% 3.19/0.98  --extra_neg_conj                        none
% 3.19/0.98  --large_theory_mode                     true
% 3.19/0.98  --prolific_symb_bound                   200
% 3.19/0.98  --lt_threshold                          2000
% 3.19/0.98  --clause_weak_htbl                      true
% 3.19/0.98  --gc_record_bc_elim                     false
% 3.19/0.98  
% 3.19/0.98  ------ Preprocessing Options
% 3.19/0.98  
% 3.19/0.98  --preprocessing_flag                    true
% 3.19/0.98  --time_out_prep_mult                    0.1
% 3.19/0.98  --splitting_mode                        input
% 3.19/0.98  --splitting_grd                         true
% 3.19/0.98  --splitting_cvd                         false
% 3.19/0.98  --splitting_cvd_svl                     false
% 3.19/0.98  --splitting_nvd                         32
% 3.19/0.98  --sub_typing                            true
% 3.19/0.98  --prep_gs_sim                           true
% 3.19/0.98  --prep_unflatten                        true
% 3.19/0.98  --prep_res_sim                          true
% 3.19/0.98  --prep_upred                            true
% 3.19/0.98  --prep_sem_filter                       exhaustive
% 3.19/0.98  --prep_sem_filter_out                   false
% 3.19/0.98  --pred_elim                             true
% 3.19/0.98  --res_sim_input                         true
% 3.19/0.98  --eq_ax_congr_red                       true
% 3.19/0.98  --pure_diseq_elim                       true
% 3.19/0.98  --brand_transform                       false
% 3.19/0.98  --non_eq_to_eq                          false
% 3.19/0.98  --prep_def_merge                        true
% 3.19/0.98  --prep_def_merge_prop_impl              false
% 3.19/0.98  --prep_def_merge_mbd                    true
% 3.19/0.98  --prep_def_merge_tr_red                 false
% 3.19/0.98  --prep_def_merge_tr_cl                  false
% 3.19/0.98  --smt_preprocessing                     true
% 3.19/0.98  --smt_ac_axioms                         fast
% 3.19/0.98  --preprocessed_out                      false
% 3.19/0.98  --preprocessed_stats                    false
% 3.19/0.98  
% 3.19/0.98  ------ Abstraction refinement Options
% 3.19/0.98  
% 3.19/0.98  --abstr_ref                             []
% 3.19/0.98  --abstr_ref_prep                        false
% 3.19/0.98  --abstr_ref_until_sat                   false
% 3.19/0.98  --abstr_ref_sig_restrict                funpre
% 3.19/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.19/0.98  --abstr_ref_under                       []
% 3.19/0.98  
% 3.19/0.98  ------ SAT Options
% 3.19/0.98  
% 3.19/0.98  --sat_mode                              false
% 3.19/0.98  --sat_fm_restart_options                ""
% 3.19/0.98  --sat_gr_def                            false
% 3.19/0.98  --sat_epr_types                         true
% 3.19/0.98  --sat_non_cyclic_types                  false
% 3.19/0.98  --sat_finite_models                     false
% 3.19/0.98  --sat_fm_lemmas                         false
% 3.19/0.98  --sat_fm_prep                           false
% 3.19/0.98  --sat_fm_uc_incr                        true
% 3.19/0.98  --sat_out_model                         small
% 3.19/0.98  --sat_out_clauses                       false
% 3.19/0.98  
% 3.19/0.98  ------ QBF Options
% 3.19/0.98  
% 3.19/0.98  --qbf_mode                              false
% 3.19/0.98  --qbf_elim_univ                         false
% 3.19/0.98  --qbf_dom_inst                          none
% 3.19/0.98  --qbf_dom_pre_inst                      false
% 3.19/0.98  --qbf_sk_in                             false
% 3.19/0.98  --qbf_pred_elim                         true
% 3.19/0.98  --qbf_split                             512
% 3.19/0.98  
% 3.19/0.98  ------ BMC1 Options
% 3.19/0.98  
% 3.19/0.98  --bmc1_incremental                      false
% 3.19/0.98  --bmc1_axioms                           reachable_all
% 3.19/0.98  --bmc1_min_bound                        0
% 3.19/0.98  --bmc1_max_bound                        -1
% 3.19/0.98  --bmc1_max_bound_default                -1
% 3.19/0.98  --bmc1_symbol_reachability              true
% 3.19/0.98  --bmc1_property_lemmas                  false
% 3.19/0.98  --bmc1_k_induction                      false
% 3.19/0.98  --bmc1_non_equiv_states                 false
% 3.19/0.98  --bmc1_deadlock                         false
% 3.19/0.98  --bmc1_ucm                              false
% 3.19/0.98  --bmc1_add_unsat_core                   none
% 3.19/0.98  --bmc1_unsat_core_children              false
% 3.19/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.19/0.98  --bmc1_out_stat                         full
% 3.19/0.98  --bmc1_ground_init                      false
% 3.19/0.98  --bmc1_pre_inst_next_state              false
% 3.19/0.98  --bmc1_pre_inst_state                   false
% 3.19/0.98  --bmc1_pre_inst_reach_state             false
% 3.19/0.98  --bmc1_out_unsat_core                   false
% 3.19/0.98  --bmc1_aig_witness_out                  false
% 3.19/0.98  --bmc1_verbose                          false
% 3.19/0.98  --bmc1_dump_clauses_tptp                false
% 3.19/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.19/0.98  --bmc1_dump_file                        -
% 3.19/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.19/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.19/0.98  --bmc1_ucm_extend_mode                  1
% 3.19/0.98  --bmc1_ucm_init_mode                    2
% 3.19/0.98  --bmc1_ucm_cone_mode                    none
% 3.19/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.19/0.98  --bmc1_ucm_relax_model                  4
% 3.19/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.19/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.19/0.98  --bmc1_ucm_layered_model                none
% 3.19/0.98  --bmc1_ucm_max_lemma_size               10
% 3.19/0.98  
% 3.19/0.98  ------ AIG Options
% 3.19/0.98  
% 3.19/0.98  --aig_mode                              false
% 3.19/0.98  
% 3.19/0.98  ------ Instantiation Options
% 3.19/0.98  
% 3.19/0.98  --instantiation_flag                    true
% 3.19/0.98  --inst_sos_flag                         false
% 3.19/0.98  --inst_sos_phase                        true
% 3.19/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.19/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.19/0.98  --inst_lit_sel_side                     none
% 3.19/0.98  --inst_solver_per_active                1400
% 3.19/0.98  --inst_solver_calls_frac                1.
% 3.19/0.98  --inst_passive_queue_type               priority_queues
% 3.19/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.19/0.98  --inst_passive_queues_freq              [25;2]
% 3.19/0.98  --inst_dismatching                      true
% 3.19/0.98  --inst_eager_unprocessed_to_passive     true
% 3.19/0.98  --inst_prop_sim_given                   true
% 3.19/0.98  --inst_prop_sim_new                     false
% 3.19/0.98  --inst_subs_new                         false
% 3.19/0.98  --inst_eq_res_simp                      false
% 3.19/0.98  --inst_subs_given                       false
% 3.19/0.98  --inst_orphan_elimination               true
% 3.19/0.98  --inst_learning_loop_flag               true
% 3.19/0.98  --inst_learning_start                   3000
% 3.19/0.98  --inst_learning_factor                  2
% 3.19/0.98  --inst_start_prop_sim_after_learn       3
% 3.19/0.98  --inst_sel_renew                        solver
% 3.19/0.98  --inst_lit_activity_flag                true
% 3.19/0.98  --inst_restr_to_given                   false
% 3.19/0.98  --inst_activity_threshold               500
% 3.19/0.98  --inst_out_proof                        true
% 3.19/0.98  
% 3.19/0.98  ------ Resolution Options
% 3.19/0.98  
% 3.19/0.98  --resolution_flag                       false
% 3.19/0.98  --res_lit_sel                           adaptive
% 3.19/0.98  --res_lit_sel_side                      none
% 3.19/0.98  --res_ordering                          kbo
% 3.19/0.98  --res_to_prop_solver                    active
% 3.19/0.98  --res_prop_simpl_new                    false
% 3.19/0.98  --res_prop_simpl_given                  true
% 3.19/0.98  --res_passive_queue_type                priority_queues
% 3.19/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.19/0.98  --res_passive_queues_freq               [15;5]
% 3.19/0.98  --res_forward_subs                      full
% 3.19/0.98  --res_backward_subs                     full
% 3.19/0.98  --res_forward_subs_resolution           true
% 3.19/0.98  --res_backward_subs_resolution          true
% 3.19/0.98  --res_orphan_elimination                true
% 3.19/0.98  --res_time_limit                        2.
% 3.19/0.98  --res_out_proof                         true
% 3.19/0.98  
% 3.19/0.98  ------ Superposition Options
% 3.19/0.98  
% 3.19/0.98  --superposition_flag                    true
% 3.19/0.98  --sup_passive_queue_type                priority_queues
% 3.19/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.19/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.19/0.98  --demod_completeness_check              fast
% 3.19/0.98  --demod_use_ground                      true
% 3.19/0.98  --sup_to_prop_solver                    passive
% 3.19/0.98  --sup_prop_simpl_new                    true
% 3.19/0.98  --sup_prop_simpl_given                  true
% 3.19/0.98  --sup_fun_splitting                     false
% 3.19/0.98  --sup_smt_interval                      50000
% 3.19/0.98  
% 3.19/0.98  ------ Superposition Simplification Setup
% 3.19/0.98  
% 3.19/0.98  --sup_indices_passive                   []
% 3.19/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.19/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.98  --sup_full_bw                           [BwDemod]
% 3.19/0.98  --sup_immed_triv                        [TrivRules]
% 3.19/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.19/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.98  --sup_immed_bw_main                     []
% 3.19/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.19/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/0.98  
% 3.19/0.98  ------ Combination Options
% 3.19/0.98  
% 3.19/0.98  --comb_res_mult                         3
% 3.19/0.98  --comb_sup_mult                         2
% 3.19/0.98  --comb_inst_mult                        10
% 3.19/0.98  
% 3.19/0.98  ------ Debug Options
% 3.19/0.98  
% 3.19/0.98  --dbg_backtrace                         false
% 3.19/0.98  --dbg_dump_prop_clauses                 false
% 3.19/0.98  --dbg_dump_prop_clauses_file            -
% 3.19/0.98  --dbg_out_stat                          false
% 3.19/0.98  
% 3.19/0.98  
% 3.19/0.98  
% 3.19/0.98  
% 3.19/0.98  ------ Proving...
% 3.19/0.98  
% 3.19/0.98  
% 3.19/0.98  % SZS status Theorem for theBenchmark.p
% 3.19/0.98  
% 3.19/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.19/0.98  
% 3.19/0.98  fof(f27,conjecture,(
% 3.19/0.98    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f28,negated_conjecture,(
% 3.19/0.98    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 3.19/0.98    inference(negated_conjecture,[],[f27])).
% 3.19/0.98  
% 3.19/0.98  fof(f66,plain,(
% 3.19/0.98    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.19/0.98    inference(ennf_transformation,[],[f28])).
% 3.19/0.98  
% 3.19/0.98  fof(f67,plain,(
% 3.19/0.98    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.19/0.98    inference(flattening,[],[f66])).
% 3.19/0.98  
% 3.19/0.98  fof(f80,plain,(
% 3.19/0.98    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.19/0.98    inference(nnf_transformation,[],[f67])).
% 3.19/0.98  
% 3.19/0.98  fof(f81,plain,(
% 3.19/0.98    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.19/0.98    inference(flattening,[],[f80])).
% 3.19/0.98  
% 3.19/0.98  fof(f83,plain,(
% 3.19/0.98    ( ! [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_subset_1(sK4,u1_struct_0(X0)) | ~v3_tex_2(sK4,X0)) & (~v1_subset_1(sK4,u1_struct_0(X0)) | v3_tex_2(sK4,X0)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.19/0.98    introduced(choice_axiom,[])).
% 3.19/0.98  
% 3.19/0.98  fof(f82,plain,(
% 3.19/0.98    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK3)) | ~v3_tex_2(X1,sK3)) & (~v1_subset_1(X1,u1_struct_0(sK3)) | v3_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v1_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 3.19/0.98    introduced(choice_axiom,[])).
% 3.19/0.98  
% 3.19/0.98  fof(f84,plain,(
% 3.19/0.98    ((v1_subset_1(sK4,u1_struct_0(sK3)) | ~v3_tex_2(sK4,sK3)) & (~v1_subset_1(sK4,u1_struct_0(sK3)) | v3_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v1_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 3.19/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f81,f83,f82])).
% 3.19/0.98  
% 3.19/0.98  fof(f128,plain,(
% 3.19/0.98    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 3.19/0.98    inference(cnf_transformation,[],[f84])).
% 3.19/0.98  
% 3.19/0.98  fof(f21,axiom,(
% 3.19/0.98    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f30,plain,(
% 3.19/0.98    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 3.19/0.98    inference(pure_predicate_removal,[],[f21])).
% 3.19/0.98  
% 3.19/0.98  fof(f54,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.19/0.98    inference(ennf_transformation,[],[f30])).
% 3.19/0.98  
% 3.19/0.98  fof(f55,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.19/0.98    inference(flattening,[],[f54])).
% 3.19/0.98  
% 3.19/0.98  fof(f74,plain,(
% 3.19/0.98    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & ~v2_struct_0(sK1(X0,X1))))),
% 3.19/0.98    introduced(choice_axiom,[])).
% 3.19/0.98  
% 3.19/0.98  fof(f75,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : ((u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & ~v2_struct_0(sK1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.19/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f55,f74])).
% 3.19/0.98  
% 3.19/0.98  fof(f115,plain,(
% 3.19/0.98    ( ! [X0,X1] : (m1_pre_topc(sK1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f75])).
% 3.19/0.98  
% 3.19/0.98  fof(f127,plain,(
% 3.19/0.98    l1_pre_topc(sK3)),
% 3.19/0.98    inference(cnf_transformation,[],[f84])).
% 3.19/0.98  
% 3.19/0.98  fof(f124,plain,(
% 3.19/0.98    ~v2_struct_0(sK3)),
% 3.19/0.98    inference(cnf_transformation,[],[f84])).
% 3.19/0.98  
% 3.19/0.98  fof(f12,axiom,(
% 3.19/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f39,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.19/0.98    inference(ennf_transformation,[],[f12])).
% 3.19/0.98  
% 3.19/0.98  fof(f40,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.19/0.98    inference(flattening,[],[f39])).
% 3.19/0.98  
% 3.19/0.98  fof(f96,plain,(
% 3.19/0.98    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f40])).
% 3.19/0.98  
% 3.19/0.98  fof(f17,axiom,(
% 3.19/0.98    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0))))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f31,plain,(
% 3.19/0.98    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_borsuk_1(X1,X0))))),
% 3.19/0.98    inference(pure_predicate_removal,[],[f17])).
% 3.19/0.98  
% 3.19/0.98  fof(f48,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & v1_borsuk_1(X1,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.19/0.98    inference(ennf_transformation,[],[f31])).
% 3.19/0.98  
% 3.19/0.98  fof(f49,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & v1_borsuk_1(X1,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.19/0.98    inference(flattening,[],[f48])).
% 3.19/0.98  
% 3.19/0.98  fof(f107,plain,(
% 3.19/0.98    ( ! [X0,X1] : (v1_borsuk_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f49])).
% 3.19/0.98  
% 3.19/0.98  fof(f14,axiom,(
% 3.19/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0))))))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f43,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.19/0.98    inference(ennf_transformation,[],[f14])).
% 3.19/0.98  
% 3.19/0.98  fof(f44,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.19/0.98    inference(flattening,[],[f43])).
% 3.19/0.98  
% 3.19/0.98  fof(f70,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) | ~v4_pre_topc(X2,X0)) & (v4_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.19/0.98    inference(nnf_transformation,[],[f44])).
% 3.19/0.98  
% 3.19/0.98  fof(f71,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) | ~v4_pre_topc(X2,X0)) & (v4_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.19/0.98    inference(flattening,[],[f70])).
% 3.19/0.98  
% 3.19/0.98  fof(f102,plain,(
% 3.19/0.98    ( ! [X2,X0,X1] : (v4_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f71])).
% 3.19/0.98  
% 3.19/0.98  fof(f137,plain,(
% 3.19/0.98    ( ! [X0,X1] : (v4_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.19/0.98    inference(equality_resolution,[],[f102])).
% 3.19/0.98  
% 3.19/0.98  fof(f15,axiom,(
% 3.19/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f45,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.19/0.98    inference(ennf_transformation,[],[f15])).
% 3.19/0.98  
% 3.19/0.98  fof(f105,plain,(
% 3.19/0.98    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f45])).
% 3.19/0.98  
% 3.19/0.98  fof(f16,axiom,(
% 3.19/0.98    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f46,plain,(
% 3.19/0.98    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 3.19/0.98    inference(ennf_transformation,[],[f16])).
% 3.19/0.98  
% 3.19/0.98  fof(f47,plain,(
% 3.19/0.98    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 3.19/0.98    inference(flattening,[],[f46])).
% 3.19/0.98  
% 3.19/0.98  fof(f106,plain,(
% 3.19/0.98    ( ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f47])).
% 3.19/0.98  
% 3.19/0.98  fof(f126,plain,(
% 3.19/0.98    v1_tdlat_3(sK3)),
% 3.19/0.98    inference(cnf_transformation,[],[f84])).
% 3.19/0.98  
% 3.19/0.98  fof(f19,axiom,(
% 3.19/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f51,plain,(
% 3.19/0.98    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.19/0.98    inference(ennf_transformation,[],[f19])).
% 3.19/0.98  
% 3.19/0.98  fof(f73,plain,(
% 3.19/0.98    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.19/0.98    inference(nnf_transformation,[],[f51])).
% 3.19/0.98  
% 3.19/0.98  fof(f112,plain,(
% 3.19/0.98    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.19/0.98    inference(cnf_transformation,[],[f73])).
% 3.19/0.98  
% 3.19/0.98  fof(f129,plain,(
% 3.19/0.98    ~v1_subset_1(sK4,u1_struct_0(sK3)) | v3_tex_2(sK4,sK3)),
% 3.19/0.98    inference(cnf_transformation,[],[f84])).
% 3.19/0.98  
% 3.19/0.98  fof(f24,axiom,(
% 3.19/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f60,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.19/0.98    inference(ennf_transformation,[],[f24])).
% 3.19/0.98  
% 3.19/0.98  fof(f61,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.19/0.98    inference(flattening,[],[f60])).
% 3.19/0.98  
% 3.19/0.98  fof(f121,plain,(
% 3.19/0.98    ( ! [X0,X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f61])).
% 3.19/0.98  
% 3.19/0.98  fof(f125,plain,(
% 3.19/0.98    v2_pre_topc(sK3)),
% 3.19/0.98    inference(cnf_transformation,[],[f84])).
% 3.19/0.98  
% 3.19/0.98  fof(f10,axiom,(
% 3.19/0.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f37,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.19/0.98    inference(ennf_transformation,[],[f10])).
% 3.19/0.98  
% 3.19/0.98  fof(f94,plain,(
% 3.19/0.98    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f37])).
% 3.19/0.98  
% 3.19/0.98  fof(f130,plain,(
% 3.19/0.98    v1_subset_1(sK4,u1_struct_0(sK3)) | ~v3_tex_2(sK4,sK3)),
% 3.19/0.98    inference(cnf_transformation,[],[f84])).
% 3.19/0.98  
% 3.19/0.98  fof(f11,axiom,(
% 3.19/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f29,plain,(
% 3.19/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 3.19/0.98    inference(unused_predicate_definition_removal,[],[f11])).
% 3.19/0.98  
% 3.19/0.98  fof(f38,plain,(
% 3.19/0.98    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 3.19/0.98    inference(ennf_transformation,[],[f29])).
% 3.19/0.98  
% 3.19/0.98  fof(f95,plain,(
% 3.19/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.19/0.98    inference(cnf_transformation,[],[f38])).
% 3.19/0.98  
% 3.19/0.98  fof(f1,axiom,(
% 3.19/0.98    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f85,plain,(
% 3.19/0.98    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f1])).
% 3.19/0.98  
% 3.19/0.98  fof(f2,axiom,(
% 3.19/0.98    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f32,plain,(
% 3.19/0.98    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 3.19/0.98    inference(ennf_transformation,[],[f2])).
% 3.19/0.98  
% 3.19/0.98  fof(f33,plain,(
% 3.19/0.98    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 3.19/0.98    inference(flattening,[],[f32])).
% 3.19/0.98  
% 3.19/0.98  fof(f86,plain,(
% 3.19/0.98    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f33])).
% 3.19/0.98  
% 3.19/0.98  fof(f5,axiom,(
% 3.19/0.98    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f89,plain,(
% 3.19/0.98    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.19/0.98    inference(cnf_transformation,[],[f5])).
% 3.19/0.98  
% 3.19/0.98  fof(f3,axiom,(
% 3.19/0.98    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f87,plain,(
% 3.19/0.98    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f3])).
% 3.19/0.98  
% 3.19/0.98  fof(f133,plain,(
% 3.19/0.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.19/0.98    inference(definition_unfolding,[],[f89,f87])).
% 3.19/0.98  
% 3.19/0.98  fof(f116,plain,(
% 3.19/0.98    ( ! [X0,X1] : (u1_struct_0(sK1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f75])).
% 3.19/0.98  
% 3.19/0.98  fof(f111,plain,(
% 3.19/0.98    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.19/0.98    inference(cnf_transformation,[],[f73])).
% 3.19/0.98  
% 3.19/0.98  fof(f138,plain,(
% 3.19/0.98    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 3.19/0.98    inference(equality_resolution,[],[f111])).
% 3.19/0.98  
% 3.19/0.98  fof(f18,axiom,(
% 3.19/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f50,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.19/0.98    inference(ennf_transformation,[],[f18])).
% 3.19/0.98  
% 3.19/0.98  fof(f72,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.19/0.98    inference(nnf_transformation,[],[f50])).
% 3.19/0.98  
% 3.19/0.98  fof(f110,plain,(
% 3.19/0.98    ( ! [X0,X1] : (v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f72])).
% 3.19/0.98  
% 3.19/0.98  fof(f23,axiom,(
% 3.19/0.98    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f58,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.19/0.98    inference(ennf_transformation,[],[f23])).
% 3.19/0.98  
% 3.19/0.98  fof(f59,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.19/0.98    inference(flattening,[],[f58])).
% 3.19/0.98  
% 3.19/0.98  fof(f120,plain,(
% 3.19/0.98    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f59])).
% 3.19/0.98  
% 3.19/0.98  fof(f26,axiom,(
% 3.19/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f64,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.19/0.98    inference(ennf_transformation,[],[f26])).
% 3.19/0.98  
% 3.19/0.98  fof(f65,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.19/0.98    inference(flattening,[],[f64])).
% 3.19/0.98  
% 3.19/0.98  fof(f123,plain,(
% 3.19/0.98    ( ! [X0,X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f65])).
% 3.19/0.98  
% 3.19/0.98  fof(f6,axiom,(
% 3.19/0.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f90,plain,(
% 3.19/0.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.19/0.98    inference(cnf_transformation,[],[f6])).
% 3.19/0.98  
% 3.19/0.98  fof(f8,axiom,(
% 3.19/0.98    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f92,plain,(
% 3.19/0.98    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 3.19/0.98    inference(cnf_transformation,[],[f8])).
% 3.19/0.98  
% 3.19/0.98  fof(f131,plain,(
% 3.19/0.98    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 3.19/0.98    inference(definition_unfolding,[],[f92,f87])).
% 3.19/0.98  
% 3.19/0.98  fof(f134,plain,(
% 3.19/0.98    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 3.19/0.98    inference(definition_unfolding,[],[f90,f131])).
% 3.19/0.98  
% 3.19/0.98  fof(f4,axiom,(
% 3.19/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f88,plain,(
% 3.19/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.19/0.98    inference(cnf_transformation,[],[f4])).
% 3.19/0.98  
% 3.19/0.98  fof(f132,plain,(
% 3.19/0.98    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 3.19/0.98    inference(definition_unfolding,[],[f88,f131])).
% 3.19/0.98  
% 3.19/0.98  fof(f22,axiom,(
% 3.19/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f56,plain,(
% 3.19/0.98    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.19/0.98    inference(ennf_transformation,[],[f22])).
% 3.19/0.98  
% 3.19/0.98  fof(f57,plain,(
% 3.19/0.98    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.19/0.98    inference(flattening,[],[f56])).
% 3.19/0.98  
% 3.19/0.98  fof(f76,plain,(
% 3.19/0.98    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.19/0.98    inference(nnf_transformation,[],[f57])).
% 3.19/0.98  
% 3.19/0.98  fof(f77,plain,(
% 3.19/0.98    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.19/0.98    inference(rectify,[],[f76])).
% 3.19/0.98  
% 3.19/0.98  fof(f78,plain,(
% 3.19/0.98    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.19/0.98    introduced(choice_axiom,[])).
% 3.19/0.98  
% 3.19/0.98  fof(f79,plain,(
% 3.19/0.98    ! [X0] : (((v1_tdlat_3(X0) | (~v3_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.19/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f77,f78])).
% 3.19/0.98  
% 3.19/0.98  fof(f117,plain,(
% 3.19/0.98    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f79])).
% 3.19/0.98  
% 3.19/0.98  fof(f25,axiom,(
% 3.19/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f62,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.19/0.98    inference(ennf_transformation,[],[f25])).
% 3.19/0.98  
% 3.19/0.98  fof(f63,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.19/0.98    inference(flattening,[],[f62])).
% 3.19/0.98  
% 3.19/0.98  fof(f122,plain,(
% 3.19/0.98    ( ! [X0,X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f63])).
% 3.19/0.98  
% 3.19/0.98  fof(f109,plain,(
% 3.19/0.98    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f72])).
% 3.19/0.98  
% 3.19/0.98  fof(f9,axiom,(
% 3.19/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_subset_1(X1,X0) => ~v1_xboole_0(X1))))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f35,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : ((~v1_xboole_0(X1) | v1_subset_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 3.19/0.98    inference(ennf_transformation,[],[f9])).
% 3.19/0.98  
% 3.19/0.98  fof(f36,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : (~v1_xboole_0(X1) | v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 3.19/0.98    inference(flattening,[],[f35])).
% 3.19/0.98  
% 3.19/0.98  fof(f93,plain,(
% 3.19/0.98    ( ! [X0,X1] : (~v1_xboole_0(X1) | v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f36])).
% 3.19/0.98  
% 3.19/0.98  fof(f13,axiom,(
% 3.19/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f41,plain,(
% 3.19/0.98    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.19/0.98    inference(ennf_transformation,[],[f13])).
% 3.19/0.98  
% 3.19/0.98  fof(f42,plain,(
% 3.19/0.98    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.19/0.98    inference(flattening,[],[f41])).
% 3.19/0.98  
% 3.19/0.98  fof(f68,plain,(
% 3.19/0.98    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v4_pre_topc(sK0(X0),X0) & v3_pre_topc(sK0(X0),X0) & ~v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.19/0.98    introduced(choice_axiom,[])).
% 3.19/0.98  
% 3.19/0.98  fof(f69,plain,(
% 3.19/0.98    ! [X0] : ((v4_pre_topc(sK0(X0),X0) & v3_pre_topc(sK0(X0),X0) & ~v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.19/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f68])).
% 3.19/0.98  
% 3.19/0.98  fof(f98,plain,(
% 3.19/0.98    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f69])).
% 3.19/0.98  
% 3.19/0.98  fof(f99,plain,(
% 3.19/0.98    ( ! [X0] : (~v1_xboole_0(sK0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f69])).
% 3.19/0.98  
% 3.19/0.98  cnf(c_39,negated_conjecture,
% 3.19/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.19/0.98      inference(cnf_transformation,[],[f128]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_3529,plain,
% 3.19/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_28,plain,
% 3.19/0.98      ( m1_pre_topc(sK1(X0,X1),X0)
% 3.19/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.19/0.98      | v2_struct_0(X0)
% 3.19/0.98      | ~ l1_pre_topc(X0)
% 3.19/0.98      | v1_xboole_0(X1) ),
% 3.19/0.98      inference(cnf_transformation,[],[f115]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_40,negated_conjecture,
% 3.19/0.98      ( l1_pre_topc(sK3) ),
% 3.19/0.98      inference(cnf_transformation,[],[f127]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1176,plain,
% 3.19/0.98      ( m1_pre_topc(sK1(X0,X1),X0)
% 3.19/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.19/0.98      | v2_struct_0(X0)
% 3.19/0.98      | v1_xboole_0(X1)
% 3.19/0.98      | sK3 != X0 ),
% 3.19/0.98      inference(resolution_lifted,[status(thm)],[c_28,c_40]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1177,plain,
% 3.19/0.98      ( m1_pre_topc(sK1(sK3,X0),sK3)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.19/0.98      | v2_struct_0(sK3)
% 3.19/0.98      | v1_xboole_0(X0) ),
% 3.19/0.98      inference(unflattening,[status(thm)],[c_1176]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_43,negated_conjecture,
% 3.19/0.98      ( ~ v2_struct_0(sK3) ),
% 3.19/0.98      inference(cnf_transformation,[],[f124]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1181,plain,
% 3.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.19/0.98      | m1_pre_topc(sK1(sK3,X0),sK3)
% 3.19/0.98      | v1_xboole_0(X0) ),
% 3.19/0.98      inference(global_propositional_subsumption,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_1177,c_43]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1182,plain,
% 3.19/0.98      ( m1_pre_topc(sK1(sK3,X0),sK3)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.19/0.98      | v1_xboole_0(X0) ),
% 3.19/0.98      inference(renaming,[status(thm)],[c_1181]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_3524,plain,
% 3.19/0.98      ( m1_pre_topc(sK1(sK3,X0),sK3) = iProver_top
% 3.19/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.19/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_1182]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_4435,plain,
% 3.19/0.98      ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top
% 3.19/0.98      | v1_xboole_0(sK4) = iProver_top ),
% 3.19/0.98      inference(superposition,[status(thm)],[c_3529,c_3524]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_10,plain,
% 3.19/0.98      ( ~ v4_pre_topc(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | ~ l1_pre_topc(X1)
% 3.19/0.98      | k2_pre_topc(X1,X0) = X0 ),
% 3.19/0.98      inference(cnf_transformation,[],[f96]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_21,plain,
% 3.19/0.98      ( v1_borsuk_1(X0,X1)
% 3.19/0.98      | ~ m1_pre_topc(X0,X1)
% 3.19/0.98      | ~ v1_tdlat_3(X1)
% 3.19/0.98      | v2_struct_0(X1)
% 3.19/0.98      | ~ l1_pre_topc(X1)
% 3.19/0.98      | ~ v2_pre_topc(X1) ),
% 3.19/0.98      inference(cnf_transformation,[],[f107]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_17,plain,
% 3.19/0.98      ( ~ v1_borsuk_1(X0,X1)
% 3.19/0.98      | ~ m1_pre_topc(X0,X1)
% 3.19/0.98      | v4_pre_topc(u1_struct_0(X0),X1)
% 3.19/0.98      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | ~ l1_pre_topc(X1)
% 3.19/0.98      | ~ v2_pre_topc(X1) ),
% 3.19/0.98      inference(cnf_transformation,[],[f137]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_18,plain,
% 3.19/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.19/0.98      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | ~ l1_pre_topc(X1) ),
% 3.19/0.98      inference(cnf_transformation,[],[f105]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_263,plain,
% 3.19/0.98      ( v4_pre_topc(u1_struct_0(X0),X1)
% 3.19/0.98      | ~ m1_pre_topc(X0,X1)
% 3.19/0.98      | ~ v1_borsuk_1(X0,X1)
% 3.19/0.98      | ~ l1_pre_topc(X1)
% 3.19/0.98      | ~ v2_pre_topc(X1) ),
% 3.19/0.98      inference(global_propositional_subsumption,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_17,c_18]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_264,plain,
% 3.19/0.98      ( ~ v1_borsuk_1(X0,X1)
% 3.19/0.98      | ~ m1_pre_topc(X0,X1)
% 3.19/0.98      | v4_pre_topc(u1_struct_0(X0),X1)
% 3.19/0.98      | ~ l1_pre_topc(X1)
% 3.19/0.98      | ~ v2_pre_topc(X1) ),
% 3.19/0.98      inference(renaming,[status(thm)],[c_263]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_622,plain,
% 3.19/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.19/0.98      | v4_pre_topc(u1_struct_0(X0),X1)
% 3.19/0.98      | ~ v1_tdlat_3(X1)
% 3.19/0.98      | v2_struct_0(X1)
% 3.19/0.98      | ~ l1_pre_topc(X1)
% 3.19/0.98      | ~ v2_pre_topc(X1) ),
% 3.19/0.98      inference(resolution,[status(thm)],[c_21,c_264]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_19,plain,
% 3.19/0.98      ( ~ v1_tdlat_3(X0) | ~ l1_pre_topc(X0) | v2_pre_topc(X0) ),
% 3.19/0.98      inference(cnf_transformation,[],[f106]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_638,plain,
% 3.19/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.19/0.98      | v4_pre_topc(u1_struct_0(X0),X1)
% 3.19/0.98      | ~ v1_tdlat_3(X1)
% 3.19/0.98      | v2_struct_0(X1)
% 3.19/0.98      | ~ l1_pre_topc(X1) ),
% 3.19/0.98      inference(forward_subsumption_resolution,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_622,c_19]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_678,plain,
% 3.19/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.19/0.98      | ~ v1_tdlat_3(X1)
% 3.19/0.98      | v2_struct_0(X1)
% 3.19/0.98      | ~ l1_pre_topc(X3)
% 3.19/0.98      | ~ l1_pre_topc(X1)
% 3.19/0.98      | X1 != X3
% 3.19/0.98      | k2_pre_topc(X3,X2) = X2
% 3.19/0.98      | u1_struct_0(X0) != X2 ),
% 3.19/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_638]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_679,plain,
% 3.19/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | ~ v1_tdlat_3(X1)
% 3.19/0.98      | v2_struct_0(X1)
% 3.19/0.98      | ~ l1_pre_topc(X1)
% 3.19/0.98      | k2_pre_topc(X1,u1_struct_0(X0)) = u1_struct_0(X0) ),
% 3.19/0.98      inference(unflattening,[status(thm)],[c_678]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_683,plain,
% 3.19/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.19/0.98      | ~ v1_tdlat_3(X1)
% 3.19/0.98      | v2_struct_0(X1)
% 3.19/0.98      | ~ l1_pre_topc(X1)
% 3.19/0.98      | k2_pre_topc(X1,u1_struct_0(X0)) = u1_struct_0(X0) ),
% 3.19/0.98      inference(global_propositional_subsumption,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_679,c_18]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1263,plain,
% 3.19/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.19/0.98      | ~ v1_tdlat_3(X1)
% 3.19/0.98      | v2_struct_0(X1)
% 3.19/0.98      | k2_pre_topc(X1,u1_struct_0(X0)) = u1_struct_0(X0)
% 3.19/0.98      | sK3 != X1 ),
% 3.19/0.98      inference(resolution_lifted,[status(thm)],[c_683,c_40]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1264,plain,
% 3.19/0.98      ( ~ m1_pre_topc(X0,sK3)
% 3.19/0.98      | ~ v1_tdlat_3(sK3)
% 3.19/0.98      | v2_struct_0(sK3)
% 3.19/0.98      | k2_pre_topc(sK3,u1_struct_0(X0)) = u1_struct_0(X0) ),
% 3.19/0.98      inference(unflattening,[status(thm)],[c_1263]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_41,negated_conjecture,
% 3.19/0.98      ( v1_tdlat_3(sK3) ),
% 3.19/0.98      inference(cnf_transformation,[],[f126]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1268,plain,
% 3.19/0.98      ( ~ m1_pre_topc(X0,sK3)
% 3.19/0.98      | k2_pre_topc(sK3,u1_struct_0(X0)) = u1_struct_0(X0) ),
% 3.19/0.98      inference(global_propositional_subsumption,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_1264,c_43,c_41]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_3521,plain,
% 3.19/0.98      ( k2_pre_topc(sK3,u1_struct_0(X0)) = u1_struct_0(X0)
% 3.19/0.98      | m1_pre_topc(X0,sK3) != iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_1268]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_4468,plain,
% 3.19/0.98      ( k2_pre_topc(sK3,u1_struct_0(sK1(sK3,sK4))) = u1_struct_0(sK1(sK3,sK4))
% 3.19/0.98      | v1_xboole_0(sK4) = iProver_top ),
% 3.19/0.98      inference(superposition,[status(thm)],[c_4435,c_3521]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_24,plain,
% 3.19/0.98      ( v1_subset_1(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.19/0.98      | X0 = X1 ),
% 3.19/0.98      inference(cnf_transformation,[],[f112]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_38,negated_conjecture,
% 3.19/0.98      ( v3_tex_2(sK4,sK3) | ~ v1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.19/0.98      inference(cnf_transformation,[],[f129]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_337,plain,
% 3.19/0.98      ( v3_tex_2(sK4,sK3) | ~ v1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.19/0.98      inference(prop_impl,[status(thm)],[c_38]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_951,plain,
% 3.19/0.98      ( v3_tex_2(sK4,sK3)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.19/0.98      | X1 = X0
% 3.19/0.98      | u1_struct_0(sK3) != X1
% 3.19/0.98      | sK4 != X0 ),
% 3.19/0.98      inference(resolution_lifted,[status(thm)],[c_24,c_337]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_952,plain,
% 3.19/0.98      ( v3_tex_2(sK4,sK3)
% 3.19/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.19/0.98      | u1_struct_0(sK3) = sK4 ),
% 3.19/0.98      inference(unflattening,[status(thm)],[c_951]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_954,plain,
% 3.19/0.98      ( v3_tex_2(sK4,sK3) | u1_struct_0(sK3) = sK4 ),
% 3.19/0.98      inference(global_propositional_subsumption,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_952,c_39]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_34,plain,
% 3.19/0.98      ( ~ v3_tex_2(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | v2_struct_0(X1)
% 3.19/0.98      | ~ l1_pre_topc(X1)
% 3.19/0.98      | ~ v2_pre_topc(X1)
% 3.19/0.98      | ~ v1_xboole_0(X0) ),
% 3.19/0.98      inference(cnf_transformation,[],[f121]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1281,plain,
% 3.19/0.98      ( ~ v3_tex_2(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | v2_struct_0(X1)
% 3.19/0.98      | ~ v2_pre_topc(X1)
% 3.19/0.98      | ~ v1_xboole_0(X0)
% 3.19/0.98      | sK3 != X1 ),
% 3.19/0.98      inference(resolution_lifted,[status(thm)],[c_34,c_40]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1282,plain,
% 3.19/0.98      ( ~ v3_tex_2(X0,sK3)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.19/0.98      | v2_struct_0(sK3)
% 3.19/0.98      | ~ v2_pre_topc(sK3)
% 3.19/0.98      | ~ v1_xboole_0(X0) ),
% 3.19/0.98      inference(unflattening,[status(thm)],[c_1281]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_42,negated_conjecture,
% 3.19/0.98      ( v2_pre_topc(sK3) ),
% 3.19/0.98      inference(cnf_transformation,[],[f125]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1286,plain,
% 3.19/0.98      ( ~ v3_tex_2(X0,sK3)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.19/0.98      | ~ v1_xboole_0(X0) ),
% 3.19/0.98      inference(global_propositional_subsumption,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_1282,c_43,c_42]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1556,plain,
% 3.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.19/0.98      | ~ v1_xboole_0(X0)
% 3.19/0.98      | u1_struct_0(sK3) = sK4
% 3.19/0.98      | sK3 != sK3
% 3.19/0.98      | sK4 != X0 ),
% 3.19/0.98      inference(resolution_lifted,[status(thm)],[c_954,c_1286]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1557,plain,
% 3.19/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.19/0.98      | ~ v1_xboole_0(sK4)
% 3.19/0.98      | u1_struct_0(sK3) = sK4 ),
% 3.19/0.98      inference(unflattening,[status(thm)],[c_1556]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1559,plain,
% 3.19/0.98      ( ~ v1_xboole_0(sK4) | u1_struct_0(sK3) = sK4 ),
% 3.19/0.98      inference(global_propositional_subsumption,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_1557,c_39]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_3514,plain,
% 3.19/0.98      ( u1_struct_0(sK3) = sK4 | v1_xboole_0(sK4) != iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_1559]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_5738,plain,
% 3.19/0.98      ( k2_pre_topc(sK3,u1_struct_0(sK1(sK3,sK4))) = u1_struct_0(sK1(sK3,sK4))
% 3.19/0.98      | u1_struct_0(sK3) = sK4 ),
% 3.19/0.98      inference(superposition,[status(thm)],[c_4468,c_3514]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_7,plain,
% 3.19/0.98      ( ~ v1_subset_1(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.19/0.98      | ~ v1_xboole_0(X1) ),
% 3.19/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_37,negated_conjecture,
% 3.19/0.98      ( ~ v3_tex_2(sK4,sK3) | v1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.19/0.98      inference(cnf_transformation,[],[f130]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_339,plain,
% 3.19/0.98      ( ~ v3_tex_2(sK4,sK3) | v1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.19/0.98      inference(prop_impl,[status(thm)],[c_37]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_996,plain,
% 3.19/0.98      ( ~ v3_tex_2(sK4,sK3)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.19/0.98      | ~ v1_xboole_0(X1)
% 3.19/0.98      | u1_struct_0(sK3) != X1
% 3.19/0.98      | sK4 != X0 ),
% 3.19/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_339]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_997,plain,
% 3.19/0.98      ( ~ v3_tex_2(sK4,sK3)
% 3.19/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.19/0.98      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 3.19/0.98      inference(unflattening,[status(thm)],[c_996]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_999,plain,
% 3.19/0.98      ( ~ v3_tex_2(sK4,sK3) | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 3.19/0.98      inference(global_propositional_subsumption,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_997,c_39]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1476,plain,
% 3.19/0.98      ( ~ v1_xboole_0(u1_struct_0(sK3)) | u1_struct_0(sK3) = sK4 ),
% 3.19/0.98      inference(resolution,[status(thm)],[c_954,c_999]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1477,plain,
% 3.19/0.98      ( u1_struct_0(sK3) = sK4
% 3.19/0.98      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_1476]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_8,plain,
% 3.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.19/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_0,plain,
% 3.19/0.98      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.19/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1,plain,
% 3.19/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | v1_xboole_0(X0) ),
% 3.19/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_556,plain,
% 3.19/0.98      ( ~ r1_tarski(X0,X1)
% 3.19/0.98      | v1_xboole_0(X0)
% 3.19/0.98      | X0 != X2
% 3.19/0.98      | k1_xboole_0 != X1 ),
% 3.19/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_557,plain,
% 3.19/0.98      ( ~ r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0) ),
% 3.19/0.98      inference(unflattening,[status(thm)],[c_556]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_571,plain,
% 3.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.19/0.98      | v1_xboole_0(X2)
% 3.19/0.98      | X2 != X0
% 3.19/0.98      | k1_xboole_0 != X1 ),
% 3.19/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_557]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_572,plain,
% 3.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0) ),
% 3.19/0.98      inference(unflattening,[status(thm)],[c_571]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_3731,plain,
% 3.19/0.98      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 3.19/0.98      | v1_xboole_0(k1_xboole_0) ),
% 3.19/0.98      inference(instantiation,[status(thm)],[c_572]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_3733,plain,
% 3.19/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.19/0.98      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_3731]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_3,plain,
% 3.19/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.19/0.98      inference(cnf_transformation,[],[f133]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_3732,plain,
% 3.19/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 3.19/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_3735,plain,
% 3.19/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_3732]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_27,plain,
% 3.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | v2_struct_0(X1)
% 3.19/0.98      | ~ l1_pre_topc(X1)
% 3.19/0.98      | v1_xboole_0(X0)
% 3.19/0.98      | u1_struct_0(sK1(X1,X0)) = X0 ),
% 3.19/0.98      inference(cnf_transformation,[],[f116]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1323,plain,
% 3.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | v2_struct_0(X1)
% 3.19/0.98      | v1_xboole_0(X0)
% 3.19/0.98      | u1_struct_0(sK1(X1,X0)) = X0
% 3.19/0.98      | sK3 != X1 ),
% 3.19/0.98      inference(resolution_lifted,[status(thm)],[c_27,c_40]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1324,plain,
% 3.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.19/0.98      | v2_struct_0(sK3)
% 3.19/0.98      | v1_xboole_0(X0)
% 3.19/0.98      | u1_struct_0(sK1(sK3,X0)) = X0 ),
% 3.19/0.98      inference(unflattening,[status(thm)],[c_1323]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1328,plain,
% 3.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.19/0.98      | v1_xboole_0(X0)
% 3.19/0.98      | u1_struct_0(sK1(sK3,X0)) = X0 ),
% 3.19/0.98      inference(global_propositional_subsumption,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_1324,c_43]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_3520,plain,
% 3.19/0.98      ( u1_struct_0(sK1(sK3,X0)) = X0
% 3.19/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.19/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_1328]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_4358,plain,
% 3.19/0.98      ( u1_struct_0(sK1(sK3,sK4)) = sK4
% 3.19/0.98      | v1_xboole_0(sK4) = iProver_top ),
% 3.19/0.98      inference(superposition,[status(thm)],[c_3529,c_3520]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_3532,plain,
% 3.19/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_916,plain,
% 3.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 3.19/0.98      inference(resolution,[status(thm)],[c_24,c_7]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_3526,plain,
% 3.19/0.98      ( X0 = X1
% 3.19/0.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 3.19/0.98      | v1_xboole_0(X0) != iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_916]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_5384,plain,
% 3.19/0.98      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.19/0.98      inference(superposition,[status(thm)],[c_3532,c_3526]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_5516,plain,
% 3.19/0.98      ( u1_struct_0(sK1(sK3,sK4)) = sK4 | sK4 = k1_xboole_0 ),
% 3.19/0.98      inference(superposition,[status(thm)],[c_4358,c_5384]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_5737,plain,
% 3.19/0.98      ( k2_pre_topc(sK3,u1_struct_0(sK1(sK3,sK4))) = u1_struct_0(sK1(sK3,sK4))
% 3.19/0.98      | sK4 = k1_xboole_0 ),
% 3.19/0.98      inference(superposition,[status(thm)],[c_4468,c_5384]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_7334,plain,
% 3.19/0.98      ( u1_struct_0(sK1(sK3,sK4)) = k2_pre_topc(sK3,sK4)
% 3.19/0.98      | sK4 = k1_xboole_0 ),
% 3.19/0.98      inference(superposition,[status(thm)],[c_5516,c_5737]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_7567,plain,
% 3.19/0.98      ( k2_pre_topc(sK3,sK4) = sK4 | sK4 = k1_xboole_0 ),
% 3.19/0.98      inference(superposition,[status(thm)],[c_7334,c_5516]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_25,plain,
% 3.19/0.98      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 3.19/0.98      inference(cnf_transformation,[],[f138]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1010,plain,
% 3.19/0.98      ( ~ v3_tex_2(sK4,sK3)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(X0))
% 3.19/0.98      | u1_struct_0(sK3) != X0
% 3.19/0.98      | sK4 != X0 ),
% 3.19/0.98      inference(resolution_lifted,[status(thm)],[c_25,c_339]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1011,plain,
% 3.19/0.98      ( ~ v3_tex_2(sK4,sK3)
% 3.19/0.98      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.19/0.98      | sK4 != u1_struct_0(sK3) ),
% 3.19/0.98      inference(unflattening,[status(thm)],[c_1010]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_22,plain,
% 3.19/0.98      ( v1_tops_1(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | ~ l1_pre_topc(X1)
% 3.19/0.98      | k2_pre_topc(X1,X0) != u1_struct_0(X1) ),
% 3.19/0.98      inference(cnf_transformation,[],[f110]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_33,plain,
% 3.19/0.98      ( v2_tex_2(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | ~ v1_tdlat_3(X1)
% 3.19/0.98      | v2_struct_0(X1)
% 3.19/0.98      | ~ l1_pre_topc(X1)
% 3.19/0.98      | ~ v2_pre_topc(X1) ),
% 3.19/0.98      inference(cnf_transformation,[],[f120]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_36,plain,
% 3.19/0.98      ( v3_tex_2(X0,X1)
% 3.19/0.98      | ~ v2_tex_2(X0,X1)
% 3.19/0.98      | ~ v1_tops_1(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | v2_struct_0(X1)
% 3.19/0.98      | ~ l1_pre_topc(X1)
% 3.19/0.98      | ~ v2_pre_topc(X1) ),
% 3.19/0.98      inference(cnf_transformation,[],[f123]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_586,plain,
% 3.19/0.98      ( v3_tex_2(X0,X1)
% 3.19/0.98      | ~ v1_tops_1(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | ~ v1_tdlat_3(X1)
% 3.19/0.98      | v2_struct_0(X1)
% 3.19/0.98      | ~ l1_pre_topc(X1)
% 3.19/0.98      | ~ v2_pre_topc(X1) ),
% 3.19/0.98      inference(resolution,[status(thm)],[c_33,c_36]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_604,plain,
% 3.19/0.98      ( v3_tex_2(X0,X1)
% 3.19/0.98      | ~ v1_tops_1(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | ~ v1_tdlat_3(X1)
% 3.19/0.98      | v2_struct_0(X1)
% 3.19/0.98      | ~ l1_pre_topc(X1) ),
% 3.19/0.98      inference(forward_subsumption_resolution,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_586,c_19]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1077,plain,
% 3.19/0.98      ( v3_tex_2(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | ~ v1_tdlat_3(X1)
% 3.19/0.98      | v2_struct_0(X1)
% 3.19/0.98      | ~ l1_pre_topc(X1)
% 3.19/0.98      | k2_pre_topc(X1,X0) != u1_struct_0(X1) ),
% 3.19/0.98      inference(resolution,[status(thm)],[c_22,c_604]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1221,plain,
% 3.19/0.98      ( v3_tex_2(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | ~ v1_tdlat_3(X1)
% 3.19/0.98      | v2_struct_0(X1)
% 3.19/0.98      | k2_pre_topc(X1,X0) != u1_struct_0(X1)
% 3.19/0.98      | sK3 != X1 ),
% 3.19/0.98      inference(resolution_lifted,[status(thm)],[c_1077,c_40]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1222,plain,
% 3.19/0.98      ( v3_tex_2(X0,sK3)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.19/0.98      | ~ v1_tdlat_3(sK3)
% 3.19/0.98      | v2_struct_0(sK3)
% 3.19/0.98      | k2_pre_topc(sK3,X0) != u1_struct_0(sK3) ),
% 3.19/0.98      inference(unflattening,[status(thm)],[c_1221]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1226,plain,
% 3.19/0.98      ( v3_tex_2(X0,sK3)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.19/0.98      | k2_pre_topc(sK3,X0) != u1_struct_0(sK3) ),
% 3.19/0.98      inference(global_propositional_subsumption,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_1222,c_43,c_41]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1581,plain,
% 3.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.19/0.98      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.19/0.98      | k2_pre_topc(sK3,X0) != u1_struct_0(sK3)
% 3.19/0.98      | u1_struct_0(sK3) != sK4
% 3.19/0.98      | sK3 != sK3
% 3.19/0.98      | sK4 != X0 ),
% 3.19/0.98      inference(resolution_lifted,[status(thm)],[c_1011,c_1226]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1582,plain,
% 3.19/0.98      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.19/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.19/0.98      | k2_pre_topc(sK3,sK4) != u1_struct_0(sK3)
% 3.19/0.98      | u1_struct_0(sK3) != sK4 ),
% 3.19/0.98      inference(unflattening,[status(thm)],[c_1581]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1584,plain,
% 3.19/0.98      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.19/0.98      | k2_pre_topc(sK3,sK4) != u1_struct_0(sK3)
% 3.19/0.98      | u1_struct_0(sK3) != sK4 ),
% 3.19/0.98      inference(global_propositional_subsumption,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_1582,c_39]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_3513,plain,
% 3.19/0.98      ( k2_pre_topc(sK3,sK4) != u1_struct_0(sK3)
% 3.19/0.98      | u1_struct_0(sK3) != sK4
% 3.19/0.98      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_1584]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_4,plain,
% 3.19/0.98      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
% 3.19/0.98      inference(cnf_transformation,[],[f134]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_3531,plain,
% 3.19/0.98      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_2,plain,
% 3.19/0.98      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 3.19/0.98      inference(cnf_transformation,[],[f132]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_3545,plain,
% 3.19/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.19/0.98      inference(light_normalisation,[status(thm)],[c_3531,c_2]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_3632,plain,
% 3.19/0.98      ( k2_pre_topc(sK3,sK4) != u1_struct_0(sK3)
% 3.19/0.98      | u1_struct_0(sK3) != sK4 ),
% 3.19/0.98      inference(forward_subsumption_resolution,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_3513,c_3545]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_9297,plain,
% 3.19/0.98      ( u1_struct_0(sK3) != sK4 | sK4 = k1_xboole_0 ),
% 3.19/0.98      inference(superposition,[status(thm)],[c_7567,c_3632]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_32,plain,
% 3.19/0.98      ( v3_pre_topc(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | ~ v1_tdlat_3(X1)
% 3.19/0.98      | ~ l1_pre_topc(X1)
% 3.19/0.98      | ~ v2_pre_topc(X1) ),
% 3.19/0.98      inference(cnf_transformation,[],[f117]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_35,plain,
% 3.19/0.98      ( ~ v3_tex_2(X0,X1)
% 3.19/0.98      | v1_tops_1(X0,X1)
% 3.19/0.98      | ~ v3_pre_topc(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | v2_struct_0(X1)
% 3.19/0.98      | ~ l1_pre_topc(X1)
% 3.19/0.98      | ~ v2_pre_topc(X1) ),
% 3.19/0.98      inference(cnf_transformation,[],[f122]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_807,plain,
% 3.19/0.98      ( ~ v3_tex_2(X0,X1)
% 3.19/0.98      | v1_tops_1(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | ~ v1_tdlat_3(X1)
% 3.19/0.98      | v2_struct_0(X1)
% 3.19/0.98      | ~ l1_pre_topc(X1)
% 3.19/0.98      | ~ v2_pre_topc(X1) ),
% 3.19/0.98      inference(resolution,[status(thm)],[c_32,c_35]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_825,plain,
% 3.19/0.98      ( ~ v3_tex_2(X0,X1)
% 3.19/0.98      | v1_tops_1(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | ~ v1_tdlat_3(X1)
% 3.19/0.98      | v2_struct_0(X1)
% 3.19/0.98      | ~ l1_pre_topc(X1) ),
% 3.19/0.98      inference(forward_subsumption_resolution,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_807,c_19]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_23,plain,
% 3.19/0.98      ( ~ v1_tops_1(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | ~ l1_pre_topc(X1)
% 3.19/0.98      | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
% 3.19/0.98      inference(cnf_transformation,[],[f109]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1054,plain,
% 3.19/0.98      ( ~ v3_tex_2(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | ~ v1_tdlat_3(X1)
% 3.19/0.98      | v2_struct_0(X1)
% 3.19/0.98      | ~ l1_pre_topc(X1)
% 3.19/0.98      | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
% 3.19/0.98      inference(resolution,[status(thm)],[c_825,c_23]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1242,plain,
% 3.19/0.98      ( ~ v3_tex_2(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | ~ v1_tdlat_3(X1)
% 3.19/0.98      | v2_struct_0(X1)
% 3.19/0.98      | k2_pre_topc(X1,X0) = u1_struct_0(X1)
% 3.19/0.98      | sK3 != X1 ),
% 3.19/0.98      inference(resolution_lifted,[status(thm)],[c_1054,c_40]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1243,plain,
% 3.19/0.98      ( ~ v3_tex_2(X0,sK3)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.19/0.98      | ~ v1_tdlat_3(sK3)
% 3.19/0.98      | v2_struct_0(sK3)
% 3.19/0.98      | k2_pre_topc(sK3,X0) = u1_struct_0(sK3) ),
% 3.19/0.98      inference(unflattening,[status(thm)],[c_1242]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1247,plain,
% 3.19/0.98      ( ~ v3_tex_2(X0,sK3)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.19/0.98      | k2_pre_topc(sK3,X0) = u1_struct_0(sK3) ),
% 3.19/0.98      inference(global_propositional_subsumption,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_1243,c_43,c_41]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1570,plain,
% 3.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.19/0.98      | k2_pre_topc(sK3,X0) = u1_struct_0(sK3)
% 3.19/0.98      | u1_struct_0(sK3) = sK4
% 3.19/0.98      | sK3 != sK3
% 3.19/0.98      | sK4 != X0 ),
% 3.19/0.98      inference(resolution_lifted,[status(thm)],[c_954,c_1247]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1571,plain,
% 3.19/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.19/0.98      | k2_pre_topc(sK3,sK4) = u1_struct_0(sK3)
% 3.19/0.98      | u1_struct_0(sK3) = sK4 ),
% 3.19/0.98      inference(unflattening,[status(thm)],[c_1570]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1573,plain,
% 3.19/0.98      ( k2_pre_topc(sK3,sK4) = u1_struct_0(sK3)
% 3.19/0.98      | u1_struct_0(sK3) = sK4 ),
% 3.19/0.98      inference(global_propositional_subsumption,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_1571,c_39]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_9300,plain,
% 3.19/0.98      ( u1_struct_0(sK3) = sK4 | sK4 = k1_xboole_0 ),
% 3.19/0.98      inference(superposition,[status(thm)],[c_7567,c_1573]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_9307,plain,
% 3.19/0.98      ( sK4 = k1_xboole_0 ),
% 3.19/0.98      inference(forward_subsumption_resolution,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_9297,c_9300]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_6,plain,
% 3.19/0.98      ( v1_subset_1(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.19/0.98      | ~ v1_xboole_0(X0)
% 3.19/0.98      | v1_xboole_0(X1) ),
% 3.19/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_965,plain,
% 3.19/0.98      ( v3_tex_2(sK4,sK3)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.19/0.98      | ~ v1_xboole_0(X0)
% 3.19/0.98      | v1_xboole_0(X1)
% 3.19/0.98      | u1_struct_0(sK3) != X1
% 3.19/0.98      | sK4 != X0 ),
% 3.19/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_337]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_966,plain,
% 3.19/0.98      ( v3_tex_2(sK4,sK3)
% 3.19/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.19/0.98      | v1_xboole_0(u1_struct_0(sK3))
% 3.19/0.98      | ~ v1_xboole_0(sK4) ),
% 3.19/0.98      inference(unflattening,[status(thm)],[c_965]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_968,plain,
% 3.19/0.98      ( v3_tex_2(sK4,sK3)
% 3.19/0.98      | v1_xboole_0(u1_struct_0(sK3))
% 3.19/0.98      | ~ v1_xboole_0(sK4) ),
% 3.19/0.98      inference(global_propositional_subsumption,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_966,c_39]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1540,plain,
% 3.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.19/0.98      | ~ v1_xboole_0(X0)
% 3.19/0.98      | v1_xboole_0(u1_struct_0(sK3))
% 3.19/0.98      | ~ v1_xboole_0(sK4)
% 3.19/0.98      | sK3 != sK3
% 3.19/0.98      | sK4 != X0 ),
% 3.19/0.98      inference(resolution_lifted,[status(thm)],[c_968,c_1286]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1541,plain,
% 3.19/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.19/0.98      | v1_xboole_0(u1_struct_0(sK3))
% 3.19/0.98      | ~ v1_xboole_0(sK4) ),
% 3.19/0.98      inference(unflattening,[status(thm)],[c_1540]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1543,plain,
% 3.19/0.98      ( v1_xboole_0(u1_struct_0(sK3)) | ~ v1_xboole_0(sK4) ),
% 3.19/0.98      inference(global_propositional_subsumption,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_1541,c_39]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_3515,plain,
% 3.19/0.98      ( v1_xboole_0(u1_struct_0(sK3)) = iProver_top
% 3.19/0.98      | v1_xboole_0(sK4) != iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_1543]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_9341,plain,
% 3.19/0.98      ( v1_xboole_0(u1_struct_0(sK3)) = iProver_top
% 3.19/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.19/0.98      inference(demodulation,[status(thm)],[c_9307,c_3515]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_9447,plain,
% 3.19/0.98      ( u1_struct_0(sK3) = sK4 ),
% 3.19/0.98      inference(global_propositional_subsumption,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_5738,c_1477,c_3733,c_3735,c_9341]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_9449,plain,
% 3.19/0.98      ( u1_struct_0(sK3) = k1_xboole_0 ),
% 3.19/0.98      inference(light_normalisation,[status(thm)],[c_9447,c_9307]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_14,plain,
% 3.19/0.98      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.19/0.98      | v2_struct_0(X0)
% 3.19/0.98      | ~ l1_pre_topc(X0)
% 3.19/0.98      | ~ v2_pre_topc(X0) ),
% 3.19/0.98      inference(cnf_transformation,[],[f98]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1199,plain,
% 3.19/0.98      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.19/0.98      | v2_struct_0(X0)
% 3.19/0.98      | ~ v2_pre_topc(X0)
% 3.19/0.98      | sK3 != X0 ),
% 3.19/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_40]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1200,plain,
% 3.19/0.98      ( m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.19/0.98      | v2_struct_0(sK3)
% 3.19/0.98      | ~ v2_pre_topc(sK3) ),
% 3.19/0.98      inference(unflattening,[status(thm)],[c_1199]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_108,plain,
% 3.19/0.98      ( m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.19/0.98      | v2_struct_0(sK3)
% 3.19/0.98      | ~ l1_pre_topc(sK3)
% 3.19/0.98      | ~ v2_pre_topc(sK3) ),
% 3.19/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1202,plain,
% 3.19/0.98      ( m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.19/0.98      inference(global_propositional_subsumption,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_1200,c_43,c_42,c_40,c_108]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_3523,plain,
% 3.19/0.98      ( m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_1202]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_9472,plain,
% 3.19/0.98      ( m1_subset_1(sK0(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.19/0.98      inference(demodulation,[status(thm)],[c_9449,c_3523]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_3528,plain,
% 3.19/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.19/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_572]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_9735,plain,
% 3.19/0.98      ( v1_xboole_0(sK0(sK3)) = iProver_top ),
% 3.19/0.98      inference(superposition,[status(thm)],[c_9472,c_3528]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_13,plain,
% 3.19/0.98      ( v2_struct_0(X0)
% 3.19/0.98      | ~ l1_pre_topc(X0)
% 3.19/0.98      | ~ v2_pre_topc(X0)
% 3.19/0.98      | ~ v1_xboole_0(sK0(X0)) ),
% 3.19/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_110,plain,
% 3.19/0.98      ( v2_struct_0(X0) = iProver_top
% 3.19/0.98      | l1_pre_topc(X0) != iProver_top
% 3.19/0.98      | v2_pre_topc(X0) != iProver_top
% 3.19/0.98      | v1_xboole_0(sK0(X0)) != iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_112,plain,
% 3.19/0.98      ( v2_struct_0(sK3) = iProver_top
% 3.19/0.98      | l1_pre_topc(sK3) != iProver_top
% 3.19/0.98      | v2_pre_topc(sK3) != iProver_top
% 3.19/0.98      | v1_xboole_0(sK0(sK3)) != iProver_top ),
% 3.19/0.98      inference(instantiation,[status(thm)],[c_110]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_47,plain,
% 3.19/0.98      ( l1_pre_topc(sK3) = iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_45,plain,
% 3.19/0.98      ( v2_pre_topc(sK3) = iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_44,plain,
% 3.19/0.98      ( v2_struct_0(sK3) != iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(contradiction,plain,
% 3.19/0.98      ( $false ),
% 3.19/0.98      inference(minisat,[status(thm)],[c_9735,c_112,c_47,c_45,c_44]) ).
% 3.19/0.98  
% 3.19/0.98  
% 3.19/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.19/0.98  
% 3.19/0.98  ------                               Statistics
% 3.19/0.98  
% 3.19/0.98  ------ General
% 3.19/0.98  
% 3.19/0.98  abstr_ref_over_cycles:                  0
% 3.19/0.98  abstr_ref_under_cycles:                 0
% 3.19/0.98  gc_basic_clause_elim:                   0
% 3.19/0.98  forced_gc_time:                         0
% 3.19/0.98  parsing_time:                           0.009
% 3.19/0.98  unif_index_cands_time:                  0.
% 3.19/0.98  unif_index_add_time:                    0.
% 3.19/0.98  orderings_time:                         0.
% 3.19/0.98  out_proof_time:                         0.012
% 3.19/0.98  total_time:                             0.238
% 3.19/0.98  num_of_symbols:                         57
% 3.19/0.98  num_of_terms:                           5710
% 3.19/0.98  
% 3.19/0.98  ------ Preprocessing
% 3.19/0.98  
% 3.19/0.98  num_of_splits:                          0
% 3.19/0.98  num_of_split_atoms:                     0
% 3.19/0.98  num_of_reused_defs:                     0
% 3.19/0.98  num_eq_ax_congr_red:                    21
% 3.19/0.98  num_of_sem_filtered_clauses:            1
% 3.19/0.98  num_of_subtypes:                        0
% 3.19/0.98  monotx_restored_types:                  0
% 3.19/0.98  sat_num_of_epr_types:                   0
% 3.19/0.98  sat_num_of_non_cyclic_types:            0
% 3.19/0.98  sat_guarded_non_collapsed_types:        0
% 3.19/0.98  num_pure_diseq_elim:                    0
% 3.19/0.98  simp_replaced_by:                       0
% 3.19/0.98  res_preprocessed:                       144
% 3.19/0.98  prep_upred:                             0
% 3.19/0.98  prep_unflattend:                        144
% 3.19/0.98  smt_new_axioms:                         0
% 3.19/0.98  pred_elim_cands:                        3
% 3.19/0.98  pred_elim:                              13
% 3.19/0.98  pred_elim_cl:                           17
% 3.19/0.98  pred_elim_cycles:                       18
% 3.19/0.98  merged_defs:                            2
% 3.19/0.98  merged_defs_ncl:                        0
% 3.19/0.98  bin_hyper_res:                          2
% 3.19/0.98  prep_cycles:                            4
% 3.19/0.98  pred_elim_time:                         0.039
% 3.19/0.98  splitting_time:                         0.
% 3.19/0.98  sem_filter_time:                        0.
% 3.19/0.98  monotx_time:                            0.
% 3.19/0.98  subtype_inf_time:                       0.
% 3.19/0.98  
% 3.19/0.98  ------ Problem properties
% 3.19/0.98  
% 3.19/0.98  clauses:                                26
% 3.19/0.98  conjectures:                            1
% 3.19/0.98  epr:                                    0
% 3.19/0.98  horn:                                   22
% 3.19/0.98  ground:                                 13
% 3.19/0.98  unary:                                  7
% 3.19/0.98  binary:                                 11
% 3.19/0.98  lits:                                   54
% 3.19/0.98  lits_eq:                                20
% 3.19/0.98  fd_pure:                                0
% 3.19/0.98  fd_pseudo:                              0
% 3.19/0.98  fd_cond:                                0
% 3.19/0.98  fd_pseudo_cond:                         2
% 3.19/0.99  ac_symbols:                             0
% 3.19/0.99  
% 3.19/0.99  ------ Propositional Solver
% 3.19/0.99  
% 3.19/0.99  prop_solver_calls:                      27
% 3.19/0.99  prop_fast_solver_calls:                 1614
% 3.19/0.99  smt_solver_calls:                       0
% 3.19/0.99  smt_fast_solver_calls:                  0
% 3.19/0.99  prop_num_of_clauses:                    2770
% 3.19/0.99  prop_preprocess_simplified:             7238
% 3.19/0.99  prop_fo_subsumed:                       95
% 3.19/0.99  prop_solver_time:                       0.
% 3.19/0.99  smt_solver_time:                        0.
% 3.19/0.99  smt_fast_solver_time:                   0.
% 3.19/0.99  prop_fast_solver_time:                  0.
% 3.19/0.99  prop_unsat_core_time:                   0.
% 3.19/0.99  
% 3.19/0.99  ------ QBF
% 3.19/0.99  
% 3.19/0.99  qbf_q_res:                              0
% 3.19/0.99  qbf_num_tautologies:                    0
% 3.19/0.99  qbf_prep_cycles:                        0
% 3.19/0.99  
% 3.19/0.99  ------ BMC1
% 3.19/0.99  
% 3.19/0.99  bmc1_current_bound:                     -1
% 3.19/0.99  bmc1_last_solved_bound:                 -1
% 3.19/0.99  bmc1_unsat_core_size:                   -1
% 3.19/0.99  bmc1_unsat_core_parents_size:           -1
% 3.19/0.99  bmc1_merge_next_fun:                    0
% 3.19/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.19/0.99  
% 3.19/0.99  ------ Instantiation
% 3.19/0.99  
% 3.19/0.99  inst_num_of_clauses:                    824
% 3.19/0.99  inst_num_in_passive:                    197
% 3.19/0.99  inst_num_in_active:                     451
% 3.19/0.99  inst_num_in_unprocessed:                177
% 3.19/0.99  inst_num_of_loops:                      490
% 3.19/0.99  inst_num_of_learning_restarts:          0
% 3.19/0.99  inst_num_moves_active_passive:          36
% 3.19/0.99  inst_lit_activity:                      0
% 3.19/0.99  inst_lit_activity_moves:                0
% 3.19/0.99  inst_num_tautologies:                   0
% 3.19/0.99  inst_num_prop_implied:                  0
% 3.19/0.99  inst_num_existing_simplified:           0
% 3.19/0.99  inst_num_eq_res_simplified:             0
% 3.19/0.99  inst_num_child_elim:                    0
% 3.19/0.99  inst_num_of_dismatching_blockings:      450
% 3.19/0.99  inst_num_of_non_proper_insts:           866
% 3.19/0.99  inst_num_of_duplicates:                 0
% 3.19/0.99  inst_inst_num_from_inst_to_res:         0
% 3.19/0.99  inst_dismatching_checking_time:         0.
% 3.19/0.99  
% 3.19/0.99  ------ Resolution
% 3.19/0.99  
% 3.19/0.99  res_num_of_clauses:                     0
% 3.19/0.99  res_num_in_passive:                     0
% 3.19/0.99  res_num_in_active:                      0
% 3.19/0.99  res_num_of_loops:                       148
% 3.19/0.99  res_forward_subset_subsumed:            119
% 3.19/0.99  res_backward_subset_subsumed:           5
% 3.19/0.99  res_forward_subsumed:                   4
% 3.19/0.99  res_backward_subsumed:                  3
% 3.19/0.99  res_forward_subsumption_resolution:     4
% 3.19/0.99  res_backward_subsumption_resolution:    0
% 3.19/0.99  res_clause_to_clause_subsumption:       544
% 3.19/0.99  res_orphan_elimination:                 0
% 3.19/0.99  res_tautology_del:                      75
% 3.19/0.99  res_num_eq_res_simplified:              1
% 3.19/0.99  res_num_sel_changes:                    0
% 3.19/0.99  res_moves_from_active_to_pass:          0
% 3.19/0.99  
% 3.19/0.99  ------ Superposition
% 3.19/0.99  
% 3.19/0.99  sup_time_total:                         0.
% 3.19/0.99  sup_time_generating:                    0.
% 3.19/0.99  sup_time_sim_full:                      0.
% 3.19/0.99  sup_time_sim_immed:                     0.
% 3.19/0.99  
% 3.19/0.99  sup_num_of_clauses:                     96
% 3.19/0.99  sup_num_in_active:                      25
% 3.19/0.99  sup_num_in_passive:                     71
% 3.19/0.99  sup_num_of_loops:                       96
% 3.19/0.99  sup_fw_superposition:                   160
% 3.19/0.99  sup_bw_superposition:                   133
% 3.19/0.99  sup_immediate_simplified:               111
% 3.19/0.99  sup_given_eliminated:                   1
% 3.19/0.99  comparisons_done:                       0
% 3.19/0.99  comparisons_avoided:                    39
% 3.19/0.99  
% 3.19/0.99  ------ Simplifications
% 3.19/0.99  
% 3.19/0.99  
% 3.19/0.99  sim_fw_subset_subsumed:                 57
% 3.19/0.99  sim_bw_subset_subsumed:                 22
% 3.19/0.99  sim_fw_subsumed:                        28
% 3.19/0.99  sim_bw_subsumed:                        12
% 3.19/0.99  sim_fw_subsumption_res:                 2
% 3.19/0.99  sim_bw_subsumption_res:                 0
% 3.19/0.99  sim_tautology_del:                      17
% 3.19/0.99  sim_eq_tautology_del:                   24
% 3.19/0.99  sim_eq_res_simp:                        0
% 3.19/0.99  sim_fw_demodulated:                     11
% 3.19/0.99  sim_bw_demodulated:                     61
% 3.19/0.99  sim_light_normalised:                   17
% 3.19/0.99  sim_joinable_taut:                      0
% 3.19/0.99  sim_joinable_simp:                      0
% 3.19/0.99  sim_ac_normalised:                      0
% 3.19/0.99  sim_smt_subsumption:                    0
% 3.19/0.99  
%------------------------------------------------------------------------------
