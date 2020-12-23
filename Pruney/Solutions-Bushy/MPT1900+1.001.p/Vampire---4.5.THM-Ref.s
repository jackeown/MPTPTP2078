%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1900+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 142 expanded)
%              Number of leaves         :   13 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  282 (1044 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f93,plain,(
    $false ),
    inference(subsumption_resolution,[],[f92,f42])).

fof(f42,plain,(
    ~ v5_pre_topc(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ v5_pre_topc(sK6,sK4,sK5)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    & v1_funct_1(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & l1_pre_topc(sK4)
    & v1_tdlat_3(sK4)
    & v2_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f7,f21,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v5_pre_topc(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,sK4,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK4)
      & v1_tdlat_3(sK4)
      & v2_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v5_pre_topc(X2,sK4,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ~ v5_pre_topc(X2,sK4,sK5)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
          & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(sK5))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( ~ v5_pre_topc(X2,sK4,sK5)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
        & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(sK5))
        & v1_funct_1(X2) )
   => ( ~ v5_pre_topc(sK6,sK4,sK5)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
      & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => v5_pre_topc(X2,X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => v5_pre_topc(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_tex_2)).

fof(f92,plain,(
    v5_pre_topc(sK6,sK4,sK5) ),
    inference(subsumption_resolution,[],[f90,f82])).

fof(f82,plain,(
    sP0(sK4,sK6,sK5) ),
    inference(subsumption_resolution,[],[f81,f63])).

fof(f63,plain,(
    sP2(sK4) ),
    inference(subsumption_resolution,[],[f62,f35])).

fof(f35,plain,(
    v1_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f22])).

fof(f62,plain,
    ( ~ v1_tdlat_3(sK4)
    | sP2(sK4) ),
    inference(resolution,[],[f59,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ sP3(X0)
      | ~ v1_tdlat_3(X0)
      | sP2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ~ sP2(X0) )
        & ( sP2(X0)
          | ~ v1_tdlat_3(X0) ) )
      | ~ sP3(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> sP2(X0) )
      | ~ sP3(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f59,plain,(
    sP3(sK4) ),
    inference(subsumption_resolution,[],[f57,f36])).

fof(f36,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,
    ( ~ l1_pre_topc(sK4)
    | sP3(sK4) ),
    inference(resolution,[],[f55,f34])).

fof(f34,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | sP3(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( sP3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f11,f17,f16])).

fof(f16,plain,(
    ! [X0] :
      ( sP2(X0)
    <=> ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tdlat_3)).

fof(f81,plain,
    ( ~ sP2(sK4)
    | sP0(sK4,sK6,sK5) ),
    inference(resolution,[],[f79,f41])).

fof(f41,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f22])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ sP2(X1)
      | sP0(X1,X0,X2) ) ),
    inference(resolution,[],[f78,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK7(X0,X1,X2)),X0)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK7(X0,X1,X2)),X0)
          & v4_pre_topc(sK7(X0,X1,X2),X2)
          & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ! [X4] :
            ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0)
            | ~ v4_pre_topc(X4,X2)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X3),X0)
          & v4_pre_topc(X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK7(X0,X1,X2)),X0)
        & v4_pre_topc(sK7(X0,X1,X2),X2)
        & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X3),X0)
            & v4_pre_topc(X3,X2)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ! [X4] :
            ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0)
            | ~ v4_pre_topc(X4,X2)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X2,X1] :
      ( ( sP0(X0,X2,X1)
        | ? [X3] :
            ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
            & v4_pre_topc(X3,X1)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X3] :
            ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
            | ~ v4_pre_topc(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X2,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X2,X1] :
      ( sP0(X0,X2,X1)
    <=> ! [X3] :
          ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          | ~ v4_pre_topc(X3,X1)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(X1),X2,X0,X3),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),X2)))
      | ~ sP2(X1) ) ),
    inference(resolution,[],[f56,f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X2,X0)
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( sP2(X0)
        | ( ~ v4_pre_topc(sK8(X0),X0)
          & m1_subset_1(sK8(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( v4_pre_topc(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP2(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f31,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK8(X0),X0)
        & m1_subset_1(sK8(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( sP2(X0)
        | ? [X1] :
            ( ~ v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( v4_pre_topc(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP2(X0) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( sP2(X0)
        | ? [X1] :
            ( ~ v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP2(X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f90,plain,
    ( ~ sP0(sK4,sK6,sK5)
    | v5_pre_topc(sK6,sK4,sK5) ),
    inference(resolution,[],[f89,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | v5_pre_topc(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( v5_pre_topc(X1,X2,X0)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ v5_pre_topc(X1,X2,X0) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X1,X2,X0] :
      ( ( ( v5_pre_topc(X2,X0,X1)
          | ~ sP0(X0,X2,X1) )
        & ( sP0(X0,X2,X1)
          | ~ v5_pre_topc(X2,X0,X1) ) )
      | ~ sP1(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X1,X2,X0] :
      ( ( v5_pre_topc(X2,X0,X1)
      <=> sP0(X0,X2,X1) )
      | ~ sP1(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f89,plain,(
    sP1(sK5,sK6,sK4) ),
    inference(subsumption_resolution,[],[f88,f36])).

fof(f88,plain,
    ( sP1(sK5,sK6,sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f87,f38])).

fof(f38,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f22])).

fof(f87,plain,
    ( sP1(sK5,sK6,sK4)
    | ~ l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f86,f39])).

fof(f39,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f22])).

fof(f86,plain,
    ( sP1(sK5,sK6,sK4)
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f85,f40])).

fof(f40,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f22])).

fof(f85,plain,
    ( sP1(sK5,sK6,sK4)
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f49,f41])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | sP1(X1,X2,X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X1,X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f9,f14,f13])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).

%------------------------------------------------------------------------------
