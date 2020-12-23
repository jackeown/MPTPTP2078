%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1911+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 457 expanded)
%              Number of leaves         :   10 ( 149 expanded)
%              Depth                    :   20
%              Number of atoms          :  349 (3437 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f76,plain,(
    $false ),
    inference(subsumption_resolution,[],[f75,f65])).

fof(f65,plain,(
    sP0(sK4,sK3) ),
    inference(subsumption_resolution,[],[f64,f28])).

fof(f28,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_borsuk_1(sK3,sK4)
    & m1_pre_topc(sK4,sK3)
    & v1_tdlat_3(sK4)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v3_tdlat_3(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f6,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_borsuk_1(X0,X1)
            & m1_pre_topc(X1,X0)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_borsuk_1(sK3,X1)
          & m1_pre_topc(X1,sK3)
          & v1_tdlat_3(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK3)
      & v3_tdlat_3(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ~ r1_borsuk_1(sK3,X1)
        & m1_pre_topc(X1,sK3)
        & v1_tdlat_3(X1)
        & ~ v2_struct_0(X1) )
   => ( ~ r1_borsuk_1(sK3,sK4)
      & m1_pre_topc(sK4,sK3)
      & v1_tdlat_3(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_borsuk_1(X0,X1)
          & m1_pre_topc(X1,X0)
          & v1_tdlat_3(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_borsuk_1(X0,X1)
          & m1_pre_topc(X1,X0)
          & v1_tdlat_3(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) )
           => r1_borsuk_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
         => r1_borsuk_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tex_2)).

fof(f64,plain,
    ( sP0(sK4,sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f63,f29])).

fof(f29,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f63,plain,
    ( sP0(sK4,sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f62,f34])).

fof(f34,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f62,plain,
    ( sP0(sK4,sK3)
    | ~ m1_pre_topc(sK4,sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f61,f31])).

fof(f31,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f61,plain,
    ( sP0(sK4,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ m1_pre_topc(sK4,sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f55,f30])).

fof(f30,plain,(
    v3_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v3_tdlat_3(X0)
      | sP0(sK4,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK4,X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f54,f32])).

fof(f32,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK4,X0)
      | sP0(sK4,X0)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f33,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | sP0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tdlat_3(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f8,f11])).

fof(f11,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v3_borsuk_1(X2,X0,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
      | ~ sP0(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tdlat_3(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tdlat_3(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
         => ? [X2] :
              ( v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tex_2)).

fof(f33,plain,(
    v1_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f75,plain,(
    ~ sP0(sK4,sK3) ),
    inference(resolution,[],[f74,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK5(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v3_borsuk_1(sK5(X0,X1),X1,X0)
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v5_pre_topc(sK5(X0,X1),X1,X0)
        & v1_funct_2(sK5(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK5(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v3_borsuk_1(X2,X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(X2,X1,X0)
          & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X2) )
     => ( v3_borsuk_1(sK5(X0,X1),X1,X0)
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v5_pre_topc(sK5(X0,X1),X1,X0)
        & v1_funct_2(sK5(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK5(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( v3_borsuk_1(X2,X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(X2,X1,X0)
          & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X2) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v3_borsuk_1(X2,X0,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
      | ~ sP0(X1,X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f74,plain,(
    ~ v1_funct_2(sK5(sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(subsumption_resolution,[],[f73,f60])).

fof(f60,plain,(
    ~ sP1(sK4,sK3) ),
    inference(subsumption_resolution,[],[f59,f35])).

fof(f35,plain,(
    ~ r1_borsuk_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f59,plain,
    ( ~ sP1(sK4,sK3)
    | r1_borsuk_1(sK3,sK4) ),
    inference(resolution,[],[f57,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | ~ sP1(X1,X0)
      | r1_borsuk_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( r1_borsuk_1(X0,X1)
          | ~ sP1(X1,X0) )
        & ( sP1(X1,X0)
          | ~ r1_borsuk_1(X0,X1) ) )
      | ~ sP2(X0,X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_borsuk_1(X0,X1)
      <=> sP1(X1,X0) )
      | ~ sP2(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f57,plain,(
    sP2(sK3,sK4) ),
    inference(subsumption_resolution,[],[f56,f32])).

fof(f56,plain,
    ( v2_struct_0(sK4)
    | sP2(sK3,sK4) ),
    inference(resolution,[],[f53,f34])).

fof(f53,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(X0)
      | sP2(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f52,f28])).

fof(f52,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(X0)
      | sP2(sK3,X0)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f51,f29])).

fof(f51,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(X0)
      | sP2(sK3,X0)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f31,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | sP2(X0,X1)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X0,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f10,f14,f13])).

fof(f13,plain,(
    ! [X1,X0] :
      ( sP1(X1,X0)
    <=> ? [X2] :
          ( v3_borsuk_1(X2,X0,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_borsuk_1(X0,X1)
          <=> ? [X2] :
                ( v3_borsuk_1(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) ) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_borsuk_1(X0,X1)
          <=> ? [X2] :
                ( v3_borsuk_1(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) ) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( r1_borsuk_1(X0,X1)
          <=> ? [X2] :
                ( v3_borsuk_1(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_borsuk_1)).

fof(f73,plain,
    ( ~ v1_funct_2(sK5(sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK4))
    | sP1(sK4,sK3) ),
    inference(subsumption_resolution,[],[f72,f67])).

fof(f67,plain,(
    v5_pre_topc(sK5(sK4,sK3),sK3,sK4) ),
    inference(resolution,[],[f65,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v5_pre_topc(sK5(X0,X1),X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f72,plain,
    ( ~ v5_pre_topc(sK5(sK4,sK3),sK3,sK4)
    | ~ v1_funct_2(sK5(sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK4))
    | sP1(sK4,sK3) ),
    inference(subsumption_resolution,[],[f71,f69])).

fof(f69,plain,(
    v3_borsuk_1(sK5(sK4,sK3),sK3,sK4) ),
    inference(resolution,[],[f65,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v3_borsuk_1(sK5(X0,X1),X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,
    ( ~ v3_borsuk_1(sK5(sK4,sK3),sK3,sK4)
    | ~ v5_pre_topc(sK5(sK4,sK3),sK3,sK4)
    | ~ v1_funct_2(sK5(sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK4))
    | sP1(sK4,sK3) ),
    inference(resolution,[],[f70,f68])).

fof(f68,plain,(
    m1_subset_1(sK5(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(resolution,[],[f65,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v3_borsuk_1(sK5(sK4,sK3),X0,X1)
      | ~ v5_pre_topc(sK5(sK4,sK3),X0,X1)
      | ~ v1_funct_2(sK5(sK4,sK3),u1_struct_0(X0),u1_struct_0(X1))
      | sP1(X1,X0) ) ),
    inference(resolution,[],[f66,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_borsuk_1(X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(X2,X1,X0)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ! [X2] :
            ( ~ v3_borsuk_1(X2,X1,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v5_pre_topc(X2,X1,X0)
            | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(X2) ) )
      & ( ( v3_borsuk_1(sK6(X0,X1),X1,X0)
          & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(sK6(X0,X1),X1,X0)
          & v1_funct_2(sK6(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(sK6(X0,X1)) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( v3_borsuk_1(X3,X1,X0)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(X3,X1,X0)
          & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X3) )
     => ( v3_borsuk_1(sK6(X0,X1),X1,X0)
        & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v5_pre_topc(sK6(X0,X1),X1,X0)
        & v1_funct_2(sK6(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ! [X2] :
            ( ~ v3_borsuk_1(X2,X1,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v5_pre_topc(X2,X1,X0)
            | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(X2) ) )
      & ( ? [X3] :
            ( v3_borsuk_1(X3,X1,X0)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            & v5_pre_topc(X3,X1,X0)
            & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
            & v1_funct_1(X3) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ( sP1(X1,X0)
        | ! [X2] :
            ( ~ v3_borsuk_1(X2,X0,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            | ~ v5_pre_topc(X2,X0,X1)
            | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
            | ~ v1_funct_1(X2) ) )
      & ( ? [X2] :
            ( v3_borsuk_1(X2,X0,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v5_pre_topc(X2,X0,X1)
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        | ~ sP1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f66,plain,(
    v1_funct_1(sK5(sK4,sK3)) ),
    inference(resolution,[],[f65,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v1_funct_1(sK5(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

%------------------------------------------------------------------------------
