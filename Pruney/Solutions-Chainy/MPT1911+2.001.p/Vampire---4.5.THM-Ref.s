%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 420 expanded)
%              Number of leaves         :   10 ( 149 expanded)
%              Depth                    :   11
%              Number of atoms          :  303 (3283 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f78,plain,(
    $false ),
    inference(global_subsumption,[],[f68,f69,f71,f77])).

fof(f77,plain,
    ( ~ m1_subset_1(sK5(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v5_pre_topc(sK5(sK4,sK3),sK3,sK4)
    | ~ v1_funct_2(sK5(sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(subsumption_resolution,[],[f76,f67])).

fof(f67,plain,(
    v1_funct_1(sK5(sK4,sK3)) ),
    inference(unit_resulting_resolution,[],[f60,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v1_funct_1(sK5(X0,X1)) ) ),
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

fof(f60,plain,(
    sP0(sK4,sK3) ),
    inference(unit_resulting_resolution,[],[f28,f29,f30,f31,f32,f34,f33,f41])).

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

fof(f34,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f32,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f31,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f30,plain,(
    v3_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f29,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f28,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f76,plain,
    ( ~ m1_subset_1(sK5(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v5_pre_topc(sK5(sK4,sK3),sK3,sK4)
    | ~ v1_funct_2(sK5(sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_1(sK5(sK4,sK3)) ),
    inference(subsumption_resolution,[],[f75,f57])).

fof(f57,plain,(
    ~ sP1(sK4,sK3) ),
    inference(unit_resulting_resolution,[],[f35,f51,f43])).

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

fof(f51,plain,(
    sP2(sK3,sK4) ),
    inference(unit_resulting_resolution,[],[f28,f29,f31,f32,f34,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | sP2(X0,X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
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

fof(f35,plain,(
    ~ r1_borsuk_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f75,plain,
    ( sP1(sK4,sK3)
    | ~ m1_subset_1(sK5(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v5_pre_topc(sK5(sK4,sK3),sK3,sK4)
    | ~ v1_funct_2(sK5(sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_1(sK5(sK4,sK3)) ),
    inference(resolution,[],[f65,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_borsuk_1(X2,X1,X0)
      | sP1(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(X2,X1,X0)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2) ) ),
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

fof(f65,plain,(
    v3_borsuk_1(sK5(sK4,sK3),sK3,sK4) ),
    inference(unit_resulting_resolution,[],[f60,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v3_borsuk_1(sK5(X0,X1),X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,(
    v5_pre_topc(sK5(sK4,sK3),sK3,sK4) ),
    inference(resolution,[],[f60,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v5_pre_topc(sK5(X0,X1),X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    v1_funct_2(sK5(sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(resolution,[],[f60,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v1_funct_2(sK5(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f68,plain,(
    m1_subset_1(sK5(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(resolution,[],[f60,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:05:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (22454)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.21/0.48  % (22462)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.21/0.48  % (22462)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(global_subsumption,[],[f68,f69,f71,f77])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    ~m1_subset_1(sK5(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v5_pre_topc(sK5(sK4,sK3),sK3,sK4) | ~v1_funct_2(sK5(sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK4))),
% 0.21/0.48    inference(subsumption_resolution,[],[f76,f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    v1_funct_1(sK5(sK4,sK3))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f60,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~sP0(X0,X1) | v1_funct_1(sK5(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1] : ((v3_borsuk_1(sK5(X0,X1),X1,X0) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(sK5(X0,X1),X1,X0) & v1_funct_2(sK5(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK5(X0,X1))) | ~sP0(X0,X1))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : (v3_borsuk_1(X2,X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(X2,X1,X0) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (v3_borsuk_1(sK5(X0,X1),X1,X0) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(sK5(X0,X1),X1,X0) & v1_funct_2(sK5(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK5(X0,X1))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1] : (? [X2] : (v3_borsuk_1(X2,X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(X2,X1,X0) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) | ~sP0(X0,X1))),
% 0.21/0.49    inference(rectify,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : (v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) | ~sP0(X1,X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : (v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) | ~sP0(X1,X0))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    sP0(sK4,sK3)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f28,f29,f30,f31,f32,f34,f33,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | sP0(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (sP0(X1,X0) | ~m1_pre_topc(X1,X0) | ~v1_tdlat_3(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(definition_folding,[],[f8,f11])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (? [X2] : (v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) | ~m1_pre_topc(X1,X0) | ~v1_tdlat_3(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (? [X2] : (v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) | (~m1_pre_topc(X1,X0) | ~v1_tdlat_3(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tex_2)).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    v1_tdlat_3(sK4)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    (~r1_borsuk_1(sK3,sK4) & m1_pre_topc(sK4,sK3) & v1_tdlat_3(sK4) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v3_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f6,f17,f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (~r1_borsuk_1(X0,X1) & m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_borsuk_1(sK3,X1) & m1_pre_topc(X1,sK3) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK3) & v3_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X1] : (~r1_borsuk_1(sK3,X1) & m1_pre_topc(X1,sK3) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) => (~r1_borsuk_1(sK3,sK4) & m1_pre_topc(sK4,sK3) & v1_tdlat_3(sK4) & ~v2_struct_0(sK4))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (~r1_borsuk_1(X0,X1) & m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f5])).
% 0.21/0.49  fof(f5,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (~r1_borsuk_1(X0,X1) & (m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) => r1_borsuk_1(X0,X1)))),
% 0.21/0.49    inference(negated_conjecture,[],[f3])).
% 0.21/0.49  fof(f3,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) => r1_borsuk_1(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tex_2)).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    m1_pre_topc(sK4,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ~v2_struct_0(sK4)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    l1_pre_topc(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    v3_tdlat_3(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    v2_pre_topc(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ~v2_struct_0(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ~m1_subset_1(sK5(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v5_pre_topc(sK5(sK4,sK3),sK3,sK4) | ~v1_funct_2(sK5(sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK4)) | ~v1_funct_1(sK5(sK4,sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f75,f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ~sP1(sK4,sK3)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f35,f51,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~sP2(X0,X1) | ~sP1(X1,X0) | r1_borsuk_1(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1] : (((r1_borsuk_1(X0,X1) | ~sP1(X1,X0)) & (sP1(X1,X0) | ~r1_borsuk_1(X0,X1))) | ~sP2(X0,X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_borsuk_1(X0,X1) <=> sP1(X1,X0)) | ~sP2(X0,X1))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    sP2(sK3,sK4)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f28,f29,f31,f32,f34,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | sP2(X0,X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (sP2(X0,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(definition_folding,[],[f10,f14,f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X1,X0] : (sP1(X1,X0) <=> ? [X2] : (v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((r1_borsuk_1(X0,X1) <=> ? [X2] : (v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((r1_borsuk_1(X0,X1) <=> ? [X2] : (v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (r1_borsuk_1(X0,X1) <=> ? [X2] : (v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_borsuk_1)).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ~r1_borsuk_1(sK3,sK4)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    sP1(sK4,sK3) | ~m1_subset_1(sK5(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v5_pre_topc(sK5(sK4,sK3),sK3,sK4) | ~v1_funct_2(sK5(sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK4)) | ~v1_funct_1(sK5(sK4,sK3))),
% 0.21/0.49    inference(resolution,[],[f65,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v3_borsuk_1(X2,X1,X0) | sP1(X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(X2,X1,X0) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1] : ((sP1(X0,X1) | ! [X2] : (~v3_borsuk_1(X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(X2,X1,X0) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) & ((v3_borsuk_1(sK6(X0,X1),X1,X0) & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(sK6(X0,X1),X1,X0) & v1_funct_2(sK6(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK6(X0,X1))) | ~sP1(X0,X1)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f25,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X3] : (v3_borsuk_1(X3,X1,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(X3,X1,X0) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (v3_borsuk_1(sK6(X0,X1),X1,X0) & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(sK6(X0,X1),X1,X0) & v1_funct_2(sK6(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK6(X0,X1))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1] : ((sP1(X0,X1) | ! [X2] : (~v3_borsuk_1(X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(X2,X1,X0) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) & (? [X3] : (v3_borsuk_1(X3,X1,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(X3,X1,X0) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) | ~sP1(X0,X1)))),
% 0.21/0.49    inference(rectify,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X1,X0] : ((sP1(X1,X0) | ! [X2] : (~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) & (? [X2] : (v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) | ~sP1(X1,X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f13])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    v3_borsuk_1(sK5(sK4,sK3),sK3,sK4)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f60,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~sP0(X0,X1) | v3_borsuk_1(sK5(X0,X1),X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    v5_pre_topc(sK5(sK4,sK3),sK3,sK4)),
% 0.21/0.49    inference(resolution,[],[f60,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~sP0(X0,X1) | v5_pre_topc(sK5(X0,X1),X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    v1_funct_2(sK5(sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK4))),
% 0.21/0.49    inference(resolution,[],[f60,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~sP0(X0,X1) | v1_funct_2(sK5(X0,X1),u1_struct_0(X1),u1_struct_0(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    m1_subset_1(sK5(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))),
% 0.21/0.49    inference(resolution,[],[f60,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~sP0(X0,X1) | m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (22462)------------------------------
% 0.21/0.49  % (22462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (22462)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (22462)Memory used [KB]: 5373
% 0.21/0.49  % (22462)Time elapsed: 0.065 s
% 0.21/0.49  % (22462)------------------------------
% 0.21/0.49  % (22462)------------------------------
% 0.21/0.49  % (22441)Success in time 0.127 s
%------------------------------------------------------------------------------
