%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 245 expanded)
%              Number of leaves         :    9 (  74 expanded)
%              Depth                    :   23
%              Number of atoms          :  301 (1482 expanded)
%              Number of equality atoms :   19 ( 194 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f253,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f161,f168,f172,f252])).

fof(f252,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f249,f28])).

fof(f28,plain,(
    sQ2_eqProxy(u1_struct_0(sK0),sK1) ),
    inference(equality_proxy_replacement,[],[f19,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( sQ2_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ2_eqProxy])])).

fof(f19,plain,(
    u1_struct_0(sK0) = sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( ~ v1_tdlat_3(sK0)
      | ~ v2_tex_2(sK1,sK0) )
    & ( v1_tdlat_3(sK0)
      | v2_tex_2(sK1,sK0) )
    & u1_struct_0(sK0) = sK1
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f13,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_tdlat_3(X0)
              | ~ v2_tex_2(X1,X0) )
            & ( v1_tdlat_3(X0)
              | v2_tex_2(X1,X0) )
            & u1_struct_0(X0) = X1
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_tdlat_3(sK0)
            | ~ v2_tex_2(X1,sK0) )
          & ( v1_tdlat_3(sK0)
            | v2_tex_2(X1,sK0) )
          & u1_struct_0(sK0) = X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( ( ~ v1_tdlat_3(sK0)
          | ~ v2_tex_2(X1,sK0) )
        & ( v1_tdlat_3(sK0)
          | v2_tex_2(X1,sK0) )
        & u1_struct_0(sK0) = X1
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ v1_tdlat_3(sK0)
        | ~ v2_tex_2(sK1,sK0) )
      & ( v1_tdlat_3(sK0)
        | v2_tex_2(sK1,sK0) )
      & u1_struct_0(sK0) = sK1
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_tdlat_3(X0)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_tdlat_3(X0)
            | v2_tex_2(X1,X0) )
          & u1_struct_0(X0) = X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_tdlat_3(X0)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_tdlat_3(X0)
            | v2_tex_2(X1,X0) )
          & u1_struct_0(X0) = X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_tdlat_3(X0) )
          & u1_struct_0(X0) = X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_tdlat_3(X0) )
          & u1_struct_0(X0) = X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( u1_struct_0(X0) = X1
             => ( v2_tex_2(X1,X0)
              <=> v1_tdlat_3(X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_struct_0(X0) = X1
           => ( v2_tex_2(X1,X0)
            <=> v1_tdlat_3(X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tex_2)).

fof(f249,plain,
    ( ~ sQ2_eqProxy(u1_struct_0(sK0),sK1)
    | ~ spl3_1
    | spl3_2
    | ~ spl3_4 ),
    inference(resolution,[],[f244,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( sQ2_eqProxy(X1,X0)
      | ~ sQ2_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f27])).

fof(f244,plain,
    ( ~ sQ2_eqProxy(sK1,u1_struct_0(sK0))
    | ~ spl3_1
    | spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f235,f37])).

fof(f37,plain,(
    ! [X0] : sQ2_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f27])).

fof(f235,plain,
    ( ~ sQ2_eqProxy(sK1,u1_struct_0(sK0))
    | ~ sQ2_eqProxy(sK0,sK0)
    | ~ spl3_1
    | spl3_2
    | ~ spl3_4 ),
    inference(resolution,[],[f227,f170])).

fof(f170,plain,
    ( ! [X0,X1] :
        ( v2_tex_2(X1,X0)
        | ~ sQ2_eqProxy(sK1,X1)
        | ~ sQ2_eqProxy(sK0,X0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f43,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_tex_2(X0,X2)
      | ~ sQ2_eqProxy(X2,X3)
      | ~ sQ2_eqProxy(X0,X1)
      | v2_tex_2(X1,X3) ) ),
    inference(equality_proxy_axiom,[],[f27])).

fof(f43,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_1
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f227,plain,
    ( ~ v2_tex_2(u1_struct_0(sK0),sK0)
    | spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f226,f17])).

fof(f17,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f226,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_tex_2(u1_struct_0(sK0),sK0)
    | spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f225,f153])).

fof(f153,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl3_4
  <=> m1_pre_topc(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f225,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_tex_2(u1_struct_0(sK0),sK0)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f223,f37])).

fof(f223,plain,
    ( ~ sQ2_eqProxy(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_tex_2(u1_struct_0(sK0),sK0)
    | spl3_2 ),
    inference(resolution,[],[f182,f16])).

fof(f16,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f182,plain,
    ( ! [X5] :
        ( v2_struct_0(X5)
        | ~ sQ2_eqProxy(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(X5)))
        | ~ m1_pre_topc(sK0,X5)
        | ~ l1_pre_topc(X5)
        | ~ v2_tex_2(u1_struct_0(sK0),X5) )
    | spl3_2 ),
    inference(subsumption_resolution,[],[f181,f16])).

fof(f181,plain,
    ( ! [X5] :
        ( ~ v2_tex_2(u1_struct_0(sK0),X5)
        | ~ sQ2_eqProxy(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(X5)))
        | ~ m1_pre_topc(sK0,X5)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X5) )
    | spl3_2 ),
    inference(subsumption_resolution,[],[f177,f28])).

fof(f177,plain,
    ( ! [X5] :
        ( ~ sQ2_eqProxy(u1_struct_0(sK0),sK1)
        | ~ v2_tex_2(u1_struct_0(sK0),X5)
        | ~ sQ2_eqProxy(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(X5)))
        | ~ m1_pre_topc(sK0,X5)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X5) )
    | spl3_2 ),
    inference(resolution,[],[f46,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ sQ2_eqProxy(u1_struct_0(X1),sK1)
      | ~ v2_tex_2(u1_struct_0(X1),X0)
      | ~ sQ2_eqProxy(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f52,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(u1_struct_0(X1),X0)
      | v1_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

fof(f52,plain,(
    ! [X4,X5] :
      ( m1_subset_1(X5,X4)
      | ~ sQ2_eqProxy(k1_zfmisc_1(u1_struct_0(sK0)),X4)
      | ~ sQ2_eqProxy(X5,sK1) ) ),
    inference(resolution,[],[f49,f38])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ sQ2_eqProxy(sK1,X1)
      | ~ sQ2_eqProxy(k1_zfmisc_1(u1_struct_0(sK0)),X0)
      | m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f34,f18])).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,X2)
      | ~ sQ2_eqProxy(X2,X3)
      | ~ sQ2_eqProxy(X0,X1)
      | m1_subset_1(X1,X3) ) ),
    inference(equality_proxy_axiom,[],[f27])).

fof(f46,plain,
    ( ~ v1_tdlat_3(sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_2
  <=> v1_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f172,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f169,f43])).

fof(f169,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f21,f47])).

fof(f47,plain,
    ( v1_tdlat_3(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f21,plain,
    ( ~ v1_tdlat_3(sK0)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f168,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f16,f42,f37,f16,f17,f47,f28,f28,f37,f153,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v1_tdlat_3(X0)
      | ~ sQ2_eqProxy(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ sQ2_eqProxy(u1_struct_0(X0),sK1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ sQ2_eqProxy(X1,X2)
      | ~ sQ2_eqProxy(u1_struct_0(X0),X3)
      | v2_tex_2(X3,X2) ) ),
    inference(resolution,[],[f55,f35])).

fof(f55,plain,(
    ! [X2,X3] :
      ( v2_tex_2(u1_struct_0(X3),X2)
      | ~ sQ2_eqProxy(u1_struct_0(X3),sK1)
      | ~ v1_tdlat_3(X3)
      | ~ sQ2_eqProxy(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_pre_topc(X3,X2)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f52,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f42,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f161,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | spl3_4 ),
    inference(subsumption_resolution,[],[f157,f17])).

fof(f157,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_4 ),
    inference(resolution,[],[f154,f22])).

fof(f22,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f154,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f152])).

fof(f48,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f20,f45,f41])).

fof(f20,plain,
    ( v1_tdlat_3(sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:49:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (26774)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (26774)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (26769)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (26782)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f253,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f48,f161,f168,f172,f252])).
% 0.21/0.48  fof(f252,plain,(
% 0.21/0.48    ~spl3_1 | spl3_2 | ~spl3_4),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f251])).
% 0.21/0.48  fof(f251,plain,(
% 0.21/0.48    $false | (~spl3_1 | spl3_2 | ~spl3_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f249,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    sQ2_eqProxy(u1_struct_0(sK0),sK1)),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f19,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X1,X0] : (sQ2_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.48    introduced(equality_proxy_definition,[new_symbols(naming,[sQ2_eqProxy])])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    u1_struct_0(sK0) = sK1),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ((~v1_tdlat_3(sK0) | ~v2_tex_2(sK1,sK0)) & (v1_tdlat_3(sK0) | v2_tex_2(sK1,sK0)) & u1_struct_0(sK0) = sK1 & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f13,f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((~v1_tdlat_3(X0) | ~v2_tex_2(X1,X0)) & (v1_tdlat_3(X0) | v2_tex_2(X1,X0)) & u1_struct_0(X0) = X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_tdlat_3(sK0) | ~v2_tex_2(X1,sK0)) & (v1_tdlat_3(sK0) | v2_tex_2(X1,sK0)) & u1_struct_0(sK0) = X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X1] : ((~v1_tdlat_3(sK0) | ~v2_tex_2(X1,sK0)) & (v1_tdlat_3(sK0) | v2_tex_2(X1,sK0)) & u1_struct_0(sK0) = X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~v1_tdlat_3(sK0) | ~v2_tex_2(sK1,sK0)) & (v1_tdlat_3(sK0) | v2_tex_2(sK1,sK0)) & u1_struct_0(sK0) = sK1 & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((~v1_tdlat_3(X0) | ~v2_tex_2(X1,X0)) & (v1_tdlat_3(X0) | v2_tex_2(X1,X0)) & u1_struct_0(X0) = X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (((~v1_tdlat_3(X0) | ~v2_tex_2(X1,X0)) & (v1_tdlat_3(X0) | v2_tex_2(X1,X0))) & u1_struct_0(X0) = X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_tdlat_3(X0)) & u1_struct_0(X0) = X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f5])).
% 0.21/0.48  fof(f5,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (((v2_tex_2(X1,X0) <~> v1_tdlat_3(X0)) & u1_struct_0(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X0) = X1 => (v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f3])).
% 0.21/0.48  fof(f3,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X0) = X1 => (v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tex_2)).
% 0.21/0.48  fof(f249,plain,(
% 0.21/0.48    ~sQ2_eqProxy(u1_struct_0(sK0),sK1) | (~spl3_1 | spl3_2 | ~spl3_4)),
% 0.21/0.48    inference(resolution,[],[f244,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sQ2_eqProxy(X1,X0) | ~sQ2_eqProxy(X0,X1)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f27])).
% 0.21/0.48  fof(f244,plain,(
% 0.21/0.48    ~sQ2_eqProxy(sK1,u1_struct_0(sK0)) | (~spl3_1 | spl3_2 | ~spl3_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f235,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0] : (sQ2_eqProxy(X0,X0)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f27])).
% 0.21/0.48  fof(f235,plain,(
% 0.21/0.48    ~sQ2_eqProxy(sK1,u1_struct_0(sK0)) | ~sQ2_eqProxy(sK0,sK0) | (~spl3_1 | spl3_2 | ~spl3_4)),
% 0.21/0.48    inference(resolution,[],[f227,f170])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~sQ2_eqProxy(sK1,X1) | ~sQ2_eqProxy(sK0,X0)) ) | ~spl3_1),
% 0.21/0.48    inference(resolution,[],[f43,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~v2_tex_2(X0,X2) | ~sQ2_eqProxy(X2,X3) | ~sQ2_eqProxy(X0,X1) | v2_tex_2(X1,X3)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f27])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    v2_tex_2(sK1,sK0) | ~spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    spl3_1 <=> v2_tex_2(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f227,plain,(
% 0.21/0.48    ~v2_tex_2(u1_struct_0(sK0),sK0) | (spl3_2 | ~spl3_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f226,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f226,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v2_tex_2(u1_struct_0(sK0),sK0) | (spl3_2 | ~spl3_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f225,f153])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    m1_pre_topc(sK0,sK0) | ~spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f152])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    spl3_4 <=> m1_pre_topc(sK0,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f225,plain,(
% 0.21/0.48    ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_tex_2(u1_struct_0(sK0),sK0) | spl3_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f223,f37])).
% 0.21/0.48  fof(f223,plain,(
% 0.21/0.48    ~sQ2_eqProxy(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_tex_2(u1_struct_0(sK0),sK0) | spl3_2),
% 0.21/0.48    inference(resolution,[],[f182,f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f182,plain,(
% 0.21/0.48    ( ! [X5] : (v2_struct_0(X5) | ~sQ2_eqProxy(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(X5))) | ~m1_pre_topc(sK0,X5) | ~l1_pre_topc(X5) | ~v2_tex_2(u1_struct_0(sK0),X5)) ) | spl3_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f181,f16])).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    ( ! [X5] : (~v2_tex_2(u1_struct_0(sK0),X5) | ~sQ2_eqProxy(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(X5))) | ~m1_pre_topc(sK0,X5) | v2_struct_0(sK0) | ~l1_pre_topc(X5) | v2_struct_0(X5)) ) | spl3_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f177,f28])).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    ( ! [X5] : (~sQ2_eqProxy(u1_struct_0(sK0),sK1) | ~v2_tex_2(u1_struct_0(sK0),X5) | ~sQ2_eqProxy(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(X5))) | ~m1_pre_topc(sK0,X5) | v2_struct_0(sK0) | ~l1_pre_topc(X5) | v2_struct_0(X5)) ) | spl3_2),
% 0.21/0.48    inference(resolution,[],[f46,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_tdlat_3(X1) | ~sQ2_eqProxy(u1_struct_0(X1),sK1) | ~v2_tex_2(u1_struct_0(X1),X0) | ~sQ2_eqProxy(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(resolution,[],[f52,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(u1_struct_0(X1),X0) | v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X4,X5] : (m1_subset_1(X5,X4) | ~sQ2_eqProxy(k1_zfmisc_1(u1_struct_0(sK0)),X4) | ~sQ2_eqProxy(X5,sK1)) )),
% 0.21/0.48    inference(resolution,[],[f49,f38])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~sQ2_eqProxy(sK1,X1) | ~sQ2_eqProxy(k1_zfmisc_1(u1_struct_0(sK0)),X0) | m1_subset_1(X1,X0)) )),
% 0.21/0.48    inference(resolution,[],[f34,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,X2) | ~sQ2_eqProxy(X2,X3) | ~sQ2_eqProxy(X0,X1) | m1_subset_1(X1,X3)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f27])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ~v1_tdlat_3(sK0) | spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    spl3_2 <=> v1_tdlat_3(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    ~spl3_1 | ~spl3_2),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f171])).
% 0.21/0.48  fof(f171,plain,(
% 0.21/0.48    $false | (~spl3_1 | ~spl3_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f169,f43])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | ~spl3_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f21,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    v1_tdlat_3(sK0) | ~spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f45])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ~v1_tdlat_3(sK0) | ~v2_tex_2(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f168,plain,(
% 0.21/0.48    spl3_1 | ~spl3_2 | ~spl3_4),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f166])).
% 0.21/0.48  fof(f166,plain,(
% 0.21/0.48    $false | (spl3_1 | ~spl3_2 | ~spl3_4)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f16,f42,f37,f16,f17,f47,f28,f28,f37,f153,f85])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v1_tdlat_3(X0) | ~sQ2_eqProxy(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X0,X1) | ~sQ2_eqProxy(u1_struct_0(X0),sK1) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~sQ2_eqProxy(X1,X2) | ~sQ2_eqProxy(u1_struct_0(X0),X3) | v2_tex_2(X3,X2)) )),
% 0.21/0.48    inference(resolution,[],[f55,f35])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X2,X3] : (v2_tex_2(u1_struct_0(X3),X2) | ~sQ2_eqProxy(u1_struct_0(X3),sK1) | ~v1_tdlat_3(X3) | ~sQ2_eqProxy(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | ~l1_pre_topc(X2) | v2_struct_0(X2)) )),
% 0.21/0.48    inference(resolution,[],[f52,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f41])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    spl3_4),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f160])).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    $false | spl3_4),
% 0.21/0.48    inference(subsumption_resolution,[],[f157,f17])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | spl3_4),
% 0.21/0.48    inference(resolution,[],[f154,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    ~m1_pre_topc(sK0,sK0) | spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f152])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    spl3_1 | spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f20,f45,f41])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    v1_tdlat_3(sK0) | v2_tex_2(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (26774)------------------------------
% 0.21/0.48  % (26774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (26774)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (26774)Memory used [KB]: 6268
% 0.21/0.48  % (26774)Time elapsed: 0.065 s
% 0.21/0.48  % (26774)------------------------------
% 0.21/0.48  % (26774)------------------------------
% 0.21/0.48  % (26768)Success in time 0.125 s
%------------------------------------------------------------------------------
