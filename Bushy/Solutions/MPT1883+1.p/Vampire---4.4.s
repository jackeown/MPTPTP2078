%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t51_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:53 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 159 expanded)
%              Number of leaves         :   11 (  53 expanded)
%              Depth                    :   14
%              Number of atoms          :  252 ( 691 expanded)
%              Number of equality atoms :   19 (  72 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f189,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f70,f75,f92,f105,f125,f173,f177,f188])).

fof(f188,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_16
    | spl7_19
    | ~ spl7_30 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_16
    | ~ spl7_19
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f186,f172])).

fof(f172,plain,
    ( ~ v4_tex_2(sK1,sK0)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl7_19
  <=> ~ v4_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f186,plain,
    ( v4_tex_2(sK1,sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_16
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f185,f65])).

fof(f65,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl7_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f185,plain,
    ( v2_struct_0(sK0)
    | v4_tex_2(sK1,sK0)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_16
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f184,f74])).

fof(f74,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl7_4
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f184,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | v4_tex_2(sK1,sK0)
    | ~ spl7_2
    | ~ spl7_16
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f183,f69])).

fof(f69,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl7_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f183,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | v4_tex_2(sK1,sK0)
    | ~ spl7_16
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f182,f121])).

fof(f121,plain,
    ( v3_tex_2(sK2,sK0)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl7_16
  <=> v3_tex_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f182,plain,
    ( ~ v3_tex_2(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | v4_tex_2(sK1,sK0)
    | ~ spl7_30 ),
    inference(superposition,[],[f50,f176])).

fof(f176,plain,
    ( sK2 = sK3(sK0,sK1)
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl7_30
  <=> sK2 = sK3(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(sK3(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | v4_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( v3_tex_2(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( v3_tex_2(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_tex_2(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t51_tex_2.p',d8_tex_2)).

fof(f177,plain,
    ( spl7_30
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f168,f103,f90,f73,f68,f64,f175])).

fof(f90,plain,
    ( spl7_8
  <=> u1_struct_0(sK1) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f103,plain,
    ( spl7_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f168,plain,
    ( sK2 = sK3(sK0,sK1)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f84,f166])).

fof(f166,plain,
    ( ~ v4_tex_2(sK1,sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f41,f165])).

fof(f165,plain,
    ( v3_tex_2(sK2,sK0)
    | ~ v4_tex_2(sK1,sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f164,f65])).

fof(f164,plain,
    ( v3_tex_2(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ v4_tex_2(sK1,sK0)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f163,f74])).

fof(f163,plain,
    ( v3_tex_2(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ v4_tex_2(sK1,sK0)
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f155,f69])).

fof(f155,plain,
    ( v3_tex_2(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ v4_tex_2(sK1,sK0)
    | ~ spl7_8
    | ~ spl7_12 ),
    inference(resolution,[],[f97,f104])).

fof(f104,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f103])).

fof(f97,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X1)))
        | v3_tex_2(sK2,X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK1,X1)
        | v2_struct_0(X1)
        | ~ v4_tex_2(sK1,X1) )
    | ~ spl7_8 ),
    inference(forward_demodulation,[],[f95,f91])).

fof(f91,plain,
    ( u1_struct_0(sK1) = sK2
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f95,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK1,X1)
        | v2_struct_0(X1)
        | v3_tex_2(u1_struct_0(sK1),X1)
        | ~ v4_tex_2(sK1,X1) )
    | ~ spl7_8 ),
    inference(superposition,[],[f62,f91])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | v3_tex_2(u1_struct_0(X1),X0)
      | ~ v4_tex_2(X1,X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v3_tex_2(X2,X0)
      | ~ v4_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f41,plain,
    ( ~ v4_tex_2(sK1,sK0)
    | ~ v3_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_tex_2(X2,X0)
              <~> v4_tex_2(X1,X0) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_tex_2(X2,X0)
              <~> v4_tex_2(X1,X0) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => ( v3_tex_2(X2,X0)
                  <=> v4_tex_2(X1,X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v3_tex_2(X2,X0)
                <=> v4_tex_2(X1,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t51_tex_2.p',t51_tex_2)).

fof(f84,plain,
    ( sK2 = sK3(sK0,sK1)
    | v4_tex_2(sK1,sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f83,f43])).

fof(f43,plain,(
    u1_struct_0(sK1) = sK2 ),
    inference(cnf_transformation,[],[f26])).

fof(f83,plain,
    ( u1_struct_0(sK1) = sK3(sK0,sK1)
    | v4_tex_2(sK1,sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f82,f65])).

fof(f82,plain,
    ( v2_struct_0(sK0)
    | u1_struct_0(sK1) = sK3(sK0,sK1)
    | v4_tex_2(sK1,sK0)
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f78,f69])).

fof(f78,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | u1_struct_0(sK1) = sK3(sK0,sK1)
    | v4_tex_2(sK1,sK0)
    | ~ spl7_4 ),
    inference(resolution,[],[f74,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | u1_struct_0(X1) = sK3(X0,X1)
      | v4_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f173,plain,
    ( ~ spl7_19
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f166,f103,f90,f73,f68,f64,f171])).

fof(f125,plain,
    ( spl7_16
    | spl7_18 ),
    inference(avatar_split_clause,[],[f40,f123,f120])).

fof(f123,plain,
    ( spl7_18
  <=> v4_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f40,plain,
    ( v4_tex_2(sK1,sK0)
    | v3_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f105,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f42,f103])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f92,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f43,f90])).

fof(f75,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f44,f73])).

fof(f44,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f46,f68])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f66,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f45,f64])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
