%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:46 EST 2020

% Result     : Theorem 1.10s
% Output     : Refutation 1.10s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 326 expanded)
%              Number of leaves         :   36 ( 142 expanded)
%              Depth                    :   12
%              Number of atoms          :  562 (1189 expanded)
%              Number of equality atoms :   24 (  48 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f557,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f117,f122,f127,f132,f153,f204,f211,f214,f222,f239,f384,f394,f401,f458,f495,f500,f542,f546,f549,f550,f551,f553])).

fof(f553,plain,
    ( ~ spl5_15
    | spl5_39
    | ~ spl5_32
    | spl5_13
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f552,f391,f219,f416,f492,f236])).

fof(f236,plain,
    ( spl5_15
  <=> v1_zfmisc_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f492,plain,
    ( spl5_39
  <=> v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f416,plain,
    ( spl5_32
  <=> v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f219,plain,
    ( spl5_13
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f391,plain,
    ( spl5_29
  <=> m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f552,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ v1_zfmisc_1(u1_struct_0(sK0))
    | spl5_13
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f531,f221])).

fof(f221,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f219])).

fof(f531,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_29 ),
    inference(resolution,[],[f393,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

fof(f393,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f391])).

fof(f551,plain,
    ( spl5_42
    | spl5_32
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f530,f391,f416,f536])).

fof(f536,plain,
    ( spl5_42
  <=> u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f530,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl5_29 ),
    inference(resolution,[],[f393,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f550,plain,
    ( spl5_2
    | ~ spl5_3
    | spl5_13
    | spl5_15 ),
    inference(avatar_split_clause,[],[f306,f236,f219,f119,f113])).

fof(f113,plain,
    ( spl5_2
  <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f119,plain,
    ( spl5_3
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f306,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl5_3
    | spl5_13
    | spl5_15 ),
    inference(unit_resulting_resolution,[],[f121,f238,f221,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

fof(f238,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f236])).

fof(f121,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f119])).

fof(f549,plain,
    ( spl5_1
    | ~ spl5_32
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f548,f228,f201,f124,f416,f109])).

fof(f109,plain,
    ( spl5_1
  <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f124,plain,
    ( spl5_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f201,plain,
    ( spl5_12
  <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f228,plain,
    ( spl5_14
  <=> sK2(sK0,k1_tex_2(sK0,sK1)) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f548,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f547,f126])).

fof(f126,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f124])).

fof(f547,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f411,f203])).

fof(f203,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f201])).

fof(f411,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_14 ),
    inference(superposition,[],[f84,f230])).

fof(f230,plain,
    ( sK2(sK0,k1_tex_2(sK0,sK1)) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f228])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK2(X0,X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f62,f63])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK2(X0,X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v1_subset_1(X2,u1_struct_0(X0))
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

fof(f546,plain,
    ( ~ spl5_1
    | spl5_32
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f545,f391,f201,f124,f416,f109])).

fof(f545,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f544,f126])).

fof(f544,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_12
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f528,f203])).

fof(f528,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_29 ),
    inference(resolution,[],[f393,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f542,plain,
    ( u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))
    | v1_zfmisc_1(u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f500,plain,
    ( spl5_40
    | ~ spl5_10
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f487,f455,f191,f497])).

fof(f497,plain,
    ( spl5_40
  <=> v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f191,plain,
    ( spl5_10
  <=> v7_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f455,plain,
    ( spl5_36
  <=> l1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f487,plain,
    ( v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl5_10
    | ~ spl5_36 ),
    inference(unit_resulting_resolution,[],[f193,f457,f94])).

fof(f94,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f457,plain,
    ( l1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f455])).

fof(f193,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f191])).

fof(f495,plain,
    ( ~ spl5_39
    | spl5_11
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f488,f455,f196,f492])).

fof(f196,plain,
    ( spl5_11
  <=> v2_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f488,plain,
    ( ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | spl5_11
    | ~ spl5_36 ),
    inference(unit_resulting_resolution,[],[f198,f457,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f198,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f196])).

fof(f458,plain,
    ( spl5_36
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f420,f396,f455])).

fof(f396,plain,
    ( spl5_30
  <=> l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f420,plain,
    ( l1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl5_30 ),
    inference(unit_resulting_resolution,[],[f398,f78])).

fof(f78,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f398,plain,
    ( l1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f396])).

fof(f401,plain,
    ( spl5_30
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f400,f201,f124,f396])).

fof(f400,plain,
    ( l1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f372,f126])).

fof(f372,plain,
    ( l1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_12 ),
    inference(resolution,[],[f203,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f394,plain,
    ( spl5_29
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f368,f201,f124,f391])).

fof(f368,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f126,f203,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f384,plain,
    ( spl5_14
    | spl5_1
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f370,f201,f124,f109,f228])).

fof(f370,plain,
    ( sK2(sK0,k1_tex_2(sK0,sK1)) = u1_struct_0(k1_tex_2(sK0,sK1))
    | spl5_1
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f126,f111,f203,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f111,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f109])).

fof(f239,plain,
    ( spl5_13
    | ~ spl5_15
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f234,f119,f113,f236,f219])).

fof(f234,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f232,f121])).

fof(f232,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_2 ),
    inference(resolution,[],[f114,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f114,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f222,plain,
    ( ~ spl5_13
    | spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f215,f150,f129,f219])).

fof(f129,plain,
    ( spl5_5
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f150,plain,
    ( spl5_6
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f215,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl5_5
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f131,f152,f88])).

fof(f152,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f150])).

fof(f131,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f129])).

fof(f214,plain,
    ( spl5_10
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f213,f129,f124,f119,f191])).

fof(f213,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5 ),
    inference(subsumption_resolution,[],[f212,f131])).

fof(f212,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f187,f126])).

fof(f187,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(resolution,[],[f121,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f211,plain,
    ( ~ spl5_11
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f210,f129,f124,f119,f196])).

fof(f210,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5 ),
    inference(subsumption_resolution,[],[f209,f131])).

fof(f209,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f186,f126])).

fof(f186,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(resolution,[],[f121,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f204,plain,
    ( spl5_12
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f181,f129,f124,f119,f201])).

fof(f181,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f131,f126,f121,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f153,plain,
    ( spl5_6
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f133,f124,f150])).

fof(f133,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f126,f78])).

fof(f132,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f70,f129])).

fof(f70,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f57,f59,f58])).

fof(f58,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
              | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
            & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
              | v1_tex_2(k1_tex_2(X0,X1),X0) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
            | ~ v1_tex_2(k1_tex_2(sK0,X1),sK0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
            | v1_tex_2(k1_tex_2(sK0,X1),sK0) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X1] :
        ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
          | ~ v1_tex_2(k1_tex_2(sK0,X1),sK0) )
        & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
          | v1_tex_2(k1_tex_2(sK0,X1),sK0) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
        | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
      & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
        | v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

fof(f127,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f71,f124])).

fof(f71,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f122,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f72,f119])).

fof(f72,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f60])).

fof(f117,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f73,f113,f109])).

fof(f73,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f116,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f74,f113,f109])).

fof(f74,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:41:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (812613632)
% 0.14/0.38  ipcrm: permission denied for id (812777476)
% 0.14/0.38  ipcrm: permission denied for id (817135621)
% 0.14/0.38  ipcrm: permission denied for id (812843014)
% 0.14/0.38  ipcrm: permission denied for id (817168391)
% 0.14/0.38  ipcrm: permission denied for id (817201160)
% 0.14/0.38  ipcrm: permission denied for id (817233929)
% 0.14/0.38  ipcrm: permission denied for id (817266698)
% 0.14/0.39  ipcrm: permission denied for id (813039628)
% 0.14/0.39  ipcrm: permission denied for id (813072397)
% 0.14/0.39  ipcrm: permission denied for id (813170704)
% 0.14/0.39  ipcrm: permission denied for id (813203473)
% 0.14/0.39  ipcrm: permission denied for id (813236242)
% 0.14/0.39  ipcrm: permission denied for id (817397779)
% 0.14/0.40  ipcrm: permission denied for id (817430548)
% 0.21/0.40  ipcrm: permission denied for id (813367318)
% 0.21/0.40  ipcrm: permission denied for id (817496087)
% 0.21/0.40  ipcrm: permission denied for id (817528856)
% 0.21/0.40  ipcrm: permission denied for id (813465625)
% 0.21/0.40  ipcrm: permission denied for id (813563931)
% 0.21/0.41  ipcrm: permission denied for id (813596700)
% 0.21/0.41  ipcrm: permission denied for id (813629469)
% 0.21/0.41  ipcrm: permission denied for id (813662238)
% 0.21/0.41  ipcrm: permission denied for id (817627168)
% 0.21/0.41  ipcrm: permission denied for id (813760545)
% 0.21/0.41  ipcrm: permission denied for id (813826083)
% 0.21/0.42  ipcrm: permission denied for id (817725477)
% 0.21/0.42  ipcrm: permission denied for id (813924390)
% 0.21/0.42  ipcrm: permission denied for id (817758247)
% 0.21/0.42  ipcrm: permission denied for id (813989928)
% 0.21/0.42  ipcrm: permission denied for id (814055466)
% 0.21/0.42  ipcrm: permission denied for id (817823787)
% 0.21/0.42  ipcrm: permission denied for id (814121004)
% 0.21/0.43  ipcrm: permission denied for id (814153773)
% 0.21/0.43  ipcrm: permission denied for id (814252080)
% 0.21/0.43  ipcrm: permission denied for id (814284849)
% 0.21/0.43  ipcrm: permission denied for id (814317618)
% 0.21/0.43  ipcrm: permission denied for id (817922099)
% 0.21/0.43  ipcrm: permission denied for id (814383156)
% 0.21/0.44  ipcrm: permission denied for id (814448693)
% 0.21/0.44  ipcrm: permission denied for id (814514230)
% 0.21/0.44  ipcrm: permission denied for id (817954871)
% 0.21/0.44  ipcrm: permission denied for id (817987640)
% 0.21/0.44  ipcrm: permission denied for id (814645306)
% 0.21/0.44  ipcrm: permission denied for id (814710844)
% 0.21/0.45  ipcrm: permission denied for id (814743613)
% 0.21/0.45  ipcrm: permission denied for id (814809151)
% 0.21/0.45  ipcrm: permission denied for id (818118720)
% 0.21/0.45  ipcrm: permission denied for id (814874689)
% 0.21/0.45  ipcrm: permission denied for id (814907458)
% 0.21/0.45  ipcrm: permission denied for id (814940227)
% 0.21/0.45  ipcrm: permission denied for id (814972996)
% 0.21/0.46  ipcrm: permission denied for id (815005765)
% 0.21/0.46  ipcrm: permission denied for id (815071302)
% 0.21/0.46  ipcrm: permission denied for id (818151495)
% 0.21/0.46  ipcrm: permission denied for id (815136840)
% 0.21/0.46  ipcrm: permission denied for id (815202378)
% 0.21/0.46  ipcrm: permission denied for id (815235147)
% 0.21/0.46  ipcrm: permission denied for id (815267916)
% 0.21/0.47  ipcrm: permission denied for id (815300685)
% 0.21/0.47  ipcrm: permission denied for id (818249807)
% 0.21/0.47  ipcrm: permission denied for id (815431761)
% 0.21/0.47  ipcrm: permission denied for id (815464530)
% 0.21/0.47  ipcrm: permission denied for id (815497299)
% 0.21/0.47  ipcrm: permission denied for id (815530068)
% 0.21/0.48  ipcrm: permission denied for id (815562837)
% 0.21/0.48  ipcrm: permission denied for id (815595606)
% 0.21/0.48  ipcrm: permission denied for id (818315351)
% 0.21/0.48  ipcrm: permission denied for id (815661144)
% 0.21/0.48  ipcrm: permission denied for id (815693913)
% 0.21/0.48  ipcrm: permission denied for id (815726682)
% 0.21/0.48  ipcrm: permission denied for id (818380892)
% 0.21/0.49  ipcrm: permission denied for id (815857757)
% 0.21/0.49  ipcrm: permission denied for id (815890526)
% 0.21/0.49  ipcrm: permission denied for id (818446432)
% 0.21/0.49  ipcrm: permission denied for id (815988833)
% 0.21/0.49  ipcrm: permission denied for id (816021602)
% 0.21/0.49  ipcrm: permission denied for id (816054371)
% 0.21/0.49  ipcrm: permission denied for id (818511972)
% 0.21/0.50  ipcrm: permission denied for id (818544741)
% 0.21/0.50  ipcrm: permission denied for id (816152678)
% 0.21/0.50  ipcrm: permission denied for id (816185447)
% 0.21/0.50  ipcrm: permission denied for id (816250985)
% 0.21/0.50  ipcrm: permission denied for id (818610282)
% 0.21/0.50  ipcrm: permission denied for id (818643051)
% 0.21/0.50  ipcrm: permission denied for id (818708588)
% 0.21/0.51  ipcrm: permission denied for id (816382061)
% 0.21/0.51  ipcrm: permission denied for id (816414830)
% 0.21/0.51  ipcrm: permission denied for id (818774128)
% 0.21/0.51  ipcrm: permission denied for id (816578674)
% 0.21/0.51  ipcrm: permission denied for id (816611443)
% 0.21/0.51  ipcrm: permission denied for id (816644212)
% 0.21/0.51  ipcrm: permission denied for id (818839669)
% 0.21/0.52  ipcrm: permission denied for id (816742519)
% 0.21/0.52  ipcrm: permission denied for id (816775288)
% 0.21/0.52  ipcrm: permission denied for id (816808057)
% 0.21/0.52  ipcrm: permission denied for id (818905210)
% 0.21/0.52  ipcrm: permission denied for id (818970748)
% 0.21/0.52  ipcrm: permission denied for id (816939133)
% 0.21/0.52  ipcrm: permission denied for id (816971902)
% 1.10/0.66  % (28991)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.10/0.66  % (28991)Refutation not found, incomplete strategy% (28991)------------------------------
% 1.10/0.66  % (28991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.10/0.66  % (28991)Termination reason: Refutation not found, incomplete strategy
% 1.10/0.66  
% 1.10/0.66  % (28991)Memory used [KB]: 10746
% 1.10/0.66  % (28991)Time elapsed: 0.102 s
% 1.10/0.66  % (28991)------------------------------
% 1.10/0.66  % (28991)------------------------------
% 1.10/0.67  % (29005)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.10/0.68  % (29014)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.10/0.68  % (29000)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.10/0.68  % (28989)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.10/0.69  % (29014)Refutation found. Thanks to Tanya!
% 1.10/0.69  % SZS status Theorem for theBenchmark
% 1.10/0.69  % (28996)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.10/0.69  % SZS output start Proof for theBenchmark
% 1.10/0.69  fof(f557,plain,(
% 1.10/0.69    $false),
% 1.10/0.69    inference(avatar_sat_refutation,[],[f116,f117,f122,f127,f132,f153,f204,f211,f214,f222,f239,f384,f394,f401,f458,f495,f500,f542,f546,f549,f550,f551,f553])).
% 1.10/0.69  fof(f553,plain,(
% 1.10/0.69    ~spl5_15 | spl5_39 | ~spl5_32 | spl5_13 | ~spl5_29),
% 1.10/0.69    inference(avatar_split_clause,[],[f552,f391,f219,f416,f492,f236])).
% 1.10/0.69  fof(f236,plain,(
% 1.10/0.69    spl5_15 <=> v1_zfmisc_1(u1_struct_0(sK0))),
% 1.10/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.10/0.69  fof(f492,plain,(
% 1.10/0.69    spl5_39 <=> v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 1.10/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 1.10/0.69  fof(f416,plain,(
% 1.10/0.69    spl5_32 <=> v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 1.10/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 1.10/0.69  fof(f219,plain,(
% 1.10/0.69    spl5_13 <=> v1_xboole_0(u1_struct_0(sK0))),
% 1.10/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.10/0.69  fof(f391,plain,(
% 1.10/0.69    spl5_29 <=> m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.10/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 1.10/0.69  fof(f552,plain,(
% 1.10/0.69    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~v1_zfmisc_1(u1_struct_0(sK0)) | (spl5_13 | ~spl5_29)),
% 1.10/0.69    inference(subsumption_resolution,[],[f531,f221])).
% 1.10/0.69  fof(f221,plain,(
% 1.10/0.69    ~v1_xboole_0(u1_struct_0(sK0)) | spl5_13),
% 1.10/0.69    inference(avatar_component_clause,[],[f219])).
% 1.10/0.69  fof(f531,plain,(
% 1.10/0.69    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~v1_zfmisc_1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~spl5_29),
% 1.10/0.69    inference(resolution,[],[f393,f93])).
% 1.10/0.69  fof(f93,plain,(
% 1.10/0.69    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 1.10/0.69    inference(cnf_transformation,[],[f46])).
% 1.10/0.69  fof(f46,plain,(
% 1.10/0.69    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 1.10/0.69    inference(flattening,[],[f45])).
% 1.10/0.69  fof(f45,plain,(
% 1.10/0.69    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 1.10/0.69    inference(ennf_transformation,[],[f12])).
% 1.10/0.69  fof(f12,axiom,(
% 1.10/0.69    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 1.10/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).
% 1.10/0.69  fof(f393,plain,(
% 1.10/0.69    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_29),
% 1.10/0.69    inference(avatar_component_clause,[],[f391])).
% 1.10/0.69  fof(f551,plain,(
% 1.10/0.69    spl5_42 | spl5_32 | ~spl5_29),
% 1.10/0.69    inference(avatar_split_clause,[],[f530,f391,f416,f536])).
% 1.10/0.69  fof(f536,plain,(
% 1.10/0.69    spl5_42 <=> u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 1.10/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 1.10/0.69  fof(f530,plain,(
% 1.10/0.69    v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~spl5_29),
% 1.10/0.69    inference(resolution,[],[f393,f99])).
% 1.10/0.69  fof(f99,plain,(
% 1.10/0.69    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.10/0.69    inference(cnf_transformation,[],[f69])).
% 1.10/0.69  fof(f69,plain,(
% 1.10/0.69    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.10/0.69    inference(nnf_transformation,[],[f50])).
% 1.10/0.69  fof(f50,plain,(
% 1.10/0.69    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.10/0.69    inference(ennf_transformation,[],[f14])).
% 1.10/0.69  fof(f14,axiom,(
% 1.10/0.69    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.10/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 1.10/0.69  fof(f550,plain,(
% 1.10/0.69    spl5_2 | ~spl5_3 | spl5_13 | spl5_15),
% 1.10/0.69    inference(avatar_split_clause,[],[f306,f236,f219,f119,f113])).
% 1.10/0.69  fof(f113,plain,(
% 1.10/0.69    spl5_2 <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 1.10/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.10/0.69  fof(f119,plain,(
% 1.10/0.69    spl5_3 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.10/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.10/0.69  fof(f306,plain,(
% 1.10/0.69    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | (~spl5_3 | spl5_13 | spl5_15)),
% 1.10/0.69    inference(unit_resulting_resolution,[],[f121,f238,f221,f92])).
% 1.10/0.69  fof(f92,plain,(
% 1.10/0.69    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 1.10/0.69    inference(cnf_transformation,[],[f44])).
% 1.10/0.69  fof(f44,plain,(
% 1.10/0.69    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 1.10/0.69    inference(flattening,[],[f43])).
% 1.10/0.69  fof(f43,plain,(
% 1.10/0.69    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 1.10/0.69    inference(ennf_transformation,[],[f20])).
% 1.10/0.69  fof(f20,axiom,(
% 1.10/0.69    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 1.10/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).
% 1.10/0.69  fof(f238,plain,(
% 1.10/0.69    ~v1_zfmisc_1(u1_struct_0(sK0)) | spl5_15),
% 1.10/0.69    inference(avatar_component_clause,[],[f236])).
% 1.10/0.69  fof(f121,plain,(
% 1.10/0.69    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_3),
% 1.10/0.69    inference(avatar_component_clause,[],[f119])).
% 1.10/0.69  fof(f549,plain,(
% 1.10/0.69    spl5_1 | ~spl5_32 | ~spl5_4 | ~spl5_12 | ~spl5_14),
% 1.10/0.69    inference(avatar_split_clause,[],[f548,f228,f201,f124,f416,f109])).
% 1.10/0.69  fof(f109,plain,(
% 1.10/0.69    spl5_1 <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 1.10/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.10/0.69  fof(f124,plain,(
% 1.10/0.69    spl5_4 <=> l1_pre_topc(sK0)),
% 1.10/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.10/0.69  fof(f201,plain,(
% 1.10/0.69    spl5_12 <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 1.10/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.10/0.69  fof(f228,plain,(
% 1.10/0.69    spl5_14 <=> sK2(sK0,k1_tex_2(sK0,sK1)) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 1.10/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.10/0.69  fof(f548,plain,(
% 1.10/0.69    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl5_4 | ~spl5_12 | ~spl5_14)),
% 1.10/0.69    inference(subsumption_resolution,[],[f547,f126])).
% 1.10/0.69  fof(f126,plain,(
% 1.10/0.69    l1_pre_topc(sK0) | ~spl5_4),
% 1.10/0.69    inference(avatar_component_clause,[],[f124])).
% 1.10/0.69  fof(f547,plain,(
% 1.10/0.69    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | (~spl5_12 | ~spl5_14)),
% 1.10/0.69    inference(subsumption_resolution,[],[f411,f203])).
% 1.10/0.69  fof(f203,plain,(
% 1.10/0.69    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~spl5_12),
% 1.10/0.69    inference(avatar_component_clause,[],[f201])).
% 1.10/0.69  fof(f411,plain,(
% 1.10/0.69    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~spl5_14),
% 1.10/0.69    inference(superposition,[],[f84,f230])).
% 1.10/0.69  fof(f230,plain,(
% 1.10/0.69    sK2(sK0,k1_tex_2(sK0,sK1)) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~spl5_14),
% 1.10/0.69    inference(avatar_component_clause,[],[f228])).
% 1.10/0.69  fof(f84,plain,(
% 1.10/0.69    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.10/0.69    inference(cnf_transformation,[],[f64])).
% 1.10/0.69  fof(f64,plain,(
% 1.10/0.69    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.10/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f62,f63])).
% 1.10/0.69  fof(f63,plain,(
% 1.10/0.69    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.10/0.69    introduced(choice_axiom,[])).
% 1.10/0.69  fof(f62,plain,(
% 1.10/0.69    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.10/0.69    inference(rectify,[],[f61])).
% 1.10/0.69  fof(f61,plain,(
% 1.10/0.69    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.10/0.69    inference(nnf_transformation,[],[f34])).
% 1.10/0.69  fof(f34,plain,(
% 1.10/0.69    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.10/0.69    inference(flattening,[],[f33])).
% 1.10/0.69  fof(f33,plain,(
% 1.10/0.69    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.10/0.69    inference(ennf_transformation,[],[f13])).
% 1.10/0.69  fof(f13,axiom,(
% 1.10/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 1.10/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).
% 1.10/0.69  fof(f546,plain,(
% 1.10/0.69    ~spl5_1 | spl5_32 | ~spl5_4 | ~spl5_12 | ~spl5_29),
% 1.10/0.69    inference(avatar_split_clause,[],[f545,f391,f201,f124,f416,f109])).
% 1.10/0.69  fof(f545,plain,(
% 1.10/0.69    v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl5_4 | ~spl5_12 | ~spl5_29)),
% 1.10/0.69    inference(subsumption_resolution,[],[f544,f126])).
% 1.10/0.69  fof(f544,plain,(
% 1.10/0.69    v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | (~spl5_12 | ~spl5_29)),
% 1.10/0.69    inference(subsumption_resolution,[],[f528,f203])).
% 1.10/0.69  fof(f528,plain,(
% 1.10/0.69    v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~spl5_29),
% 1.10/0.69    inference(resolution,[],[f393,f106])).
% 1.10/0.69  fof(f106,plain,(
% 1.10/0.69    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.10/0.69    inference(equality_resolution,[],[f81])).
% 1.10/0.69  fof(f81,plain,(
% 1.10/0.69    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.10/0.69    inference(cnf_transformation,[],[f64])).
% 1.10/0.69  fof(f542,plain,(
% 1.10/0.69    u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1)) | ~v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))) | v1_zfmisc_1(u1_struct_0(sK0))),
% 1.10/0.69    introduced(theory_tautology_sat_conflict,[])).
% 1.10/0.69  fof(f500,plain,(
% 1.10/0.69    spl5_40 | ~spl5_10 | ~spl5_36),
% 1.10/0.69    inference(avatar_split_clause,[],[f487,f455,f191,f497])).
% 1.10/0.69  fof(f497,plain,(
% 1.10/0.69    spl5_40 <=> v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 1.10/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 1.10/0.69  fof(f191,plain,(
% 1.10/0.69    spl5_10 <=> v7_struct_0(k1_tex_2(sK0,sK1))),
% 1.10/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.10/0.69  fof(f455,plain,(
% 1.10/0.69    spl5_36 <=> l1_struct_0(k1_tex_2(sK0,sK1))),
% 1.10/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 1.10/0.69  fof(f487,plain,(
% 1.10/0.69    v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))) | (~spl5_10 | ~spl5_36)),
% 1.10/0.69    inference(unit_resulting_resolution,[],[f193,f457,f94])).
% 1.10/0.69  fof(f94,plain,(
% 1.10/0.69    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 1.10/0.69    inference(cnf_transformation,[],[f48])).
% 1.10/0.69  fof(f48,plain,(
% 1.10/0.69    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 1.10/0.69    inference(flattening,[],[f47])).
% 1.10/0.69  fof(f47,plain,(
% 1.10/0.69    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 1.10/0.69    inference(ennf_transformation,[],[f9])).
% 1.10/0.69  fof(f9,axiom,(
% 1.10/0.69    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 1.10/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).
% 1.10/0.69  fof(f457,plain,(
% 1.10/0.69    l1_struct_0(k1_tex_2(sK0,sK1)) | ~spl5_36),
% 1.10/0.69    inference(avatar_component_clause,[],[f455])).
% 1.10/0.69  fof(f193,plain,(
% 1.10/0.69    v7_struct_0(k1_tex_2(sK0,sK1)) | ~spl5_10),
% 1.10/0.69    inference(avatar_component_clause,[],[f191])).
% 1.10/0.69  fof(f495,plain,(
% 1.10/0.69    ~spl5_39 | spl5_11 | ~spl5_36),
% 1.10/0.69    inference(avatar_split_clause,[],[f488,f455,f196,f492])).
% 1.10/0.69  fof(f196,plain,(
% 1.10/0.69    spl5_11 <=> v2_struct_0(k1_tex_2(sK0,sK1))),
% 1.10/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.10/0.69  fof(f488,plain,(
% 1.10/0.69    ~v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | (spl5_11 | ~spl5_36)),
% 1.10/0.69    inference(unit_resulting_resolution,[],[f198,f457,f88])).
% 1.10/0.69  fof(f88,plain,(
% 1.10/0.69    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.10/0.69    inference(cnf_transformation,[],[f40])).
% 1.10/0.69  fof(f40,plain,(
% 1.10/0.69    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.10/0.69    inference(flattening,[],[f39])).
% 1.10/0.69  fof(f39,plain,(
% 1.10/0.69    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.10/0.69    inference(ennf_transformation,[],[f8])).
% 1.10/0.69  fof(f8,axiom,(
% 1.10/0.69    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.10/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.10/0.69  fof(f198,plain,(
% 1.10/0.69    ~v2_struct_0(k1_tex_2(sK0,sK1)) | spl5_11),
% 1.10/0.69    inference(avatar_component_clause,[],[f196])).
% 1.10/0.69  fof(f458,plain,(
% 1.10/0.69    spl5_36 | ~spl5_30),
% 1.10/0.69    inference(avatar_split_clause,[],[f420,f396,f455])).
% 1.10/0.69  fof(f396,plain,(
% 1.10/0.69    spl5_30 <=> l1_pre_topc(k1_tex_2(sK0,sK1))),
% 1.10/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 1.10/0.69  fof(f420,plain,(
% 1.10/0.69    l1_struct_0(k1_tex_2(sK0,sK1)) | ~spl5_30),
% 1.10/0.69    inference(unit_resulting_resolution,[],[f398,f78])).
% 1.10/0.69  fof(f78,plain,(
% 1.10/0.69    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.10/0.69    inference(cnf_transformation,[],[f30])).
% 1.10/0.69  fof(f30,plain,(
% 1.10/0.69    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.10/0.69    inference(ennf_transformation,[],[f6])).
% 1.10/0.69  fof(f6,axiom,(
% 1.10/0.69    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.10/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.10/0.69  fof(f398,plain,(
% 1.10/0.69    l1_pre_topc(k1_tex_2(sK0,sK1)) | ~spl5_30),
% 1.10/0.69    inference(avatar_component_clause,[],[f396])).
% 1.10/0.69  fof(f401,plain,(
% 1.10/0.69    spl5_30 | ~spl5_4 | ~spl5_12),
% 1.10/0.69    inference(avatar_split_clause,[],[f400,f201,f124,f396])).
% 1.10/0.69  fof(f400,plain,(
% 1.10/0.69    l1_pre_topc(k1_tex_2(sK0,sK1)) | (~spl5_4 | ~spl5_12)),
% 1.10/0.69    inference(subsumption_resolution,[],[f372,f126])).
% 1.10/0.69  fof(f372,plain,(
% 1.10/0.69    l1_pre_topc(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl5_12),
% 1.10/0.69    inference(resolution,[],[f203,f79])).
% 1.10/0.69  fof(f79,plain,(
% 1.10/0.69    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.10/0.69    inference(cnf_transformation,[],[f31])).
% 1.10/0.69  fof(f31,plain,(
% 1.10/0.69    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.10/0.69    inference(ennf_transformation,[],[f7])).
% 1.10/0.69  fof(f7,axiom,(
% 1.10/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.10/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.10/0.69  fof(f394,plain,(
% 1.10/0.69    spl5_29 | ~spl5_4 | ~spl5_12),
% 1.10/0.69    inference(avatar_split_clause,[],[f368,f201,f124,f391])).
% 1.10/0.69  fof(f368,plain,(
% 1.10/0.69    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_4 | ~spl5_12)),
% 1.10/0.69    inference(unit_resulting_resolution,[],[f126,f203,f80])).
% 1.10/0.69  fof(f80,plain,(
% 1.10/0.69    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.10/0.69    inference(cnf_transformation,[],[f32])).
% 1.10/0.69  fof(f32,plain,(
% 1.10/0.69    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.10/0.69    inference(ennf_transformation,[],[f10])).
% 1.10/0.69  fof(f10,axiom,(
% 1.10/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.10/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.10/0.69  fof(f384,plain,(
% 1.10/0.69    spl5_14 | spl5_1 | ~spl5_4 | ~spl5_12),
% 1.10/0.69    inference(avatar_split_clause,[],[f370,f201,f124,f109,f228])).
% 1.10/0.69  fof(f370,plain,(
% 1.10/0.69    sK2(sK0,k1_tex_2(sK0,sK1)) = u1_struct_0(k1_tex_2(sK0,sK1)) | (spl5_1 | ~spl5_4 | ~spl5_12)),
% 1.10/0.69    inference(unit_resulting_resolution,[],[f126,f111,f203,f83])).
% 1.10/0.69  fof(f83,plain,(
% 1.10/0.69    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.10/0.69    inference(cnf_transformation,[],[f64])).
% 1.10/0.69  fof(f111,plain,(
% 1.10/0.69    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | spl5_1),
% 1.10/0.69    inference(avatar_component_clause,[],[f109])).
% 1.10/0.69  fof(f239,plain,(
% 1.10/0.69    spl5_13 | ~spl5_15 | ~spl5_2 | ~spl5_3),
% 1.10/0.69    inference(avatar_split_clause,[],[f234,f119,f113,f236,f219])).
% 1.10/0.69  fof(f234,plain,(
% 1.10/0.69    ~v1_zfmisc_1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl5_2 | ~spl5_3)),
% 1.10/0.69    inference(subsumption_resolution,[],[f232,f121])).
% 1.10/0.69  fof(f232,plain,(
% 1.10/0.69    ~v1_zfmisc_1(u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~spl5_2),
% 1.10/0.69    inference(resolution,[],[f114,f77])).
% 1.10/0.69  fof(f77,plain,(
% 1.10/0.69    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.10/0.69    inference(cnf_transformation,[],[f29])).
% 1.10/0.69  fof(f29,plain,(
% 1.10/0.69    ! [X0] : (! [X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 1.10/0.69    inference(flattening,[],[f28])).
% 1.10/0.69  fof(f28,plain,(
% 1.10/0.69    ! [X0] : (! [X1] : ((~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0)) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 1.10/0.69    inference(ennf_transformation,[],[f19])).
% 1.10/0.69  fof(f19,axiom,(
% 1.10/0.69    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 1.10/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 1.10/0.69  fof(f114,plain,(
% 1.10/0.69    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl5_2),
% 1.10/0.69    inference(avatar_component_clause,[],[f113])).
% 1.10/0.69  fof(f222,plain,(
% 1.10/0.69    ~spl5_13 | spl5_5 | ~spl5_6),
% 1.10/0.69    inference(avatar_split_clause,[],[f215,f150,f129,f219])).
% 1.10/0.69  fof(f129,plain,(
% 1.10/0.69    spl5_5 <=> v2_struct_0(sK0)),
% 1.10/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.10/0.69  fof(f150,plain,(
% 1.10/0.69    spl5_6 <=> l1_struct_0(sK0)),
% 1.10/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.10/0.69  fof(f215,plain,(
% 1.10/0.69    ~v1_xboole_0(u1_struct_0(sK0)) | (spl5_5 | ~spl5_6)),
% 1.10/0.69    inference(unit_resulting_resolution,[],[f131,f152,f88])).
% 1.10/0.69  fof(f152,plain,(
% 1.10/0.69    l1_struct_0(sK0) | ~spl5_6),
% 1.10/0.69    inference(avatar_component_clause,[],[f150])).
% 1.10/0.69  fof(f131,plain,(
% 1.10/0.69    ~v2_struct_0(sK0) | spl5_5),
% 1.10/0.69    inference(avatar_component_clause,[],[f129])).
% 1.10/0.69  fof(f214,plain,(
% 1.10/0.69    spl5_10 | ~spl5_3 | ~spl5_4 | spl5_5),
% 1.10/0.69    inference(avatar_split_clause,[],[f213,f129,f124,f119,f191])).
% 1.10/0.69  fof(f213,plain,(
% 1.10/0.69    v7_struct_0(k1_tex_2(sK0,sK1)) | (~spl5_3 | ~spl5_4 | spl5_5)),
% 1.10/0.69    inference(subsumption_resolution,[],[f212,f131])).
% 1.10/0.69  fof(f212,plain,(
% 1.10/0.69    v7_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | (~spl5_3 | ~spl5_4)),
% 1.10/0.69    inference(subsumption_resolution,[],[f187,f126])).
% 1.10/0.69  fof(f187,plain,(
% 1.10/0.69    v7_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_3),
% 1.10/0.69    inference(resolution,[],[f121,f101])).
% 1.10/0.69  fof(f101,plain,(
% 1.10/0.69    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.10/0.69    inference(cnf_transformation,[],[f52])).
% 1.10/0.69  fof(f52,plain,(
% 1.10/0.69    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.10/0.69    inference(flattening,[],[f51])).
% 1.10/0.69  fof(f51,plain,(
% 1.10/0.69    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.10/0.69    inference(ennf_transformation,[],[f25])).
% 1.10/0.69  fof(f25,plain,(
% 1.10/0.69    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.10/0.69    inference(pure_predicate_removal,[],[f16])).
% 1.10/0.69  fof(f16,axiom,(
% 1.10/0.69    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.10/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).
% 1.10/0.69  fof(f211,plain,(
% 1.10/0.69    ~spl5_11 | ~spl5_3 | ~spl5_4 | spl5_5),
% 1.10/0.69    inference(avatar_split_clause,[],[f210,f129,f124,f119,f196])).
% 1.10/0.69  fof(f210,plain,(
% 1.10/0.69    ~v2_struct_0(k1_tex_2(sK0,sK1)) | (~spl5_3 | ~spl5_4 | spl5_5)),
% 1.10/0.69    inference(subsumption_resolution,[],[f209,f131])).
% 1.10/0.69  fof(f209,plain,(
% 1.10/0.69    ~v2_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | (~spl5_3 | ~spl5_4)),
% 1.10/0.69    inference(subsumption_resolution,[],[f186,f126])).
% 1.10/0.69  fof(f186,plain,(
% 1.10/0.69    ~v2_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_3),
% 1.10/0.69    inference(resolution,[],[f121,f100])).
% 1.10/0.69  fof(f100,plain,(
% 1.10/0.69    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.10/0.69    inference(cnf_transformation,[],[f52])).
% 1.10/0.69  fof(f204,plain,(
% 1.10/0.69    spl5_12 | ~spl5_3 | ~spl5_4 | spl5_5),
% 1.10/0.69    inference(avatar_split_clause,[],[f181,f129,f124,f119,f201])).
% 1.10/0.69  fof(f181,plain,(
% 1.10/0.69    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | (~spl5_3 | ~spl5_4 | spl5_5)),
% 1.10/0.69    inference(unit_resulting_resolution,[],[f131,f126,f121,f103])).
% 1.10/0.69  fof(f103,plain,(
% 1.10/0.69    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.10/0.69    inference(cnf_transformation,[],[f54])).
% 1.10/0.69  fof(f54,plain,(
% 1.10/0.69    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.10/0.69    inference(flattening,[],[f53])).
% 1.10/0.69  fof(f53,plain,(
% 1.10/0.69    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.10/0.69    inference(ennf_transformation,[],[f24])).
% 1.10/0.69  fof(f24,plain,(
% 1.10/0.69    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.10/0.69    inference(pure_predicate_removal,[],[f15])).
% 1.10/0.69  fof(f15,axiom,(
% 1.10/0.69    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.10/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 1.10/0.69  fof(f153,plain,(
% 1.10/0.69    spl5_6 | ~spl5_4),
% 1.10/0.69    inference(avatar_split_clause,[],[f133,f124,f150])).
% 1.10/0.69  fof(f133,plain,(
% 1.10/0.69    l1_struct_0(sK0) | ~spl5_4),
% 1.10/0.69    inference(unit_resulting_resolution,[],[f126,f78])).
% 1.10/0.69  fof(f132,plain,(
% 1.10/0.69    ~spl5_5),
% 1.10/0.69    inference(avatar_split_clause,[],[f70,f129])).
% 1.10/0.69  fof(f70,plain,(
% 1.10/0.69    ~v2_struct_0(sK0)),
% 1.10/0.69    inference(cnf_transformation,[],[f60])).
% 1.10/0.69  fof(f60,plain,(
% 1.10/0.69    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.10/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f57,f59,f58])).
% 1.10/0.69  fof(f58,plain,(
% 1.10/0.69    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,X1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,X1),sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.10/0.69    introduced(choice_axiom,[])).
% 1.10/0.69  fof(f59,plain,(
% 1.10/0.69    ? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,X1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,X1),sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 1.10/0.69    introduced(choice_axiom,[])).
% 1.10/0.69  fof(f57,plain,(
% 1.10/0.69    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.10/0.69    inference(flattening,[],[f56])).
% 1.10/0.70  fof(f56,plain,(
% 1.10/0.70    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.10/0.70    inference(nnf_transformation,[],[f27])).
% 1.10/0.70  fof(f27,plain,(
% 1.10/0.70    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.10/0.70    inference(flattening,[],[f26])).
% 1.10/0.70  fof(f26,plain,(
% 1.10/0.70    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.10/0.70    inference(ennf_transformation,[],[f22])).
% 1.10/0.70  fof(f22,negated_conjecture,(
% 1.10/0.70    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 1.10/0.70    inference(negated_conjecture,[],[f21])).
% 1.10/0.70  fof(f21,conjecture,(
% 1.10/0.70    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 1.10/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).
% 1.10/0.70  fof(f127,plain,(
% 1.10/0.70    spl5_4),
% 1.10/0.70    inference(avatar_split_clause,[],[f71,f124])).
% 1.10/0.70  fof(f71,plain,(
% 1.10/0.70    l1_pre_topc(sK0)),
% 1.10/0.70    inference(cnf_transformation,[],[f60])).
% 1.10/0.70  fof(f122,plain,(
% 1.10/0.70    spl5_3),
% 1.10/0.70    inference(avatar_split_clause,[],[f72,f119])).
% 1.10/0.70  fof(f72,plain,(
% 1.10/0.70    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.10/0.70    inference(cnf_transformation,[],[f60])).
% 1.10/0.70  fof(f117,plain,(
% 1.10/0.70    spl5_1 | spl5_2),
% 1.10/0.70    inference(avatar_split_clause,[],[f73,f113,f109])).
% 1.10/0.70  fof(f73,plain,(
% 1.10/0.70    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 1.10/0.70    inference(cnf_transformation,[],[f60])).
% 1.10/0.70  fof(f116,plain,(
% 1.10/0.70    ~spl5_1 | ~spl5_2),
% 1.10/0.70    inference(avatar_split_clause,[],[f74,f113,f109])).
% 1.10/0.70  fof(f74,plain,(
% 1.10/0.70    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 1.10/0.70    inference(cnf_transformation,[],[f60])).
% 1.10/0.70  % SZS output end Proof for theBenchmark
% 1.10/0.70  % (29014)------------------------------
% 1.10/0.70  % (29014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.10/0.70  % (29014)Termination reason: Refutation
% 1.10/0.70  
% 1.10/0.70  % (29014)Memory used [KB]: 6524
% 1.10/0.70  % (29014)Time elapsed: 0.128 s
% 1.10/0.70  % (29014)------------------------------
% 1.10/0.70  % (29014)------------------------------
% 1.10/0.70  % (28990)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.10/0.70  % (29010)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.10/0.70  % (28993)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.10/0.70  % (28998)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.10/0.70  % (28833)Success in time 0.335 s
%------------------------------------------------------------------------------
