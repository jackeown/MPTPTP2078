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
% DateTime   : Thu Dec  3 13:20:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  202 ( 411 expanded)
%              Number of leaves         :   43 ( 161 expanded)
%              Depth                    :   12
%              Number of atoms          :  659 (1494 expanded)
%              Number of equality atoms :   24 ( 109 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f658,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f99,f104,f109,f114,f121,f127,f208,f216,f221,f246,f255,f260,f266,f272,f281,f286,f296,f319,f349,f377,f384,f510,f629,f646,f657])).

fof(f657,plain,
    ( spl7_16
    | ~ spl7_18
    | ~ spl7_21
    | ~ spl7_40 ),
    inference(avatar_contradiction_clause,[],[f656])).

fof(f656,plain,
    ( $false
    | spl7_16
    | ~ spl7_18
    | ~ spl7_21
    | ~ spl7_40 ),
    inference(subsumption_resolution,[],[f650,f285])).

fof(f285,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl7_18
  <=> m1_subset_1(u1_struct_0(k1_tex_2(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f650,plain,
    ( ~ m1_subset_1(u1_struct_0(k1_tex_2(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK4)))
    | spl7_16
    | ~ spl7_21
    | ~ spl7_40 ),
    inference(unit_resulting_resolution,[],[f506,f271,f322,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(subsumption_resolution,[],[f75,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

fof(f322,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK4,sK5)),u1_struct_0(sK4))
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f321])).

fof(f321,plain,
    ( spl7_21
  <=> v1_subset_1(u1_struct_0(k1_tex_2(sK4,sK5)),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f271,plain,
    ( ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK4,sK5)))
    | spl7_16 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl7_16
  <=> v1_xboole_0(u1_struct_0(k1_tex_2(sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f506,plain,
    ( v1_zfmisc_1(u1_struct_0(sK4))
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f504])).

fof(f504,plain,
    ( spl7_40
  <=> v1_zfmisc_1(u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f646,plain,
    ( ~ spl7_18
    | ~ spl7_19
    | spl7_21 ),
    inference(avatar_contradiction_clause,[],[f645])).

fof(f645,plain,
    ( $false
    | ~ spl7_18
    | ~ spl7_19
    | spl7_21 ),
    inference(subsumption_resolution,[],[f637,f285])).

fof(f637,plain,
    ( ~ m1_subset_1(u1_struct_0(k1_tex_2(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl7_19
    | spl7_21 ),
    inference(unit_resulting_resolution,[],[f292,f323,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ v1_subset_1(sK6(X0,X1),u1_struct_0(X0))
          & u1_struct_0(X1) = sK6(X0,X1)
          & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( v1_subset_1(X3,u1_struct_0(X0))
            | u1_struct_0(X1) != X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f51,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK6(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK6(X0,X1)
        & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ~ v1_subset_1(X2,u1_struct_0(X0))
            & u1_struct_0(X1) = X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( v1_subset_1(X3,u1_struct_0(X0))
            | u1_struct_0(X1) != X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ~ v1_subset_1(X2,u1_struct_0(X0))
            & u1_struct_0(X1) = X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( v1_subset_1(X2,u1_struct_0(X0))
            | u1_struct_0(X1) != X2
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( v1_subset_1(X2,u1_struct_0(X0))
          | u1_struct_0(X1) != X2
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f323,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK4,sK5)),u1_struct_0(sK4))
    | spl7_21 ),
    inference(avatar_component_clause,[],[f321])).

fof(f292,plain,
    ( sP0(sK4,k1_tex_2(sK4,sK5))
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl7_19
  <=> sP0(sK4,k1_tex_2(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f629,plain,
    ( spl7_9
    | ~ spl7_10
    | ~ spl7_15
    | ~ spl7_26
    | ~ spl7_27 ),
    inference(avatar_contradiction_clause,[],[f628])).

fof(f628,plain,
    ( $false
    | spl7_9
    | ~ spl7_10
    | ~ spl7_15
    | ~ spl7_26
    | ~ spl7_27 ),
    inference(subsumption_resolution,[],[f623,f353])).

fof(f353,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(sK4,sK5)),sK5),u1_struct_0(k1_tex_2(sK4,sK5)))
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f351])).

fof(f351,plain,
    ( spl7_27
  <=> v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(sK4,sK5)),sK5),u1_struct_0(k1_tex_2(sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f623,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(sK4,sK5)),sK5),u1_struct_0(k1_tex_2(sK4,sK5)))
    | spl7_9
    | ~ spl7_10
    | ~ spl7_15
    | ~ spl7_26 ),
    inference(unit_resulting_resolution,[],[f215,f265,f220,f348,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ v7_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

fof(f348,plain,
    ( m1_subset_1(sK5,u1_struct_0(k1_tex_2(sK4,sK5)))
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f346])).

fof(f346,plain,
    ( spl7_26
  <=> m1_subset_1(sK5,u1_struct_0(k1_tex_2(sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f220,plain,
    ( v7_struct_0(k1_tex_2(sK4,sK5))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl7_10
  <=> v7_struct_0(k1_tex_2(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f265,plain,
    ( l1_struct_0(k1_tex_2(sK4,sK5))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f263])).

fof(f263,plain,
    ( spl7_15
  <=> l1_struct_0(k1_tex_2(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f215,plain,
    ( ~ v2_struct_0(k1_tex_2(sK4,sK5))
    | spl7_9 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl7_9
  <=> v2_struct_0(k1_tex_2(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f510,plain,
    ( spl7_40
    | spl7_2
    | ~ spl7_3
    | spl7_7 ),
    inference(avatar_split_clause,[],[f509,f124,f101,f95,f504])).

fof(f95,plain,
    ( spl7_2
  <=> v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f101,plain,
    ( spl7_3
  <=> m1_subset_1(sK5,u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f124,plain,
    ( spl7_7
  <=> v1_xboole_0(u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f509,plain,
    ( v1_zfmisc_1(u1_struct_0(sK4))
    | spl7_2
    | ~ spl7_3
    | spl7_7 ),
    inference(subsumption_resolution,[],[f508,f126])).

fof(f126,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | spl7_7 ),
    inference(avatar_component_clause,[],[f124])).

fof(f508,plain,
    ( v1_zfmisc_1(u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f502,f103])).

fof(f103,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f502,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | v1_zfmisc_1(u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | spl7_2 ),
    inference(resolution,[],[f74,f97])).

fof(f97,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

fof(f384,plain,
    ( spl7_19
    | ~ spl7_1
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f383,f278,f91,f291])).

fof(f91,plain,
    ( spl7_1
  <=> v1_tex_2(k1_tex_2(sK4,sK5),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f278,plain,
    ( spl7_17
  <=> sP1(k1_tex_2(sK4,sK5),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f383,plain,
    ( sP0(sK4,k1_tex_2(sK4,sK5))
    | ~ spl7_1
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f289,f92])).

fof(f92,plain,
    ( v1_tex_2(k1_tex_2(sK4,sK5),sK4)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f289,plain,
    ( ~ v1_tex_2(k1_tex_2(sK4,sK5),sK4)
    | sP0(sK4,k1_tex_2(sK4,sK5))
    | ~ spl7_17 ),
    inference(resolution,[],[f280,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v1_tex_2(X0,X1)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v1_tex_2(X0,X1)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v1_tex_2(X0,X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ( ( v1_tex_2(X1,X0)
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v1_tex_2(X1,X0) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ( v1_tex_2(X1,X0)
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f280,plain,
    ( sP1(k1_tex_2(sK4,sK5),sK4)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f278])).

fof(f377,plain,
    ( ~ spl7_2
    | ~ spl7_20
    | spl7_27 ),
    inference(avatar_split_clause,[],[f364,f351,f316,f95])).

fof(f316,plain,
    ( spl7_20
  <=> u1_struct_0(sK4) = u1_struct_0(k1_tex_2(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f364,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
    | ~ spl7_20
    | spl7_27 ),
    inference(backward_demodulation,[],[f352,f318])).

fof(f318,plain,
    ( u1_struct_0(sK4) = u1_struct_0(k1_tex_2(sK4,sK5))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f316])).

fof(f352,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(sK4,sK5)),sK5),u1_struct_0(k1_tex_2(sK4,sK5)))
    | spl7_27 ),
    inference(avatar_component_clause,[],[f351])).

fof(f349,plain,
    ( spl7_26
    | ~ spl7_3
    | spl7_19 ),
    inference(avatar_split_clause,[],[f301,f291,f101,f346])).

fof(f301,plain,
    ( m1_subset_1(sK5,u1_struct_0(k1_tex_2(sK4,sK5)))
    | ~ spl7_3
    | spl7_19 ),
    inference(unit_resulting_resolution,[],[f293,f148])).

fof(f148,plain,
    ( ! [X2] :
        ( m1_subset_1(sK5,u1_struct_0(X2))
        | sP0(sK4,X2) )
    | ~ spl7_3 ),
    inference(superposition,[],[f103,f141])).

fof(f141,plain,(
    ! [X2,X3] :
      ( u1_struct_0(X2) = u1_struct_0(X3)
      | sP0(X2,X3) ) ),
    inference(subsumption_resolution,[],[f139,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | sP0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | sP0(X0,X1)
      | sP0(X0,X1) ) ),
    inference(superposition,[],[f71,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X1) = sK6(X0,X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK6(X0,X1),u1_struct_0(X0))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f139,plain,(
    ! [X2,X3] :
      ( u1_struct_0(X2) = u1_struct_0(X3)
      | v1_subset_1(u1_struct_0(X3),u1_struct_0(X2))
      | sP0(X2,X3) ) ),
    inference(resolution,[],[f79,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | sP0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | sP0(X0,X1)
      | sP0(X0,X1) ) ),
    inference(superposition,[],[f69,f70])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f293,plain,
    ( ~ sP0(sK4,k1_tex_2(sK4,sK5))
    | spl7_19 ),
    inference(avatar_component_clause,[],[f291])).

fof(f319,plain,
    ( spl7_20
    | spl7_19 ),
    inference(avatar_split_clause,[],[f311,f291,f316])).

fof(f311,plain,
    ( u1_struct_0(sK4) = u1_struct_0(k1_tex_2(sK4,sK5))
    | spl7_19 ),
    inference(unit_resulting_resolution,[],[f293,f141])).

fof(f296,plain,
    ( ~ spl7_19
    | spl7_1
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f295,f278,f91,f291])).

fof(f295,plain,
    ( ~ sP0(sK4,k1_tex_2(sK4,sK5))
    | spl7_1
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f288,f93])).

fof(f93,plain,
    ( ~ v1_tex_2(k1_tex_2(sK4,sK5),sK4)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f288,plain,
    ( ~ sP0(sK4,k1_tex_2(sK4,sK5))
    | v1_tex_2(k1_tex_2(sK4,sK5),sK4)
    | ~ spl7_17 ),
    inference(resolution,[],[f280,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v1_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f286,plain,
    ( spl7_18
    | ~ spl7_4
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f273,f252,f106,f283])).

fof(f106,plain,
    ( spl7_4
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f252,plain,
    ( spl7_13
  <=> m1_pre_topc(k1_tex_2(sK4,sK5),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f273,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl7_4
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f108,f254,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f254,plain,
    ( m1_pre_topc(k1_tex_2(sK4,sK5),sK4)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f252])).

fof(f108,plain,
    ( l1_pre_topc(sK4)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f281,plain,
    ( spl7_17
    | ~ spl7_4
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f274,f252,f106,f278])).

fof(f274,plain,
    ( sP1(k1_tex_2(sK4,sK5),sK4)
    | ~ spl7_4
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f108,f254,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f21,f37,f36])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f272,plain,
    ( ~ spl7_16
    | spl7_9
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f267,f263,f213,f269])).

fof(f267,plain,
    ( ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK4,sK5)))
    | spl7_9
    | ~ spl7_15 ),
    inference(unit_resulting_resolution,[],[f215,f265,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f266,plain,
    ( spl7_15
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f261,f257,f263])).

fof(f257,plain,
    ( spl7_14
  <=> l1_pre_topc(k1_tex_2(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f261,plain,
    ( l1_struct_0(k1_tex_2(sK4,sK5))
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f259,f63])).

fof(f63,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f259,plain,
    ( l1_pre_topc(k1_tex_2(sK4,sK5))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f257])).

fof(f260,plain,
    ( spl7_14
    | ~ spl7_4
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f247,f240,f106,f257])).

fof(f240,plain,
    ( spl7_12
  <=> sP3(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f247,plain,
    ( l1_pre_topc(k1_tex_2(sK4,sK5))
    | ~ spl7_4
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f108,f242,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k1_tex_2(X0,X1))
      | ~ sP3(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f86,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ sP3(X0,X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ sP3(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f242,plain,
    ( sP3(sK4,sK5)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f240])).

fof(f255,plain,
    ( spl7_13
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f248,f240,f252])).

fof(f248,plain,
    ( m1_pre_topc(k1_tex_2(sK4,sK5),sK4)
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f242,f86])).

fof(f246,plain,
    ( spl7_12
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5 ),
    inference(avatar_split_clause,[],[f245,f111,f106,f101,f240])).

fof(f111,plain,
    ( spl7_5
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f245,plain,
    ( sP3(sK4,sK5)
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5 ),
    inference(subsumption_resolution,[],[f244,f113])).

fof(f113,plain,
    ( ~ v2_struct_0(sK4)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f244,plain,
    ( sP3(sK4,sK5)
    | v2_struct_0(sK4)
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f230,f108])).

fof(f230,plain,
    ( sP3(sK4,sK5)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl7_3 ),
    inference(resolution,[],[f87,f103])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP3(X0,X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f35,f41])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f221,plain,
    ( spl7_10
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f210,f202,f218])).

fof(f202,plain,
    ( spl7_8
  <=> sP2(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f210,plain,
    ( v7_struct_0(k1_tex_2(sK4,sK5))
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f204,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X1,X0))
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X1,X0))
        & v7_struct_0(k1_tex_2(X1,X0))
        & ~ v2_struct_0(k1_tex_2(X1,X0)) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f204,plain,
    ( sP2(sK5,sK4)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f202])).

fof(f216,plain,
    ( ~ spl7_9
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f211,f202,f213])).

fof(f211,plain,
    ( ~ v2_struct_0(k1_tex_2(sK4,sK5))
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f204,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X1,X0))
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f208,plain,
    ( spl7_8
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5 ),
    inference(avatar_split_clause,[],[f207,f111,f106,f101,f202])).

fof(f207,plain,
    ( sP2(sK5,sK4)
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5 ),
    inference(subsumption_resolution,[],[f206,f113])).

fof(f206,plain,
    ( sP2(sK5,sK4)
    | v2_struct_0(sK4)
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f192,f108])).

fof(f192,plain,
    ( sP2(sK5,sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl7_3 ),
    inference(resolution,[],[f83,f103])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP2(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( sP2(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f33,f39])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f127,plain,
    ( ~ spl7_7
    | spl7_5
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f122,f118,f111,f124])).

fof(f118,plain,
    ( spl7_6
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f122,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | spl7_5
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f113,f120,f76])).

% (15992)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (15999)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% (15982)Refutation not found, incomplete strategy% (15982)------------------------------
% (15982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15982)Termination reason: Refutation not found, incomplete strategy

% (15982)Memory used [KB]: 10618
% (15982)Time elapsed: 0.060 s
% (15982)------------------------------
% (15982)------------------------------
% (15983)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f120,plain,
    ( l1_struct_0(sK4)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f118])).

fof(f121,plain,
    ( spl7_6
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f116,f106,f118])).

fof(f116,plain,
    ( l1_struct_0(sK4)
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f108,f63])).

fof(f114,plain,(
    ~ spl7_5 ),
    inference(avatar_split_clause,[],[f58,f111])).

fof(f58,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
      | ~ v1_tex_2(k1_tex_2(sK4,sK5),sK4) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
      | v1_tex_2(k1_tex_2(sK4,sK5),sK4) )
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f44,f46,f45])).

fof(f45,plain,
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
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK4),X1),u1_struct_0(sK4))
            | ~ v1_tex_2(k1_tex_2(sK4,X1),sK4) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(sK4),X1),u1_struct_0(sK4))
            | v1_tex_2(k1_tex_2(sK4,X1),sK4) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X1] :
        ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK4),X1),u1_struct_0(sK4))
          | ~ v1_tex_2(k1_tex_2(sK4,X1),sK4) )
        & ( v1_subset_1(k6_domain_1(u1_struct_0(sK4),X1),u1_struct_0(sK4))
          | v1_tex_2(k1_tex_2(sK4,X1),sK4) )
        & m1_subset_1(X1,u1_struct_0(sK4)) )
   => ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
        | ~ v1_tex_2(k1_tex_2(sK4,sK5),sK4) )
      & ( v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
        | v1_tex_2(k1_tex_2(sK4,sK5),sK4) )
      & m1_subset_1(sK5,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

fof(f109,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f59,f106])).

fof(f59,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f104,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f60,f101])).

fof(f60,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f47])).

fof(f99,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f61,f95,f91])).

fof(f61,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
    | v1_tex_2(k1_tex_2(sK4,sK5),sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f98,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f62,f95,f91])).

fof(f62,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
    | ~ v1_tex_2(k1_tex_2(sK4,sK5),sK4) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:13:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (15997)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.44  % (15989)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.46  % (15982)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (15997)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f658,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f98,f99,f104,f109,f114,f121,f127,f208,f216,f221,f246,f255,f260,f266,f272,f281,f286,f296,f319,f349,f377,f384,f510,f629,f646,f657])).
% 0.21/0.46  fof(f657,plain,(
% 0.21/0.46    spl7_16 | ~spl7_18 | ~spl7_21 | ~spl7_40),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f656])).
% 0.21/0.46  fof(f656,plain,(
% 0.21/0.46    $false | (spl7_16 | ~spl7_18 | ~spl7_21 | ~spl7_40)),
% 0.21/0.46    inference(subsumption_resolution,[],[f650,f285])).
% 0.21/0.46  fof(f285,plain,(
% 0.21/0.46    m1_subset_1(u1_struct_0(k1_tex_2(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK4))) | ~spl7_18),
% 0.21/0.46    inference(avatar_component_clause,[],[f283])).
% 0.21/0.46  fof(f283,plain,(
% 0.21/0.46    spl7_18 <=> m1_subset_1(u1_struct_0(k1_tex_2(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK4)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.46  fof(f650,plain,(
% 0.21/0.46    ~m1_subset_1(u1_struct_0(k1_tex_2(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK4))) | (spl7_16 | ~spl7_21 | ~spl7_40)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f506,f271,f322,f115])).
% 0.21/0.46  fof(f115,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~v1_zfmisc_1(X0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f75,f73])).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.21/0.46    inference(flattening,[],[f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.21/0.46  fof(f322,plain,(
% 0.21/0.46    v1_subset_1(u1_struct_0(k1_tex_2(sK4,sK5)),u1_struct_0(sK4)) | ~spl7_21),
% 0.21/0.46    inference(avatar_component_clause,[],[f321])).
% 0.21/0.46  fof(f321,plain,(
% 0.21/0.46    spl7_21 <=> v1_subset_1(u1_struct_0(k1_tex_2(sK4,sK5)),u1_struct_0(sK4))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.21/0.46  fof(f271,plain,(
% 0.21/0.46    ~v1_xboole_0(u1_struct_0(k1_tex_2(sK4,sK5))) | spl7_16),
% 0.21/0.46    inference(avatar_component_clause,[],[f269])).
% 0.21/0.46  fof(f269,plain,(
% 0.21/0.46    spl7_16 <=> v1_xboole_0(u1_struct_0(k1_tex_2(sK4,sK5)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.46  fof(f506,plain,(
% 0.21/0.46    v1_zfmisc_1(u1_struct_0(sK4)) | ~spl7_40),
% 0.21/0.46    inference(avatar_component_clause,[],[f504])).
% 0.21/0.46  fof(f504,plain,(
% 0.21/0.46    spl7_40 <=> v1_zfmisc_1(u1_struct_0(sK4))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).
% 0.21/0.46  fof(f646,plain,(
% 0.21/0.46    ~spl7_18 | ~spl7_19 | spl7_21),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f645])).
% 0.21/0.46  fof(f645,plain,(
% 0.21/0.46    $false | (~spl7_18 | ~spl7_19 | spl7_21)),
% 0.21/0.46    inference(subsumption_resolution,[],[f637,f285])).
% 0.21/0.46  fof(f637,plain,(
% 0.21/0.46    ~m1_subset_1(u1_struct_0(k1_tex_2(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK4))) | (~spl7_19 | spl7_21)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f292,f323,f88])).
% 0.21/0.46  fof(f88,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~sP0(X0,X1)) )),
% 0.21/0.46    inference(equality_resolution,[],[f68])).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f53])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    ! [X0,X1] : ((sP0(X0,X1) | (~v1_subset_1(sK6(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK6(X0,X1) & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f51,f52])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK6(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK6(X0,X1) & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 0.21/0.46    inference(rectify,[],[f50])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 0.21/0.46    inference(nnf_transformation,[],[f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.46  fof(f323,plain,(
% 0.21/0.46    ~v1_subset_1(u1_struct_0(k1_tex_2(sK4,sK5)),u1_struct_0(sK4)) | spl7_21),
% 0.21/0.46    inference(avatar_component_clause,[],[f321])).
% 0.21/0.46  fof(f292,plain,(
% 0.21/0.46    sP0(sK4,k1_tex_2(sK4,sK5)) | ~spl7_19),
% 0.21/0.46    inference(avatar_component_clause,[],[f291])).
% 0.21/0.46  fof(f291,plain,(
% 0.21/0.46    spl7_19 <=> sP0(sK4,k1_tex_2(sK4,sK5))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.46  fof(f629,plain,(
% 0.21/0.46    spl7_9 | ~spl7_10 | ~spl7_15 | ~spl7_26 | ~spl7_27),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f628])).
% 0.21/0.46  fof(f628,plain,(
% 0.21/0.46    $false | (spl7_9 | ~spl7_10 | ~spl7_15 | ~spl7_26 | ~spl7_27)),
% 0.21/0.46    inference(subsumption_resolution,[],[f623,f353])).
% 0.21/0.46  fof(f353,plain,(
% 0.21/0.46    v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(sK4,sK5)),sK5),u1_struct_0(k1_tex_2(sK4,sK5))) | ~spl7_27),
% 0.21/0.46    inference(avatar_component_clause,[],[f351])).
% 0.21/0.46  fof(f351,plain,(
% 0.21/0.46    spl7_27 <=> v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(sK4,sK5)),sK5),u1_struct_0(k1_tex_2(sK4,sK5)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.21/0.46  fof(f623,plain,(
% 0.21/0.46    ~v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(sK4,sK5)),sK5),u1_struct_0(k1_tex_2(sK4,sK5))) | (spl7_9 | ~spl7_10 | ~spl7_15 | ~spl7_26)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f215,f265,f220,f348,f77])).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v7_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f30])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,axiom,(
% 0.21/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).
% 0.21/0.46  fof(f348,plain,(
% 0.21/0.46    m1_subset_1(sK5,u1_struct_0(k1_tex_2(sK4,sK5))) | ~spl7_26),
% 0.21/0.46    inference(avatar_component_clause,[],[f346])).
% 0.21/0.46  fof(f346,plain,(
% 0.21/0.46    spl7_26 <=> m1_subset_1(sK5,u1_struct_0(k1_tex_2(sK4,sK5)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.21/0.46  fof(f220,plain,(
% 0.21/0.46    v7_struct_0(k1_tex_2(sK4,sK5)) | ~spl7_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f218])).
% 0.21/0.46  fof(f218,plain,(
% 0.21/0.46    spl7_10 <=> v7_struct_0(k1_tex_2(sK4,sK5))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.46  fof(f265,plain,(
% 0.21/0.46    l1_struct_0(k1_tex_2(sK4,sK5)) | ~spl7_15),
% 0.21/0.46    inference(avatar_component_clause,[],[f263])).
% 0.21/0.46  fof(f263,plain,(
% 0.21/0.46    spl7_15 <=> l1_struct_0(k1_tex_2(sK4,sK5))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.46  fof(f215,plain,(
% 0.21/0.46    ~v2_struct_0(k1_tex_2(sK4,sK5)) | spl7_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f213])).
% 0.21/0.46  fof(f213,plain,(
% 0.21/0.46    spl7_9 <=> v2_struct_0(k1_tex_2(sK4,sK5))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.46  fof(f510,plain,(
% 0.21/0.46    spl7_40 | spl7_2 | ~spl7_3 | spl7_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f509,f124,f101,f95,f504])).
% 0.21/0.46  fof(f95,plain,(
% 0.21/0.46    spl7_2 <=> v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    spl7_3 <=> m1_subset_1(sK5,u1_struct_0(sK4))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.46  fof(f124,plain,(
% 0.21/0.46    spl7_7 <=> v1_xboole_0(u1_struct_0(sK4))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.46  fof(f509,plain,(
% 0.21/0.46    v1_zfmisc_1(u1_struct_0(sK4)) | (spl7_2 | ~spl7_3 | spl7_7)),
% 0.21/0.46    inference(subsumption_resolution,[],[f508,f126])).
% 0.21/0.46  fof(f126,plain,(
% 0.21/0.46    ~v1_xboole_0(u1_struct_0(sK4)) | spl7_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f124])).
% 0.21/0.46  fof(f508,plain,(
% 0.21/0.46    v1_zfmisc_1(u1_struct_0(sK4)) | v1_xboole_0(u1_struct_0(sK4)) | (spl7_2 | ~spl7_3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f502,f103])).
% 0.21/0.46  fof(f103,plain,(
% 0.21/0.46    m1_subset_1(sK5,u1_struct_0(sK4)) | ~spl7_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f101])).
% 0.21/0.46  fof(f502,plain,(
% 0.21/0.46    ~m1_subset_1(sK5,u1_struct_0(sK4)) | v1_zfmisc_1(u1_struct_0(sK4)) | v1_xboole_0(u1_struct_0(sK4)) | spl7_2),
% 0.21/0.46    inference(resolution,[],[f74,f97])).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    ~v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) | spl7_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f95])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.21/0.46    inference(flattening,[],[f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,axiom,(
% 0.21/0.46    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).
% 0.21/0.46  fof(f384,plain,(
% 0.21/0.46    spl7_19 | ~spl7_1 | ~spl7_17),
% 0.21/0.46    inference(avatar_split_clause,[],[f383,f278,f91,f291])).
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    spl7_1 <=> v1_tex_2(k1_tex_2(sK4,sK5),sK4)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.46  fof(f278,plain,(
% 0.21/0.46    spl7_17 <=> sP1(k1_tex_2(sK4,sK5),sK4)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.21/0.46  fof(f383,plain,(
% 0.21/0.46    sP0(sK4,k1_tex_2(sK4,sK5)) | (~spl7_1 | ~spl7_17)),
% 0.21/0.46    inference(subsumption_resolution,[],[f289,f92])).
% 0.21/0.46  fof(f92,plain,(
% 0.21/0.46    v1_tex_2(k1_tex_2(sK4,sK5),sK4) | ~spl7_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f91])).
% 0.21/0.46  fof(f289,plain,(
% 0.21/0.46    ~v1_tex_2(k1_tex_2(sK4,sK5),sK4) | sP0(sK4,k1_tex_2(sK4,sK5)) | ~spl7_17),
% 0.21/0.46    inference(resolution,[],[f280,f66])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~sP1(X0,X1) | ~v1_tex_2(X0,X1) | sP0(X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f49])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    ! [X0,X1] : (((v1_tex_2(X0,X1) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v1_tex_2(X0,X1))) | ~sP1(X0,X1))),
% 0.21/0.46    inference(rectify,[],[f48])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    ! [X1,X0] : (((v1_tex_2(X1,X0) | ~sP0(X0,X1)) & (sP0(X0,X1) | ~v1_tex_2(X1,X0))) | ~sP1(X1,X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f37])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ! [X1,X0] : ((v1_tex_2(X1,X0) <=> sP0(X0,X1)) | ~sP1(X1,X0))),
% 0.21/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.46  fof(f280,plain,(
% 0.21/0.46    sP1(k1_tex_2(sK4,sK5),sK4) | ~spl7_17),
% 0.21/0.46    inference(avatar_component_clause,[],[f278])).
% 0.21/0.46  fof(f377,plain,(
% 0.21/0.46    ~spl7_2 | ~spl7_20 | spl7_27),
% 0.21/0.46    inference(avatar_split_clause,[],[f364,f351,f316,f95])).
% 0.21/0.46  fof(f316,plain,(
% 0.21/0.46    spl7_20 <=> u1_struct_0(sK4) = u1_struct_0(k1_tex_2(sK4,sK5))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.21/0.46  fof(f364,plain,(
% 0.21/0.46    ~v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) | (~spl7_20 | spl7_27)),
% 0.21/0.46    inference(backward_demodulation,[],[f352,f318])).
% 0.21/0.46  fof(f318,plain,(
% 0.21/0.46    u1_struct_0(sK4) = u1_struct_0(k1_tex_2(sK4,sK5)) | ~spl7_20),
% 0.21/0.46    inference(avatar_component_clause,[],[f316])).
% 0.21/0.46  fof(f352,plain,(
% 0.21/0.46    ~v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(sK4,sK5)),sK5),u1_struct_0(k1_tex_2(sK4,sK5))) | spl7_27),
% 0.21/0.46    inference(avatar_component_clause,[],[f351])).
% 0.21/0.46  fof(f349,plain,(
% 0.21/0.46    spl7_26 | ~spl7_3 | spl7_19),
% 0.21/0.46    inference(avatar_split_clause,[],[f301,f291,f101,f346])).
% 0.21/0.46  fof(f301,plain,(
% 0.21/0.46    m1_subset_1(sK5,u1_struct_0(k1_tex_2(sK4,sK5))) | (~spl7_3 | spl7_19)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f293,f148])).
% 0.21/0.46  fof(f148,plain,(
% 0.21/0.46    ( ! [X2] : (m1_subset_1(sK5,u1_struct_0(X2)) | sP0(sK4,X2)) ) | ~spl7_3),
% 0.21/0.46    inference(superposition,[],[f103,f141])).
% 0.21/0.46  fof(f141,plain,(
% 0.21/0.46    ( ! [X2,X3] : (u1_struct_0(X2) = u1_struct_0(X3) | sP0(X2,X3)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f139,f132])).
% 0.21/0.46  fof(f132,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | sP0(X0,X1)) )),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f131])).
% 0.21/0.46  fof(f131,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | sP0(X0,X1) | sP0(X0,X1)) )),
% 0.21/0.46    inference(superposition,[],[f71,f70])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    ( ! [X0,X1] : (u1_struct_0(X1) = sK6(X0,X1) | sP0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f53])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_subset_1(sK6(X0,X1),u1_struct_0(X0)) | sP0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f53])).
% 0.21/0.46  fof(f139,plain,(
% 0.21/0.46    ( ! [X2,X3] : (u1_struct_0(X2) = u1_struct_0(X3) | v1_subset_1(u1_struct_0(X3),u1_struct_0(X2)) | sP0(X2,X3)) )),
% 0.21/0.46    inference(resolution,[],[f79,f135])).
% 0.21/0.46  fof(f135,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | sP0(X0,X1)) )),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f134])).
% 0.21/0.46  fof(f134,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | sP0(X0,X1) | sP0(X0,X1)) )),
% 0.21/0.46    inference(superposition,[],[f69,f70])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | sP0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f53])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f54])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    inference(nnf_transformation,[],[f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.46  fof(f293,plain,(
% 0.21/0.46    ~sP0(sK4,k1_tex_2(sK4,sK5)) | spl7_19),
% 0.21/0.46    inference(avatar_component_clause,[],[f291])).
% 0.21/0.46  fof(f319,plain,(
% 0.21/0.46    spl7_20 | spl7_19),
% 0.21/0.46    inference(avatar_split_clause,[],[f311,f291,f316])).
% 0.21/0.46  fof(f311,plain,(
% 0.21/0.46    u1_struct_0(sK4) = u1_struct_0(k1_tex_2(sK4,sK5)) | spl7_19),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f293,f141])).
% 0.21/0.46  fof(f296,plain,(
% 0.21/0.46    ~spl7_19 | spl7_1 | ~spl7_17),
% 0.21/0.46    inference(avatar_split_clause,[],[f295,f278,f91,f291])).
% 0.21/0.46  fof(f295,plain,(
% 0.21/0.46    ~sP0(sK4,k1_tex_2(sK4,sK5)) | (spl7_1 | ~spl7_17)),
% 0.21/0.46    inference(subsumption_resolution,[],[f288,f93])).
% 0.21/0.46  fof(f93,plain,(
% 0.21/0.46    ~v1_tex_2(k1_tex_2(sK4,sK5),sK4) | spl7_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f91])).
% 0.21/0.46  fof(f288,plain,(
% 0.21/0.46    ~sP0(sK4,k1_tex_2(sK4,sK5)) | v1_tex_2(k1_tex_2(sK4,sK5),sK4) | ~spl7_17),
% 0.21/0.46    inference(resolution,[],[f280,f67])).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~sP1(X0,X1) | ~sP0(X1,X0) | v1_tex_2(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f49])).
% 0.21/0.46  fof(f286,plain,(
% 0.21/0.46    spl7_18 | ~spl7_4 | ~spl7_13),
% 0.21/0.46    inference(avatar_split_clause,[],[f273,f252,f106,f283])).
% 0.21/0.46  fof(f106,plain,(
% 0.21/0.46    spl7_4 <=> l1_pre_topc(sK4)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.46  fof(f252,plain,(
% 0.21/0.46    spl7_13 <=> m1_pre_topc(k1_tex_2(sK4,sK5),sK4)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.46  fof(f273,plain,(
% 0.21/0.46    m1_subset_1(u1_struct_0(k1_tex_2(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK4))) | (~spl7_4 | ~spl7_13)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f108,f254,f65])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.46  fof(f254,plain,(
% 0.21/0.46    m1_pre_topc(k1_tex_2(sK4,sK5),sK4) | ~spl7_13),
% 0.21/0.46    inference(avatar_component_clause,[],[f252])).
% 0.21/0.46  fof(f108,plain,(
% 0.21/0.46    l1_pre_topc(sK4) | ~spl7_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f106])).
% 0.21/0.46  fof(f281,plain,(
% 0.21/0.46    spl7_17 | ~spl7_4 | ~spl7_13),
% 0.21/0.46    inference(avatar_split_clause,[],[f274,f252,f106,f278])).
% 0.21/0.46  fof(f274,plain,(
% 0.21/0.46    sP1(k1_tex_2(sK4,sK5),sK4) | (~spl7_4 | ~spl7_13)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f108,f254,f72])).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    ( ! [X0,X1] : (sP1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f38])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (sP1(X1,X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(definition_folding,[],[f21,f37,f36])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(flattening,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).
% 0.21/0.46  fof(f272,plain,(
% 0.21/0.46    ~spl7_16 | spl7_9 | ~spl7_15),
% 0.21/0.46    inference(avatar_split_clause,[],[f267,f263,f213,f269])).
% 0.21/0.46  fof(f267,plain,(
% 0.21/0.46    ~v1_xboole_0(u1_struct_0(k1_tex_2(sK4,sK5))) | (spl7_9 | ~spl7_15)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f215,f265,f76])).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.46  fof(f266,plain,(
% 0.21/0.46    spl7_15 | ~spl7_14),
% 0.21/0.46    inference(avatar_split_clause,[],[f261,f257,f263])).
% 0.21/0.46  fof(f257,plain,(
% 0.21/0.46    spl7_14 <=> l1_pre_topc(k1_tex_2(sK4,sK5))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.46  fof(f261,plain,(
% 0.21/0.46    l1_struct_0(k1_tex_2(sK4,sK5)) | ~spl7_14),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f259,f63])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.46  fof(f259,plain,(
% 0.21/0.46    l1_pre_topc(k1_tex_2(sK4,sK5)) | ~spl7_14),
% 0.21/0.46    inference(avatar_component_clause,[],[f257])).
% 0.21/0.46  fof(f260,plain,(
% 0.21/0.46    spl7_14 | ~spl7_4 | ~spl7_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f247,f240,f106,f257])).
% 0.21/0.46  fof(f240,plain,(
% 0.21/0.46    spl7_12 <=> sP3(sK4,sK5)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.46  fof(f247,plain,(
% 0.21/0.46    l1_pre_topc(k1_tex_2(sK4,sK5)) | (~spl7_4 | ~spl7_12)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f108,f242,f128])).
% 0.21/0.46  fof(f128,plain,(
% 0.21/0.46    ( ! [X0,X1] : (l1_pre_topc(k1_tex_2(X0,X1)) | ~sP3(X0,X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.46    inference(resolution,[],[f86,f64])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~sP3(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f57])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~sP3(X0,X1))),
% 0.21/0.46    inference(nnf_transformation,[],[f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~sP3(X0,X1))),
% 0.21/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.46  fof(f242,plain,(
% 0.21/0.46    sP3(sK4,sK5) | ~spl7_12),
% 0.21/0.46    inference(avatar_component_clause,[],[f240])).
% 0.21/0.46  fof(f255,plain,(
% 0.21/0.46    spl7_13 | ~spl7_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f248,f240,f252])).
% 0.21/0.47  fof(f248,plain,(
% 0.21/0.47    m1_pre_topc(k1_tex_2(sK4,sK5),sK4) | ~spl7_12),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f242,f86])).
% 0.21/0.47  fof(f246,plain,(
% 0.21/0.47    spl7_12 | ~spl7_3 | ~spl7_4 | spl7_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f245,f111,f106,f101,f240])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    spl7_5 <=> v2_struct_0(sK4)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.47  fof(f245,plain,(
% 0.21/0.47    sP3(sK4,sK5) | (~spl7_3 | ~spl7_4 | spl7_5)),
% 0.21/0.47    inference(subsumption_resolution,[],[f244,f113])).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    ~v2_struct_0(sK4) | spl7_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f111])).
% 0.21/0.47  fof(f244,plain,(
% 0.21/0.47    sP3(sK4,sK5) | v2_struct_0(sK4) | (~spl7_3 | ~spl7_4)),
% 0.21/0.47    inference(subsumption_resolution,[],[f230,f108])).
% 0.21/0.47  fof(f230,plain,(
% 0.21/0.47    sP3(sK4,sK5) | ~l1_pre_topc(sK4) | v2_struct_0(sK4) | ~spl7_3),
% 0.21/0.47    inference(resolution,[],[f87,f103])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP3(X0,X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ! [X0,X1] : (sP3(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(definition_folding,[],[f35,f41])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.21/0.47  fof(f221,plain,(
% 0.21/0.47    spl7_10 | ~spl7_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f210,f202,f218])).
% 0.21/0.47  fof(f202,plain,(
% 0.21/0.47    spl7_8 <=> sP2(sK5,sK4)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.47  fof(f210,plain,(
% 0.21/0.47    v7_struct_0(k1_tex_2(sK4,sK5)) | ~spl7_8),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f204,f81])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X1,X0)) | ~sP2(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X1,X0)) & v7_struct_0(k1_tex_2(X1,X0)) & ~v2_struct_0(k1_tex_2(X1,X0))) | ~sP2(X0,X1))),
% 0.21/0.47    inference(rectify,[],[f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ! [X1,X0] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~sP2(X1,X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ! [X1,X0] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~sP2(X1,X0))),
% 0.21/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.47  fof(f204,plain,(
% 0.21/0.47    sP2(sK5,sK4) | ~spl7_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f202])).
% 0.21/0.47  fof(f216,plain,(
% 0.21/0.47    ~spl7_9 | ~spl7_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f211,f202,f213])).
% 0.21/0.47  fof(f211,plain,(
% 0.21/0.47    ~v2_struct_0(k1_tex_2(sK4,sK5)) | ~spl7_8),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f204,f80])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X1,X0)) | ~sP2(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f56])).
% 0.21/0.47  fof(f208,plain,(
% 0.21/0.47    spl7_8 | ~spl7_3 | ~spl7_4 | spl7_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f207,f111,f106,f101,f202])).
% 0.21/0.47  fof(f207,plain,(
% 0.21/0.47    sP2(sK5,sK4) | (~spl7_3 | ~spl7_4 | spl7_5)),
% 0.21/0.47    inference(subsumption_resolution,[],[f206,f113])).
% 0.21/0.47  fof(f206,plain,(
% 0.21/0.47    sP2(sK5,sK4) | v2_struct_0(sK4) | (~spl7_3 | ~spl7_4)),
% 0.21/0.47    inference(subsumption_resolution,[],[f192,f108])).
% 0.21/0.47  fof(f192,plain,(
% 0.21/0.47    sP2(sK5,sK4) | ~l1_pre_topc(sK4) | v2_struct_0(sK4) | ~spl7_3),
% 0.21/0.47    inference(resolution,[],[f83,f103])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP2(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ! [X0,X1] : (sP2(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(definition_folding,[],[f33,f39])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    ~spl7_7 | spl7_5 | ~spl7_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f122,f118,f111,f124])).
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    spl7_6 <=> l1_struct_0(sK4)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    ~v1_xboole_0(u1_struct_0(sK4)) | (spl7_5 | ~spl7_6)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f113,f120,f76])).
% 0.21/0.47  % (15992)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.47  % (15999)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.47  % (15982)Refutation not found, incomplete strategy% (15982)------------------------------
% 0.21/0.47  % (15982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (15982)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (15982)Memory used [KB]: 10618
% 0.21/0.47  % (15982)Time elapsed: 0.060 s
% 0.21/0.47  % (15982)------------------------------
% 0.21/0.47  % (15982)------------------------------
% 0.21/0.48  % (15983)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    l1_struct_0(sK4) | ~spl7_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f118])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    spl7_6 | ~spl7_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f116,f106,f118])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    l1_struct_0(sK4) | ~spl7_4),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f108,f63])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    ~spl7_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f58,f111])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ~v2_struct_0(sK4)),
% 0.21/0.48    inference(cnf_transformation,[],[f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) | ~v1_tex_2(k1_tex_2(sK4,sK5),sK4)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) | v1_tex_2(k1_tex_2(sK4,sK5),sK4)) & m1_subset_1(sK5,u1_struct_0(sK4))) & l1_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f44,f46,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK4),X1),u1_struct_0(sK4)) | ~v1_tex_2(k1_tex_2(sK4,X1),sK4)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK4),X1),u1_struct_0(sK4)) | v1_tex_2(k1_tex_2(sK4,X1),sK4)) & m1_subset_1(X1,u1_struct_0(sK4))) & l1_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK4),X1),u1_struct_0(sK4)) | ~v1_tex_2(k1_tex_2(sK4,X1),sK4)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK4),X1),u1_struct_0(sK4)) | v1_tex_2(k1_tex_2(sK4,X1),sK4)) & m1_subset_1(X1,u1_struct_0(sK4))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) | ~v1_tex_2(k1_tex_2(sK4,sK5),sK4)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) | v1_tex_2(k1_tex_2(sK4,sK5),sK4)) & m1_subset_1(sK5,u1_struct_0(sK4)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f13])).
% 0.21/0.48  fof(f13,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    spl7_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f59,f106])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    l1_pre_topc(sK4)),
% 0.21/0.48    inference(cnf_transformation,[],[f47])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    spl7_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f60,f101])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    m1_subset_1(sK5,u1_struct_0(sK4))),
% 0.21/0.48    inference(cnf_transformation,[],[f47])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    spl7_1 | spl7_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f61,f95,f91])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) | v1_tex_2(k1_tex_2(sK4,sK5),sK4)),
% 0.21/0.48    inference(cnf_transformation,[],[f47])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    ~spl7_1 | ~spl7_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f62,f95,f91])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ~v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) | ~v1_tex_2(k1_tex_2(sK4,sK5),sK4)),
% 0.21/0.48    inference(cnf_transformation,[],[f47])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (15997)------------------------------
% 0.21/0.48  % (15997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (15997)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (15997)Memory used [KB]: 11001
% 0.21/0.48  % (15997)Time elapsed: 0.076 s
% 0.21/0.48  % (15997)------------------------------
% 0.21/0.48  % (15997)------------------------------
% 0.21/0.48  % (15980)Success in time 0.12 s
%------------------------------------------------------------------------------
