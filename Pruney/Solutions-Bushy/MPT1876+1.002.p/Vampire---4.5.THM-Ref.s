%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1876+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:49 EST 2020

% Result     : Theorem 1.80s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :  213 ( 776 expanded)
%              Number of leaves         :   40 ( 227 expanded)
%              Depth                    :   18
%              Number of atoms          :  754 (5190 expanded)
%              Number of equality atoms :  105 ( 177 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3206,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f127,f128,f139,f187,f219,f224,f235,f239,f445,f450,f455,f463,f1756,f1803,f2977,f3205])).

fof(f3205,plain,
    ( spl7_1
    | ~ spl7_2
    | spl7_4
    | ~ spl7_7
    | ~ spl7_14
    | ~ spl7_15 ),
    inference(avatar_contradiction_clause,[],[f3204])).

fof(f3204,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | spl7_4
    | ~ spl7_7
    | ~ spl7_14
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f3145,f3081])).

fof(f3081,plain,
    ( m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f3080,f82])).

fof(f82,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,
    ( ( ~ v1_zfmisc_1(sK1)
      | ~ v2_tex_2(sK1,sK0) )
    & ( v1_zfmisc_1(sK1)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f58,f60,f59])).

fof(f59,plain,
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
            | ~ v2_tex_2(X1,sK0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ? [X1] :
        ( ( ~ v1_zfmisc_1(X1)
          | ~ v2_tex_2(X1,sK0) )
        & ( v1_zfmisc_1(X1)
          | v2_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & ~ v1_xboole_0(X1) )
   => ( ( ~ v1_zfmisc_1(sK1)
        | ~ v2_tex_2(sK1,sK0) )
      & ( v1_zfmisc_1(sK1)
        | v2_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
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
    inference(flattening,[],[f57])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
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
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

fof(f3080,plain,
    ( m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f704,f125])).

fof(f125,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl7_2
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f704,plain,
    ( m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK1)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f548,f86])).

fof(f86,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK2(X0)) = X0
            & m1_subset_1(sK2(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f63,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK2(X0)) = X0
        & m1_subset_1(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
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
    inference(rectify,[],[f62])).

fof(f62,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(f548,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f544,f82])).

fof(f544,plain,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(X0,sK1) ) ),
    inference(resolution,[],[f277,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f277,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,sK1)
      | m1_subset_1(X6,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f83,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f83,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f61])).

fof(f3145,plain,
    ( ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | spl7_1
    | spl7_4
    | ~ spl7_7
    | ~ spl7_14
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f3142,f122])).

fof(f122,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl7_1
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f3142,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | spl7_4
    | ~ spl7_7
    | ~ spl7_14
    | ~ spl7_15 ),
    inference(superposition,[],[f813,f391])).

fof(f391,plain,
    ( sK1 = k1_tarski(sK2(sK1))
    | ~ spl7_14
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f390,f82])).

fof(f390,plain,
    ( sK1 = k1_tarski(sK2(sK1))
    | v1_xboole_0(sK1)
    | ~ spl7_14
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f385,f218])).

fof(f218,plain,
    ( m1_subset_1(sK2(sK1),sK1)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl7_14
  <=> m1_subset_1(sK2(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f385,plain,
    ( sK1 = k1_tarski(sK2(sK1))
    | ~ m1_subset_1(sK2(sK1),sK1)
    | v1_xboole_0(sK1)
    | ~ spl7_15 ),
    inference(superposition,[],[f223,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f223,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl7_15
  <=> sK1 = k6_domain_1(sK1,sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f813,plain,
    ( ! [X0] :
        ( v2_tex_2(k1_tarski(X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl7_4
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f800,f138])).

fof(f138,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl7_4 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl7_4
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f800,plain,
    ( ! [X0] :
        ( v2_tex_2(k1_tarski(X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl7_7 ),
    inference(duplicate_literal_removal,[],[f799])).

fof(f799,plain,
    ( ! [X0] :
        ( v2_tex_2(k1_tarski(X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl7_7 ),
    inference(superposition,[],[f150,f100])).

fof(f150,plain,
    ( ! [X0] :
        ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl7_7
  <=> ! [X0] :
        ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f2977,plain,
    ( ~ spl7_36
    | ~ spl7_38
    | spl7_39
    | ~ spl7_67 ),
    inference(avatar_contradiction_clause,[],[f2976])).

fof(f2976,plain,
    ( $false
    | ~ spl7_36
    | ~ spl7_38
    | spl7_39
    | ~ spl7_67 ),
    inference(subsumption_resolution,[],[f2975,f636])).

fof(f636,plain,
    ( sK1 != k1_tarski(sK6(sK1))
    | spl7_39 ),
    inference(subsumption_resolution,[],[f635,f82])).

fof(f635,plain,
    ( sK1 != k1_tarski(sK6(sK1))
    | v1_xboole_0(sK1)
    | spl7_39 ),
    inference(subsumption_resolution,[],[f634,f344])).

fof(f344,plain,(
    m1_subset_1(sK6(sK1),sK1) ),
    inference(resolution,[],[f214,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f214,plain,(
    r2_hidden(sK6(sK1),sK1) ),
    inference(resolution,[],[f82,f111])).

fof(f111,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK6(X0),X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f75,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f634,plain,
    ( sK1 != k1_tarski(sK6(sK1))
    | ~ m1_subset_1(sK6(sK1),sK1)
    | v1_xboole_0(sK1)
    | spl7_39 ),
    inference(superposition,[],[f462,f100])).

fof(f462,plain,
    ( sK1 != k6_domain_1(sK1,sK6(sK1))
    | spl7_39 ),
    inference(avatar_component_clause,[],[f460])).

fof(f460,plain,
    ( spl7_39
  <=> sK1 = k6_domain_1(sK1,sK6(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f2975,plain,
    ( sK1 = k1_tarski(sK6(sK1))
    | ~ spl7_36
    | ~ spl7_38
    | ~ spl7_67 ),
    inference(forward_demodulation,[],[f2974,f353])).

fof(f353,plain,(
    sK1 = k3_xboole_0(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f273,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f273,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f83,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f2974,plain,
    ( k1_tarski(sK6(sK1)) = k3_xboole_0(sK1,u1_struct_0(sK0))
    | ~ spl7_36
    | ~ spl7_38
    | ~ spl7_67 ),
    inference(subsumption_resolution,[],[f2966,f2079])).

fof(f2079,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_38
    | ~ spl7_67 ),
    inference(backward_demodulation,[],[f1128,f1081])).

fof(f1081,plain,
    ( u1_struct_0(sK0) = sK3(sK0,sK1,sK6(sK1))
    | ~ spl7_67 ),
    inference(avatar_component_clause,[],[f1079])).

fof(f1079,plain,
    ( spl7_67
  <=> u1_struct_0(sK0) = sK3(sK0,sK1,sK6(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).

fof(f1128,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK6(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_38 ),
    inference(resolution,[],[f1105,f214])).

fof(f1105,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | m1_subset_1(sK3(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f454,f277])).

fof(f454,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f453])).

fof(f453,plain,
    ( spl7_38
  <=> ! [X0] :
        ( m1_subset_1(sK3(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f2966,plain,
    ( k1_tarski(sK6(sK1)) = k3_xboole_0(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_36
    | ~ spl7_67 ),
    inference(superposition,[],[f96,f2614])).

fof(f2614,plain,
    ( k1_tarski(sK6(sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))
    | ~ spl7_36
    | ~ spl7_67 ),
    inference(forward_demodulation,[],[f1306,f1081])).

fof(f1306,plain,
    ( k1_tarski(sK6(sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,sK3(sK0,sK1,sK6(sK1)))
    | ~ spl7_36 ),
    inference(resolution,[],[f1278,f214])).

fof(f1278,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | k1_tarski(X2) = k9_subset_1(u1_struct_0(sK0),sK1,sK3(sK0,sK1,X2)) )
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f444,f277])).

fof(f444,plain,
    ( ! [X2] :
        ( k1_tarski(X2) = k9_subset_1(u1_struct_0(sK0),sK1,sK3(sK0,sK1,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,sK1) )
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f443])).

fof(f443,plain,
    ( spl7_36
  <=> ! [X2] :
        ( k1_tarski(X2) = k9_subset_1(u1_struct_0(sK0),sK1,sK3(sK0,sK1,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f1803,plain,
    ( spl7_66
    | spl7_67
    | ~ spl7_37
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f1802,f453,f448,f1079,f1074])).

fof(f1074,plain,
    ( spl7_66
  <=> k1_xboole_0 = sK3(sK0,sK1,sK6(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f448,plain,
    ( spl7_37
  <=> ! [X1] :
        ( v3_pre_topc(sK3(sK0,sK1,X1),sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f1802,plain,
    ( u1_struct_0(sK0) = sK3(sK0,sK1,sK6(sK1))
    | k1_xboole_0 = sK3(sK0,sK1,sK6(sK1))
    | ~ spl7_37
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f1801,f79])).

fof(f79,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f1801,plain,
    ( u1_struct_0(sK0) = sK3(sK0,sK1,sK6(sK1))
    | k1_xboole_0 = sK3(sK0,sK1,sK6(sK1))
    | ~ v2_pre_topc(sK0)
    | ~ spl7_37
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f1800,f81])).

fof(f81,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f1800,plain,
    ( u1_struct_0(sK0) = sK3(sK0,sK1,sK6(sK1))
    | k1_xboole_0 = sK3(sK0,sK1,sK6(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_37
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f1799,f80])).

fof(f80,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f1799,plain,
    ( u1_struct_0(sK0) = sK3(sK0,sK1,sK6(sK1))
    | k1_xboole_0 = sK3(sK0,sK1,sK6(sK1))
    | ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_37
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f1784,f928])).

fof(f928,plain,
    ( v3_pre_topc(sK3(sK0,sK1,sK6(sK1)),sK0)
    | ~ spl7_37 ),
    inference(resolution,[],[f891,f214])).

fof(f891,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | v3_pre_topc(sK3(sK0,sK1,X1),sK0) )
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f449,f277])).

fof(f449,plain,
    ( ! [X1] :
        ( v3_pre_topc(sK3(sK0,sK1,X1),sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK1) )
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f448])).

fof(f1784,plain,
    ( u1_struct_0(sK0) = sK3(sK0,sK1,sK6(sK1))
    | k1_xboole_0 = sK3(sK0,sK1,sK6(sK1))
    | ~ v3_pre_topc(sK3(sK0,sK1,sK6(sK1)),sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_38 ),
    inference(resolution,[],[f1128,f104])).

fof(f104,plain,(
    ! [X2,X0] :
      ( u1_struct_0(X0) = X2
      | k1_xboole_0 = X2
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ( ( v2_tdlat_3(X0)
          | ( u1_struct_0(X0) != sK5(X0)
            & k1_xboole_0 != sK5(X0)
            & v3_pre_topc(sK5(X0),X0)
            & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( u1_struct_0(X0) = X2
              | k1_xboole_0 = X2
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f71,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ? [X1] :
          ( u1_struct_0(X0) != X1
          & k1_xboole_0 != X1
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( u1_struct_0(X0) != sK5(X0)
        & k1_xboole_0 != sK5(X0)
        & v3_pre_topc(sK5(X0),X0)
        & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0] :
      ( ( ( v2_tdlat_3(X0)
          | ? [X1] :
              ( u1_struct_0(X0) != X1
              & k1_xboole_0 != X1
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( u1_struct_0(X0) = X2
              | k1_xboole_0 = X2
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ( ( v2_tdlat_3(X0)
          | ? [X1] :
              ( u1_struct_0(X0) != X1
              & k1_xboole_0 != X1
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( u1_struct_0(X0) = X1
              | k1_xboole_0 = X1
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
      <=> ! [X1] :
            ( u1_struct_0(X0) = X1
            | k1_xboole_0 = X1
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
      <=> ! [X1] :
            ( u1_struct_0(X0) = X1
            | k1_xboole_0 = X1
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ~ ( u1_struct_0(X0) != X1
                & k1_xboole_0 != X1
                & v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tdlat_3)).

fof(f1756,plain,
    ( ~ spl7_1
    | ~ spl7_66 ),
    inference(avatar_contradiction_clause,[],[f1755])).

fof(f1755,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_66 ),
    inference(subsumption_resolution,[],[f1746,f113])).

fof(f113,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1746,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_66 ),
    inference(superposition,[],[f112,f1731])).

fof(f1731,plain,
    ( k1_xboole_0 = k1_tarski(sK6(sK1))
    | ~ spl7_1
    | ~ spl7_66 ),
    inference(forward_demodulation,[],[f1730,f1053])).

fof(f1053,plain,(
    ! [X5] : k1_xboole_0 = k9_subset_1(u1_struct_0(sK0),X5,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1025,f117])).

fof(f117,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f1025,plain,(
    ! [X5] : k9_subset_1(u1_struct_0(sK0),X5,k1_xboole_0) = k3_xboole_0(X5,k1_xboole_0) ),
    inference(resolution,[],[f1007,f96])).

fof(f1007,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f754,f117])).

fof(f754,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f707,f116])).

fof(f116,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f707,plain,(
    ! [X4] : m1_subset_1(k3_xboole_0(X4,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f275,f276])).

fof(f276,plain,(
    ! [X5] : k9_subset_1(u1_struct_0(sK0),X5,sK1) = k3_xboole_0(X5,sK1) ),
    inference(resolution,[],[f83,f96])).

fof(f275,plain,(
    ! [X4] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X4,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f83,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f1730,plain,
    ( k1_tarski(sK6(sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_66 ),
    inference(subsumption_resolution,[],[f1729,f81])).

fof(f1729,plain,
    ( k1_tarski(sK6(sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_1
    | ~ spl7_66 ),
    inference(subsumption_resolution,[],[f1728,f83])).

fof(f1728,plain,
    ( k1_tarski(sK6(sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_1
    | ~ spl7_66 ),
    inference(subsumption_resolution,[],[f1727,f121])).

fof(f121,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f1727,plain,
    ( k1_tarski(sK6(sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_66 ),
    inference(subsumption_resolution,[],[f1726,f546])).

fof(f546,plain,(
    m1_subset_1(sK6(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f277,f214])).

fof(f1726,plain,
    ( k1_tarski(sK6(sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)
    | ~ m1_subset_1(sK6(sK1),u1_struct_0(sK0))
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_66 ),
    inference(subsumption_resolution,[],[f1717,f214])).

fof(f1717,plain,
    ( k1_tarski(sK6(sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)
    | ~ r2_hidden(sK6(sK1),sK1)
    | ~ m1_subset_1(sK6(sK1),u1_struct_0(sK0))
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_66 ),
    inference(superposition,[],[f93,f1076])).

fof(f1076,plain,
    ( k1_xboole_0 = sK3(sK0,sK1,sK6(sK1))
    | ~ spl7_66 ),
    inference(avatar_component_clause,[],[f1074])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X2))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X2))
                & v3_pre_topc(sK3(X0,X1,X2),X0)
                & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f66])).

fof(f66,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X2))
        & v3_pre_topc(sK3(X0,X1,X2),X0)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                            & v3_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tex_2)).

fof(f112,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f463,plain,
    ( ~ spl7_39
    | spl7_2 ),
    inference(avatar_split_clause,[],[f458,f124,f460])).

fof(f458,plain,
    ( v1_zfmisc_1(sK1)
    | sK1 != k6_domain_1(sK1,sK6(sK1)) ),
    inference(subsumption_resolution,[],[f375,f82])).

fof(f375,plain,
    ( v1_zfmisc_1(sK1)
    | sK1 != k6_domain_1(sK1,sK6(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f344,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X0)
      | k6_domain_1(X0,X1) != X0
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f455,plain,
    ( ~ spl7_1
    | spl7_38 ),
    inference(avatar_split_clause,[],[f451,f453,f120])).

fof(f451,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v2_tex_2(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f270,f81])).

fof(f270,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v2_tex_2(sK1,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f83,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f450,plain,
    ( ~ spl7_1
    | spl7_37 ),
    inference(avatar_split_clause,[],[f446,f448,f120])).

fof(f446,plain,(
    ! [X1] :
      ( v3_pre_topc(sK3(sK0,sK1,X1),sK0)
      | ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v2_tex_2(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f271,f81])).

fof(f271,plain,(
    ! [X1] :
      ( v3_pre_topc(sK3(sK0,sK1,X1),sK0)
      | ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v2_tex_2(sK1,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f83,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f445,plain,
    ( ~ spl7_1
    | spl7_36 ),
    inference(avatar_split_clause,[],[f441,f443,f120])).

fof(f441,plain,(
    ! [X2] :
      ( k1_tarski(X2) = k9_subset_1(u1_struct_0(sK0),sK1,sK3(sK0,sK1,X2))
      | ~ r2_hidden(X2,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v2_tex_2(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f272,f81])).

fof(f272,plain,(
    ! [X2] :
      ( k1_tarski(X2) = k9_subset_1(u1_struct_0(sK0),sK1,sK3(sK0,sK1,X2))
      | ~ r2_hidden(X2,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v2_tex_2(sK1,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f83,f93])).

fof(f239,plain,(
    spl7_6 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | spl7_6 ),
    inference(subsumption_resolution,[],[f147,f81])).

fof(f147,plain,
    ( ~ l1_pre_topc(sK0)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl7_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f235,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | spl7_3 ),
    inference(subsumption_resolution,[],[f233,f81])).

fof(f233,plain,
    ( ~ l1_pre_topc(sK0)
    | spl7_3 ),
    inference(resolution,[],[f134,f114])).

fof(f114,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f134,plain,
    ( ~ l1_struct_0(sK0)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl7_3
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f224,plain,
    ( ~ spl7_2
    | spl7_15 ),
    inference(avatar_split_clause,[],[f209,f221,f124])).

fof(f209,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | ~ v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f82,f87])).

fof(f87,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK2(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f219,plain,
    ( ~ spl7_2
    | spl7_14 ),
    inference(avatar_split_clause,[],[f208,f216,f124])).

fof(f208,plain,
    ( m1_subset_1(sK2(sK1),sK1)
    | ~ v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f82,f86])).

fof(f187,plain,
    ( ~ spl7_6
    | spl7_7 ),
    inference(avatar_split_clause,[],[f186,f149,f145])).

fof(f186,plain,(
    ! [X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f157,f78])).

fof(f78,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f157,plain,(
    ! [X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f79,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(f139,plain,
    ( ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f129,f136,f132])).

fof(f129,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f78,f109])).

fof(f109,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f128,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f84,f124,f120])).

fof(f84,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f127,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f85,f124,f120])).

fof(f85,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f61])).

%------------------------------------------------------------------------------
