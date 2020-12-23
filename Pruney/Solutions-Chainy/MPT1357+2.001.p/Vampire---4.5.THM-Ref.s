%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 608 expanded)
%              Number of leaves         :   26 ( 207 expanded)
%              Depth                    :   24
%              Number of atoms          :  586 (2943 expanded)
%              Number of equality atoms :   56 ( 462 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f483,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f271,f274,f278,f429,f438,f467,f475,f479,f482])).

fof(f482,plain,
    ( ~ spl8_2
    | ~ spl8_5
    | ~ spl8_13 ),
    inference(avatar_contradiction_clause,[],[f481])).

fof(f481,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_5
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f480,f104])).

fof(f104,plain,
    ( sP1(sK6,sK5)
    | ~ spl8_2 ),
    inference(resolution,[],[f52,f95])).

fof(f95,plain,
    ( sP2(sK5,sK6)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl8_2
  <=> sP2(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | sP1(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP1(X1,X0)
        & k1_xboole_0 != X1
        & v2_pre_topc(X0) )
      | ~ sP2(X0,X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( sP1(X1,X0)
        & k1_xboole_0 != X1
        & v2_pre_topc(X0) )
      | ~ sP2(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f480,plain,
    ( ~ sP1(sK6,sK5)
    | ~ spl8_5
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f477,f134])).

fof(f134,plain,
    ( v2_compts_1(sK6,sK5)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl8_5
  <=> v2_compts_1(sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f477,plain,
    ( ~ v2_compts_1(sK6,sK5)
    | ~ sP1(sK6,sK5)
    | ~ spl8_13 ),
    inference(resolution,[],[f339,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_compts_1(k1_pre_topc(X1,X0))
      | ~ v2_compts_1(X0,X1)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

% (12887)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( ~ v1_compts_1(k1_pre_topc(X1,X0))
          | ~ v2_compts_1(X0,X1) )
        & ( v1_compts_1(k1_pre_topc(X1,X0))
          | v2_compts_1(X0,X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ( ( ~ v1_compts_1(k1_pre_topc(X0,X1))
          | ~ v2_compts_1(X1,X0) )
        & ( v1_compts_1(k1_pre_topc(X0,X1))
          | v2_compts_1(X1,X0) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ( v2_compts_1(X1,X0)
      <~> v1_compts_1(k1_pre_topc(X0,X1)) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f339,plain,
    ( v1_compts_1(k1_pre_topc(sK5,sK6))
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f337])).

fof(f337,plain,
    ( spl8_13
  <=> v1_compts_1(k1_pre_topc(sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f479,plain,
    ( ~ spl8_1
    | ~ spl8_5
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f478,f337,f132,f89])).

fof(f89,plain,
    ( spl8_1
  <=> sP0(sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f478,plain,
    ( ~ sP0(sK6,sK5)
    | ~ spl8_5
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f476,f134])).

fof(f476,plain,
    ( ~ v2_compts_1(sK6,sK5)
    | ~ sP0(sK6,sK5)
    | ~ spl8_13 ),
    inference(resolution,[],[f339,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_compts_1(k1_pre_topc(X1,X0))
      | ~ v2_compts_1(X0,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( ~ v1_compts_1(k1_pre_topc(X1,X0))
          | ~ v2_compts_1(X0,X1) )
        & ( v1_compts_1(k1_pre_topc(X1,X0))
          | v2_compts_1(X0,X1) ) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ( ( ~ v1_compts_1(k1_pre_topc(X0,X1))
          | ~ v2_compts_1(X1,X0) )
        & ( v1_compts_1(k1_pre_topc(X0,X1))
          | v2_compts_1(X1,X0) ) )
      | ~ sP0(X1,X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ( v2_compts_1(X1,X0)
      <~> v1_compts_1(k1_pre_topc(X0,X1)) )
      | ~ sP0(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f475,plain,
    ( spl8_13
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f474,f394,f337])).

fof(f394,plain,
    ( spl8_19
  <=> v2_compts_1(sK6,k1_pre_topc(sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f474,plain,
    ( v1_compts_1(k1_pre_topc(sK5,sK6))
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f473,f57])).

fof(f57,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( sP2(sK5,sK6)
      | ( sP0(sK6,sK5)
        & k1_xboole_0 = sK6 ) )
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    & l1_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f28,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( sP2(X0,X1)
              | ( sP0(X1,X0)
                & k1_xboole_0 = X1 ) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( sP2(sK5,X1)
            | ( sP0(X1,sK5)
              & k1_xboole_0 = X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) )
      & l1_pre_topc(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ( sP2(sK5,X1)
          | ( sP0(X1,sK5)
            & k1_xboole_0 = X1 ) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) )
   => ( ( sP2(sK5,sK6)
        | ( sP0(sK6,sK5)
          & k1_xboole_0 = sK6 ) )
      & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( sP2(X0,X1)
            | ( sP0(X1,X0)
              & k1_xboole_0 = X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f14,f27,f26,f25])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ( v2_compts_1(X1,X0)
              <~> v1_compts_1(k1_pre_topc(X0,X1)) )
              & k1_xboole_0 != X1
              & v2_pre_topc(X0) )
            | ( ( v2_compts_1(X1,X0)
              <~> v1_compts_1(k1_pre_topc(X0,X1)) )
              & k1_xboole_0 = X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ( v2_compts_1(X1,X0)
              <~> v1_compts_1(k1_pre_topc(X0,X1)) )
              & k1_xboole_0 != X1
              & v2_pre_topc(X0) )
            | ( ( v2_compts_1(X1,X0)
              <~> v1_compts_1(k1_pre_topc(X0,X1)) )
              & k1_xboole_0 = X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v2_pre_topc(X0)
               => ( ( v2_compts_1(X1,X0)
                  <=> v1_compts_1(k1_pre_topc(X0,X1)) )
                  | k1_xboole_0 = X1 ) )
              & ( k1_xboole_0 = X1
               => ( v2_compts_1(X1,X0)
                <=> v1_compts_1(k1_pre_topc(X0,X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_pre_topc(X0)
             => ( ( v2_compts_1(X1,X0)
                <=> v1_compts_1(k1_pre_topc(X0,X1)) )
                | k1_xboole_0 = X1 ) )
            & ( k1_xboole_0 = X1
             => ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_compts_1)).

fof(f473,plain,
    ( v1_compts_1(k1_pre_topc(sK5,sK6))
    | ~ l1_pre_topc(sK5)
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f468,f58])).

fof(f58,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f39])).

fof(f468,plain,
    ( v1_compts_1(k1_pre_topc(sK5,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5)
    | ~ spl8_19 ),
    inference(resolution,[],[f396,f229])).

fof(f229,plain,(
    ! [X6,X5] :
      ( ~ v2_compts_1(X6,k1_pre_topc(X5,X6))
      | v1_compts_1(k1_pre_topc(X5,X6))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
      | ~ l1_pre_topc(X5) ) ),
    inference(subsumption_resolution,[],[f226,f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | l1_pre_topc(k1_pre_topc(X1,X0)) ) ),
    inference(duplicate_literal_removal,[],[f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | l1_pre_topc(k1_pre_topc(X1,X0))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f78,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f226,plain,(
    ! [X6,X5] :
      ( ~ v2_compts_1(X6,k1_pre_topc(X5,X6))
      | v1_compts_1(k1_pre_topc(X5,X6))
      | ~ l1_pre_topc(k1_pre_topc(X5,X6))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
      | ~ l1_pre_topc(X5) ) ),
    inference(superposition,[],[f64,f222])).

fof(f222,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f221,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f221,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f85,f78])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

fof(f64,plain,(
    ! [X0] :
      ( ~ v2_compts_1(k2_struct_0(X0),X0)
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ~ v2_compts_1(k2_struct_0(X0),X0) )
        & ( v2_compts_1(k2_struct_0(X0),X0)
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_compts_1)).

fof(f396,plain,
    ( v2_compts_1(sK6,k1_pre_topc(sK5,sK6))
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f394])).

fof(f467,plain,
    ( spl8_19
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f466,f390,f394])).

fof(f390,plain,
    ( spl8_18
  <=> sP3(k1_pre_topc(sK5,sK6),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f466,plain,
    ( v2_compts_1(sK6,k1_pre_topc(sK5,sK6))
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f465,f57])).

fof(f465,plain,
    ( v2_compts_1(sK6,k1_pre_topc(sK5,sK6))
    | ~ l1_pre_topc(sK5)
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f464,f58])).

fof(f464,plain,
    ( v2_compts_1(sK6,k1_pre_topc(sK5,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5)
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f460,f103])).

fof(f103,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f62,f61])).

fof(f61,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f460,plain,
    ( v2_compts_1(sK6,k1_pre_topc(sK5,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5)
    | ~ spl8_18 ),
    inference(resolution,[],[f154,f391])).

fof(f391,plain,
    ( sP3(k1_pre_topc(sK5,sK6),sK6)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f390])).

fof(f154,plain,(
    ! [X6,X8,X7] :
      ( ~ sP3(k1_pre_topc(X6,X7),X8)
      | v2_compts_1(X8,k1_pre_topc(X6,X7))
      | ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
      | ~ l1_pre_topc(X6) ) ),
    inference(superposition,[],[f83,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f83,plain,(
    ! [X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_compts_1(X3,X0)
      | ~ sP3(X0,X3) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( v2_compts_1(X3,X0)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ( ~ v2_compts_1(sK7(X0,X1),X0)
          & sK7(X0,X1) = X1
          & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( v2_compts_1(X3,X0)
            | X1 != X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP3(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v2_compts_1(X2,X0)
          & X1 = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_compts_1(sK7(X0,X1),X0)
        & sK7(X0,X1) = X1
        & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ? [X2] :
            ( ~ v2_compts_1(X2,X0)
            & X1 = X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( v2_compts_1(X3,X0)
            | X1 != X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP3(X0,X1) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X1,X2] :
      ( ( sP3(X1,X2)
        | ? [X3] :
            ( ~ v2_compts_1(X3,X1)
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X3] :
            ( v2_compts_1(X3,X1)
            | X2 != X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP3(X1,X2) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X1,X2] :
      ( sP3(X1,X2)
    <=> ! [X3] :
          ( v2_compts_1(X3,X1)
          | X2 != X3
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f438,plain,
    ( ~ spl8_6
    | spl8_18
    | ~ spl8_21 ),
    inference(avatar_contradiction_clause,[],[f437])).

fof(f437,plain,
    ( $false
    | ~ spl8_6
    | spl8_18
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f404,f418])).

fof(f418,plain,
    ( m1_pre_topc(k1_pre_topc(sK5,sK6),sK5)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f417])).

fof(f417,plain,
    ( spl8_21
  <=> m1_pre_topc(k1_pre_topc(sK5,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f404,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK5,sK6),sK5)
    | ~ spl8_6
    | spl8_18 ),
    inference(subsumption_resolution,[],[f403,f57])).

fof(f403,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK5,sK6),sK5)
    | ~ l1_pre_topc(sK5)
    | ~ spl8_6
    | spl8_18 ),
    inference(subsumption_resolution,[],[f402,f58])).

% (12892)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
fof(f402,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK5,sK6),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5)
    | ~ spl8_6
    | spl8_18 ),
    inference(subsumption_resolution,[],[f399,f86])).

fof(f86,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f399,plain,
    ( ~ r1_tarski(sK6,sK6)
    | ~ m1_pre_topc(k1_pre_topc(sK5,sK6),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5)
    | ~ spl8_6
    | spl8_18 ),
    inference(resolution,[],[f392,f314])).

fof(f314,plain,
    ( ! [X0,X1] :
        ( sP3(k1_pre_topc(X0,X1),sK6)
        | ~ r1_tarski(sK6,X1)
        | ~ m1_pre_topc(k1_pre_topc(X0,X1),sK5)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl8_6 ),
    inference(superposition,[],[f277,f222])).

fof(f277,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK6,k2_struct_0(X1))
        | sP3(X1,sK6)
        | ~ m1_pre_topc(X1,sK5) )
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl8_6
  <=> ! [X1] :
        ( ~ r1_tarski(sK6,k2_struct_0(X1))
        | sP3(X1,sK6)
        | ~ m1_pre_topc(X1,sK5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f392,plain,
    ( ~ sP3(k1_pre_topc(sK5,sK6),sK6)
    | spl8_18 ),
    inference(avatar_component_clause,[],[f390])).

fof(f429,plain,(
    spl8_21 ),
    inference(avatar_contradiction_clause,[],[f428])).

fof(f428,plain,
    ( $false
    | spl8_21 ),
    inference(subsumption_resolution,[],[f427,f57])).

fof(f427,plain,
    ( ~ l1_pre_topc(sK5)
    | spl8_21 ),
    inference(subsumption_resolution,[],[f426,f58])).

fof(f426,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5)
    | spl8_21 ),
    inference(resolution,[],[f419,f78])).

fof(f419,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK5,sK6),sK5)
    | spl8_21 ),
    inference(avatar_component_clause,[],[f417])).

fof(f278,plain,
    ( ~ spl8_5
    | spl8_6 ),
    inference(avatar_split_clause,[],[f190,f276,f132])).

fof(f190,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK6,k2_struct_0(X1))
      | ~ m1_pre_topc(X1,sK5)
      | ~ v2_compts_1(sK6,sK5)
      | sP3(X1,sK6) ) ),
    inference(resolution,[],[f187,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | ~ v2_compts_1(X0,X2)
      | sP3(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( v2_compts_1(X0,X2)
          | ~ sP3(X1,X0) )
        & ( sP3(X1,X0)
          | ~ v2_compts_1(X0,X2) ) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ( ( v2_compts_1(X2,X0)
          | ~ sP3(X1,X2) )
        & ( sP3(X1,X2)
          | ~ v2_compts_1(X2,X0) ) )
      | ~ sP4(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ( v2_compts_1(X2,X0)
      <=> sP3(X1,X2) )
      | ~ sP4(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f187,plain,(
    ! [X0] :
      ( sP4(sK6,X0,sK5)
      | ~ r1_tarski(sK6,k2_struct_0(X0))
      | ~ m1_pre_topc(X0,sK5) ) ),
    inference(subsumption_resolution,[],[f180,f57])).

fof(f180,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK6,k2_struct_0(X0))
      | sP4(sK6,X0,sK5)
      | ~ m1_pre_topc(X0,sK5)
      | ~ l1_pre_topc(sK5) ) ),
    inference(resolution,[],[f73,f58])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | sP4(X2,X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP4(X2,X1,X0)
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f19,f30,f29])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X2,k2_struct_0(X1))
               => ( v2_compts_1(X2,X0)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( X2 = X3
                       => v2_compts_1(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_compts_1)).

fof(f274,plain,
    ( ~ spl8_2
    | spl8_5 ),
    inference(avatar_contradiction_clause,[],[f273])).

fof(f273,plain,
    ( $false
    | ~ spl8_2
    | spl8_5 ),
    inference(subsumption_resolution,[],[f272,f104])).

fof(f272,plain,
    ( ~ sP1(sK6,sK5)
    | spl8_5 ),
    inference(subsumption_resolution,[],[f269,f133])).

fof(f133,plain,
    ( ~ v2_compts_1(sK6,sK5)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f132])).

fof(f269,plain,
    ( v2_compts_1(sK6,sK5)
    | ~ sP1(sK6,sK5)
    | spl8_5 ),
    inference(resolution,[],[f267,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_compts_1(k1_pre_topc(X1,X0))
      | v2_compts_1(X0,X1)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f267,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK5,sK6))
    | spl8_5 ),
    inference(subsumption_resolution,[],[f266,f57])).

fof(f266,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v1_compts_1(k1_pre_topc(sK5,sK6))
    | spl8_5 ),
    inference(subsumption_resolution,[],[f265,f58])).

fof(f265,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5)
    | ~ v1_compts_1(k1_pre_topc(sK5,sK6))
    | spl8_5 ),
    inference(duplicate_literal_removal,[],[f264])).

fof(f264,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5)
    | ~ v1_compts_1(k1_pre_topc(sK5,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5)
    | spl8_5 ),
    inference(resolution,[],[f263,f78])).

fof(f263,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(X0,sK6),sK5)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v1_compts_1(k1_pre_topc(X0,sK6)) )
    | spl8_5 ),
    inference(subsumption_resolution,[],[f262,f86])).

fof(f262,plain,
    ( ! [X0] :
        ( ~ v1_compts_1(k1_pre_topc(X0,sK6))
        | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ r1_tarski(sK6,sK6)
        | ~ m1_pre_topc(k1_pre_topc(X0,sK6),sK5) )
    | spl8_5 ),
    inference(duplicate_literal_removal,[],[f259])).

fof(f259,plain,
    ( ! [X0] :
        ( ~ v1_compts_1(k1_pre_topc(X0,sK6))
        | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ r1_tarski(sK6,sK6)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k1_pre_topc(X0,sK6),sK5) )
    | spl8_5 ),
    inference(resolution,[],[f230,f231])).

fof(f231,plain,
    ( ! [X0,X1] :
        ( ~ v2_compts_1(sK6,k1_pre_topc(X0,X1))
        | ~ r1_tarski(sK6,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k1_pre_topc(X0,X1),sK5) )
    | spl8_5 ),
    inference(resolution,[],[f225,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | ~ v2_compts_1(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ v2_compts_1(X1,X0)
      | sP3(X0,X1)
      | sP3(X0,X1) ) ),
    inference(superposition,[],[f72,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( sK7(X0,X1) = X1
      | sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v2_compts_1(sK7(X0,X1),X0)
      | sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f225,plain,
    ( ! [X4,X3] :
        ( ~ sP3(k1_pre_topc(X3,X4),sK6)
        | ~ m1_pre_topc(k1_pre_topc(X3,X4),sK5)
        | ~ r1_tarski(sK6,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ l1_pre_topc(X3) )
    | spl8_5 ),
    inference(superposition,[],[f191,f222])).

fof(f191,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK6,k2_struct_0(X0))
        | ~ m1_pre_topc(X0,sK5)
        | ~ sP3(X0,sK6) )
    | spl8_5 ),
    inference(subsumption_resolution,[],[f189,f133])).

fof(f189,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK6,k2_struct_0(X0))
      | ~ m1_pre_topc(X0,sK5)
      | ~ sP3(X0,sK6)
      | v2_compts_1(sK6,sK5) ) ),
    inference(resolution,[],[f187,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | ~ sP3(X1,X0)
      | v2_compts_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f230,plain,(
    ! [X8,X7] :
      ( v2_compts_1(X8,k1_pre_topc(X7,X8))
      | ~ v1_compts_1(k1_pre_topc(X7,X8))
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
      | ~ l1_pre_topc(X7) ) ),
    inference(subsumption_resolution,[],[f227,f144])).

fof(f227,plain,(
    ! [X8,X7] :
      ( v2_compts_1(X8,k1_pre_topc(X7,X8))
      | ~ v1_compts_1(k1_pre_topc(X7,X8))
      | ~ l1_pre_topc(k1_pre_topc(X7,X8))
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
      | ~ l1_pre_topc(X7) ) ),
    inference(superposition,[],[f63,f222])).

fof(f63,plain,(
    ! [X0] :
      ( v2_compts_1(k2_struct_0(X0),X0)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f271,plain,
    ( ~ spl8_1
    | spl8_5 ),
    inference(avatar_split_clause,[],[f270,f132,f89])).

fof(f270,plain,
    ( ~ sP0(sK6,sK5)
    | spl8_5 ),
    inference(subsumption_resolution,[],[f268,f133])).

fof(f268,plain,
    ( v2_compts_1(sK6,sK5)
    | ~ sP0(sK6,sK5)
    | spl8_5 ),
    inference(resolution,[],[f267,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_compts_1(k1_pre_topc(X1,X0))
      | v2_compts_1(X0,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f96,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f60,f93,f89])).

fof(f60,plain,
    ( sP2(sK5,sK6)
    | sP0(sK6,sK5) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:13:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (12872)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (12871)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (12873)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (12874)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (12873)Refutation not found, incomplete strategy% (12873)------------------------------
% 0.21/0.50  % (12873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (12873)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (12873)Memory used [KB]: 6140
% 0.21/0.50  % (12873)Time elapsed: 0.096 s
% 0.21/0.50  % (12873)------------------------------
% 0.21/0.50  % (12873)------------------------------
% 0.21/0.50  % (12877)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.50  % (12891)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.50  % (12874)Refutation not found, incomplete strategy% (12874)------------------------------
% 0.21/0.50  % (12874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (12874)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (12874)Memory used [KB]: 10618
% 0.21/0.50  % (12874)Time elapsed: 0.093 s
% 0.21/0.50  % (12874)------------------------------
% 0.21/0.50  % (12874)------------------------------
% 0.21/0.51  % (12889)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (12880)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (12881)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (12888)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (12890)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (12883)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (12881)Refutation not found, incomplete strategy% (12881)------------------------------
% 0.21/0.51  % (12881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12881)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (12881)Memory used [KB]: 6140
% 0.21/0.51  % (12881)Time elapsed: 0.109 s
% 0.21/0.51  % (12881)------------------------------
% 0.21/0.51  % (12881)------------------------------
% 0.21/0.51  % (12878)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (12872)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (12879)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (12869)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (12879)Refutation not found, incomplete strategy% (12879)------------------------------
% 0.21/0.52  % (12879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12879)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (12879)Memory used [KB]: 10618
% 0.21/0.52  % (12879)Time elapsed: 0.112 s
% 0.21/0.52  % (12879)------------------------------
% 0.21/0.52  % (12879)------------------------------
% 0.21/0.52  % (12870)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (12875)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (12893)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (12886)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f483,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f96,f271,f274,f278,f429,f438,f467,f475,f479,f482])).
% 0.21/0.53  fof(f482,plain,(
% 0.21/0.53    ~spl8_2 | ~spl8_5 | ~spl8_13),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f481])).
% 0.21/0.53  fof(f481,plain,(
% 0.21/0.53    $false | (~spl8_2 | ~spl8_5 | ~spl8_13)),
% 0.21/0.53    inference(subsumption_resolution,[],[f480,f104])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    sP1(sK6,sK5) | ~spl8_2),
% 0.21/0.53    inference(resolution,[],[f52,f95])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    sP2(sK5,sK6) | ~spl8_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f93])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    spl8_2 <=> sP2(sK5,sK6)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~sP2(X0,X1) | sP1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1] : ((sP1(X1,X0) & k1_xboole_0 != X1 & v2_pre_topc(X0)) | ~sP2(X0,X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1] : ((sP1(X1,X0) & k1_xboole_0 != X1 & v2_pre_topc(X0)) | ~sP2(X0,X1))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.53  fof(f480,plain,(
% 0.21/0.53    ~sP1(sK6,sK5) | (~spl8_5 | ~spl8_13)),
% 0.21/0.53    inference(subsumption_resolution,[],[f477,f134])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    v2_compts_1(sK6,sK5) | ~spl8_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f132])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    spl8_5 <=> v2_compts_1(sK6,sK5)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.53  fof(f477,plain,(
% 0.21/0.53    ~v2_compts_1(sK6,sK5) | ~sP1(sK6,sK5) | ~spl8_13),
% 0.21/0.53    inference(resolution,[],[f339,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_compts_1(k1_pre_topc(X1,X0)) | ~v2_compts_1(X0,X1) | ~sP1(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  % (12887)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1] : (((~v1_compts_1(k1_pre_topc(X1,X0)) | ~v2_compts_1(X0,X1)) & (v1_compts_1(k1_pre_topc(X1,X0)) | v2_compts_1(X0,X1))) | ~sP1(X0,X1))),
% 0.21/0.53    inference(rectify,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X1,X0] : (((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0))) | ~sP1(X1,X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X1,X0] : ((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) | ~sP1(X1,X0))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.53  fof(f339,plain,(
% 0.21/0.53    v1_compts_1(k1_pre_topc(sK5,sK6)) | ~spl8_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f337])).
% 0.21/0.53  fof(f337,plain,(
% 0.21/0.53    spl8_13 <=> v1_compts_1(k1_pre_topc(sK5,sK6))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.53  fof(f479,plain,(
% 0.21/0.53    ~spl8_1 | ~spl8_5 | ~spl8_13),
% 0.21/0.53    inference(avatar_split_clause,[],[f478,f337,f132,f89])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    spl8_1 <=> sP0(sK6,sK5)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.53  fof(f478,plain,(
% 0.21/0.53    ~sP0(sK6,sK5) | (~spl8_5 | ~spl8_13)),
% 0.21/0.53    inference(subsumption_resolution,[],[f476,f134])).
% 0.21/0.53  fof(f476,plain,(
% 0.21/0.53    ~v2_compts_1(sK6,sK5) | ~sP0(sK6,sK5) | ~spl8_13),
% 0.21/0.53    inference(resolution,[],[f339,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_compts_1(k1_pre_topc(X1,X0)) | ~v2_compts_1(X0,X1) | ~sP0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0,X1] : (((~v1_compts_1(k1_pre_topc(X1,X0)) | ~v2_compts_1(X0,X1)) & (v1_compts_1(k1_pre_topc(X1,X0)) | v2_compts_1(X0,X1))) | ~sP0(X0,X1))),
% 0.21/0.53    inference(rectify,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X1,X0] : (((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0))) | ~sP0(X1,X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X1,X0] : ((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) | ~sP0(X1,X0))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.53  fof(f475,plain,(
% 0.21/0.53    spl8_13 | ~spl8_19),
% 0.21/0.53    inference(avatar_split_clause,[],[f474,f394,f337])).
% 0.21/0.53  fof(f394,plain,(
% 0.21/0.53    spl8_19 <=> v2_compts_1(sK6,k1_pre_topc(sK5,sK6))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.21/0.53  fof(f474,plain,(
% 0.21/0.53    v1_compts_1(k1_pre_topc(sK5,sK6)) | ~spl8_19),
% 0.21/0.53    inference(subsumption_resolution,[],[f473,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    l1_pre_topc(sK5)),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ((sP2(sK5,sK6) | (sP0(sK6,sK5) & k1_xboole_0 = sK6)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))) & l1_pre_topc(sK5)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f28,f38,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((sP2(X0,X1) | (sP0(X1,X0) & k1_xboole_0 = X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((sP2(sK5,X1) | (sP0(X1,sK5) & k1_xboole_0 = X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))) & l1_pre_topc(sK5))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ? [X1] : ((sP2(sK5,X1) | (sP0(X1,sK5) & k1_xboole_0 = X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))) => ((sP2(sK5,sK6) | (sP0(sK6,sK5) & k1_xboole_0 = sK6)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((sP2(X0,X1) | (sP0(X1,X0) & k1_xboole_0 = X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.53    inference(definition_folding,[],[f14,f27,f26,f25])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) & k1_xboole_0 != X1 & v2_pre_topc(X0)) | ((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) & k1_xboole_0 = X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (((((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) & k1_xboole_0 != X1) & v2_pre_topc(X0)) | ((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) & k1_xboole_0 = X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,negated_conjecture,(
% 0.21/0.53    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_pre_topc(X0) => ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1)) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f11])).
% 0.21/0.53  fof(f11,conjecture,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_pre_topc(X0) => ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1)) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_compts_1)).
% 0.21/0.53  fof(f473,plain,(
% 0.21/0.53    v1_compts_1(k1_pre_topc(sK5,sK6)) | ~l1_pre_topc(sK5) | ~spl8_19),
% 0.21/0.53    inference(subsumption_resolution,[],[f468,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f468,plain,(
% 0.21/0.53    v1_compts_1(k1_pre_topc(sK5,sK6)) | ~m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) | ~l1_pre_topc(sK5) | ~spl8_19),
% 0.21/0.53    inference(resolution,[],[f396,f229])).
% 0.21/0.53  fof(f229,plain,(
% 0.21/0.53    ( ! [X6,X5] : (~v2_compts_1(X6,k1_pre_topc(X5,X6)) | v1_compts_1(k1_pre_topc(X5,X6)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5))) | ~l1_pre_topc(X5)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f226,f144])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | l1_pre_topc(k1_pre_topc(X1,X0))) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f143])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | l1_pre_topc(k1_pre_topc(X1,X0)) | ~l1_pre_topc(X1)) )),
% 0.21/0.53    inference(resolution,[],[f78,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.21/0.53  fof(f226,plain,(
% 0.21/0.53    ( ! [X6,X5] : (~v2_compts_1(X6,k1_pre_topc(X5,X6)) | v1_compts_1(k1_pre_topc(X5,X6)) | ~l1_pre_topc(k1_pre_topc(X5,X6)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5))) | ~l1_pre_topc(X5)) )),
% 0.21/0.53    inference(superposition,[],[f64,f222])).
% 0.21/0.53  fof(f222,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f221,f77])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_pre_topc(k1_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f221,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f85,f78])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f75])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_compts_1(k2_struct_0(X0),X0) | v1_compts_1(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0] : (((v1_compts_1(X0) | ~v2_compts_1(k2_struct_0(X0),X0)) & (v2_compts_1(k2_struct_0(X0),X0) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : ((v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => (v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_compts_1)).
% 0.21/0.53  fof(f396,plain,(
% 0.21/0.53    v2_compts_1(sK6,k1_pre_topc(sK5,sK6)) | ~spl8_19),
% 0.21/0.53    inference(avatar_component_clause,[],[f394])).
% 0.21/0.53  fof(f467,plain,(
% 0.21/0.53    spl8_19 | ~spl8_18),
% 0.21/0.53    inference(avatar_split_clause,[],[f466,f390,f394])).
% 0.21/0.53  fof(f390,plain,(
% 0.21/0.53    spl8_18 <=> sP3(k1_pre_topc(sK5,sK6),sK6)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.53  fof(f466,plain,(
% 0.21/0.53    v2_compts_1(sK6,k1_pre_topc(sK5,sK6)) | ~spl8_18),
% 0.21/0.53    inference(subsumption_resolution,[],[f465,f57])).
% 0.21/0.53  fof(f465,plain,(
% 0.21/0.53    v2_compts_1(sK6,k1_pre_topc(sK5,sK6)) | ~l1_pre_topc(sK5) | ~spl8_18),
% 0.21/0.53    inference(subsumption_resolution,[],[f464,f58])).
% 0.21/0.53  fof(f464,plain,(
% 0.21/0.53    v2_compts_1(sK6,k1_pre_topc(sK5,sK6)) | ~m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) | ~l1_pre_topc(sK5) | ~spl8_18),
% 0.21/0.53    inference(subsumption_resolution,[],[f460,f103])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f62,f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.53  fof(f460,plain,(
% 0.21/0.53    v2_compts_1(sK6,k1_pre_topc(sK5,sK6)) | ~m1_subset_1(sK6,k1_zfmisc_1(sK6)) | ~m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) | ~l1_pre_topc(sK5) | ~spl8_18),
% 0.21/0.53    inference(resolution,[],[f154,f391])).
% 0.21/0.53  fof(f391,plain,(
% 0.21/0.53    sP3(k1_pre_topc(sK5,sK6),sK6) | ~spl8_18),
% 0.21/0.53    inference(avatar_component_clause,[],[f390])).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    ( ! [X6,X8,X7] : (~sP3(k1_pre_topc(X6,X7),X8) | v2_compts_1(X8,k1_pre_topc(X6,X7)) | ~m1_subset_1(X8,k1_zfmisc_1(X7)) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6))) | ~l1_pre_topc(X6)) )),
% 0.21/0.53    inference(superposition,[],[f83,f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X0,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v2_compts_1(X3,X0) | ~sP3(X0,X3)) )),
% 0.21/0.53    inference(equality_resolution,[],[f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (v2_compts_1(X3,X0) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~sP3(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ! [X0,X1] : ((sP3(X0,X1) | (~v2_compts_1(sK7(X0,X1),X0) & sK7(X0,X1) = X1 & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v2_compts_1(X3,X0) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP3(X0,X1)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : (~v2_compts_1(X2,X0) & X1 = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_compts_1(sK7(X0,X1),X0) & sK7(X0,X1) = X1 & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ! [X0,X1] : ((sP3(X0,X1) | ? [X2] : (~v2_compts_1(X2,X0) & X1 = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v2_compts_1(X3,X0) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP3(X0,X1)))),
% 0.21/0.53    inference(rectify,[],[f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ! [X1,X2] : ((sP3(X1,X2) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP3(X1,X2)))),
% 0.21/0.53    inference(nnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X1,X2] : (sP3(X1,X2) <=> ! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.53  fof(f438,plain,(
% 0.21/0.53    ~spl8_6 | spl8_18 | ~spl8_21),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f437])).
% 0.21/0.53  fof(f437,plain,(
% 0.21/0.53    $false | (~spl8_6 | spl8_18 | ~spl8_21)),
% 0.21/0.53    inference(subsumption_resolution,[],[f404,f418])).
% 0.21/0.53  fof(f418,plain,(
% 0.21/0.53    m1_pre_topc(k1_pre_topc(sK5,sK6),sK5) | ~spl8_21),
% 0.21/0.53    inference(avatar_component_clause,[],[f417])).
% 0.21/0.53  fof(f417,plain,(
% 0.21/0.53    spl8_21 <=> m1_pre_topc(k1_pre_topc(sK5,sK6),sK5)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.21/0.53  fof(f404,plain,(
% 0.21/0.53    ~m1_pre_topc(k1_pre_topc(sK5,sK6),sK5) | (~spl8_6 | spl8_18)),
% 0.21/0.53    inference(subsumption_resolution,[],[f403,f57])).
% 0.21/0.53  fof(f403,plain,(
% 0.21/0.53    ~m1_pre_topc(k1_pre_topc(sK5,sK6),sK5) | ~l1_pre_topc(sK5) | (~spl8_6 | spl8_18)),
% 0.21/0.53    inference(subsumption_resolution,[],[f402,f58])).
% 0.21/0.53  % (12892)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.53  fof(f402,plain,(
% 0.21/0.53    ~m1_pre_topc(k1_pre_topc(sK5,sK6),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) | ~l1_pre_topc(sK5) | (~spl8_6 | spl8_18)),
% 0.21/0.53    inference(subsumption_resolution,[],[f399,f86])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f80])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(flattening,[],[f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f399,plain,(
% 0.21/0.53    ~r1_tarski(sK6,sK6) | ~m1_pre_topc(k1_pre_topc(sK5,sK6),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) | ~l1_pre_topc(sK5) | (~spl8_6 | spl8_18)),
% 0.21/0.53    inference(resolution,[],[f392,f314])).
% 0.21/0.53  fof(f314,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sP3(k1_pre_topc(X0,X1),sK6) | ~r1_tarski(sK6,X1) | ~m1_pre_topc(k1_pre_topc(X0,X1),sK5) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl8_6),
% 0.21/0.53    inference(superposition,[],[f277,f222])).
% 0.21/0.53  fof(f277,plain,(
% 0.21/0.53    ( ! [X1] : (~r1_tarski(sK6,k2_struct_0(X1)) | sP3(X1,sK6) | ~m1_pre_topc(X1,sK5)) ) | ~spl8_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f276])).
% 0.21/0.53  fof(f276,plain,(
% 0.21/0.53    spl8_6 <=> ! [X1] : (~r1_tarski(sK6,k2_struct_0(X1)) | sP3(X1,sK6) | ~m1_pre_topc(X1,sK5))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.53  fof(f392,plain,(
% 0.21/0.53    ~sP3(k1_pre_topc(sK5,sK6),sK6) | spl8_18),
% 0.21/0.53    inference(avatar_component_clause,[],[f390])).
% 0.21/0.53  fof(f429,plain,(
% 0.21/0.53    spl8_21),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f428])).
% 0.21/0.53  fof(f428,plain,(
% 0.21/0.53    $false | spl8_21),
% 0.21/0.53    inference(subsumption_resolution,[],[f427,f57])).
% 0.21/0.53  fof(f427,plain,(
% 0.21/0.53    ~l1_pre_topc(sK5) | spl8_21),
% 0.21/0.53    inference(subsumption_resolution,[],[f426,f58])).
% 0.21/0.53  fof(f426,plain,(
% 0.21/0.53    ~m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) | ~l1_pre_topc(sK5) | spl8_21),
% 0.21/0.53    inference(resolution,[],[f419,f78])).
% 0.21/0.53  fof(f419,plain,(
% 0.21/0.53    ~m1_pre_topc(k1_pre_topc(sK5,sK6),sK5) | spl8_21),
% 0.21/0.53    inference(avatar_component_clause,[],[f417])).
% 0.21/0.53  fof(f278,plain,(
% 0.21/0.53    ~spl8_5 | spl8_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f190,f276,f132])).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    ( ! [X1] : (~r1_tarski(sK6,k2_struct_0(X1)) | ~m1_pre_topc(X1,sK5) | ~v2_compts_1(sK6,sK5) | sP3(X1,sK6)) )),
% 0.21/0.53    inference(resolution,[],[f187,f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~sP4(X0,X1,X2) | ~v2_compts_1(X0,X2) | sP3(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((v2_compts_1(X0,X2) | ~sP3(X1,X0)) & (sP3(X1,X0) | ~v2_compts_1(X0,X2))) | ~sP4(X0,X1,X2))),
% 0.21/0.53    inference(rectify,[],[f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (((v2_compts_1(X2,X0) | ~sP3(X1,X2)) & (sP3(X1,X2) | ~v2_compts_1(X2,X0))) | ~sP4(X2,X1,X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X2,X1,X0] : ((v2_compts_1(X2,X0) <=> sP3(X1,X2)) | ~sP4(X2,X1,X0))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.21/0.53  fof(f187,plain,(
% 0.21/0.53    ( ! [X0] : (sP4(sK6,X0,sK5) | ~r1_tarski(sK6,k2_struct_0(X0)) | ~m1_pre_topc(X0,sK5)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f180,f57])).
% 0.21/0.53  fof(f180,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(sK6,k2_struct_0(X0)) | sP4(sK6,X0,sK5) | ~m1_pre_topc(X0,sK5) | ~l1_pre_topc(sK5)) )),
% 0.21/0.53    inference(resolution,[],[f73,f58])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | sP4(X2,X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (sP4(X2,X1,X0) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(definition_folding,[],[f19,f30,f29])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) <=> ! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) <=> ! [X3] : ((v2_compts_1(X3,X1) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,k2_struct_0(X1)) => (v2_compts_1(X2,X0) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => v2_compts_1(X3,X1))))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_compts_1)).
% 0.21/0.53  fof(f274,plain,(
% 0.21/0.53    ~spl8_2 | spl8_5),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f273])).
% 0.21/0.53  fof(f273,plain,(
% 0.21/0.53    $false | (~spl8_2 | spl8_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f272,f104])).
% 0.21/0.53  fof(f272,plain,(
% 0.21/0.53    ~sP1(sK6,sK5) | spl8_5),
% 0.21/0.53    inference(subsumption_resolution,[],[f269,f133])).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    ~v2_compts_1(sK6,sK5) | spl8_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f132])).
% 0.21/0.53  fof(f269,plain,(
% 0.21/0.53    v2_compts_1(sK6,sK5) | ~sP1(sK6,sK5) | spl8_5),
% 0.21/0.53    inference(resolution,[],[f267,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_compts_1(k1_pre_topc(X1,X0)) | v2_compts_1(X0,X1) | ~sP1(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f267,plain,(
% 0.21/0.53    ~v1_compts_1(k1_pre_topc(sK5,sK6)) | spl8_5),
% 0.21/0.53    inference(subsumption_resolution,[],[f266,f57])).
% 0.21/0.53  fof(f266,plain,(
% 0.21/0.53    ~l1_pre_topc(sK5) | ~v1_compts_1(k1_pre_topc(sK5,sK6)) | spl8_5),
% 0.21/0.53    inference(subsumption_resolution,[],[f265,f58])).
% 0.21/0.53  fof(f265,plain,(
% 0.21/0.53    ~m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) | ~l1_pre_topc(sK5) | ~v1_compts_1(k1_pre_topc(sK5,sK6)) | spl8_5),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f264])).
% 0.21/0.53  fof(f264,plain,(
% 0.21/0.53    ~m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) | ~l1_pre_topc(sK5) | ~v1_compts_1(k1_pre_topc(sK5,sK6)) | ~m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) | ~l1_pre_topc(sK5) | spl8_5),
% 0.21/0.53    inference(resolution,[],[f263,f78])).
% 0.21/0.53  fof(f263,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_pre_topc(k1_pre_topc(X0,sK6),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_compts_1(k1_pre_topc(X0,sK6))) ) | spl8_5),
% 0.21/0.53    inference(subsumption_resolution,[],[f262,f86])).
% 0.21/0.53  fof(f262,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_compts_1(k1_pre_topc(X0,sK6)) | ~m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r1_tarski(sK6,sK6) | ~m1_pre_topc(k1_pre_topc(X0,sK6),sK5)) ) | spl8_5),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f259])).
% 0.21/0.53  fof(f259,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_compts_1(k1_pre_topc(X0,sK6)) | ~m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r1_tarski(sK6,sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_pre_topc(k1_pre_topc(X0,sK6),sK5)) ) | spl8_5),
% 0.21/0.53    inference(resolution,[],[f230,f231])).
% 0.21/0.53  fof(f231,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v2_compts_1(sK6,k1_pre_topc(X0,X1)) | ~r1_tarski(sK6,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_pre_topc(k1_pre_topc(X0,X1),sK5)) ) | spl8_5),
% 0.21/0.53    inference(resolution,[],[f225,f108])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sP3(X0,X1) | ~v2_compts_1(X1,X0)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f107])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v2_compts_1(X1,X0) | sP3(X0,X1) | sP3(X0,X1)) )),
% 0.21/0.53    inference(superposition,[],[f72,f71])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sK7(X0,X1) = X1 | sP3(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f46])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v2_compts_1(sK7(X0,X1),X0) | sP3(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f46])).
% 0.21/0.53  fof(f225,plain,(
% 0.21/0.53    ( ! [X4,X3] : (~sP3(k1_pre_topc(X3,X4),sK6) | ~m1_pre_topc(k1_pre_topc(X3,X4),sK5) | ~r1_tarski(sK6,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3)) ) | spl8_5),
% 0.21/0.53    inference(superposition,[],[f191,f222])).
% 0.21/0.53  fof(f191,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(sK6,k2_struct_0(X0)) | ~m1_pre_topc(X0,sK5) | ~sP3(X0,sK6)) ) | spl8_5),
% 0.21/0.53    inference(subsumption_resolution,[],[f189,f133])).
% 0.21/0.53  fof(f189,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(sK6,k2_struct_0(X0)) | ~m1_pre_topc(X0,sK5) | ~sP3(X0,sK6) | v2_compts_1(sK6,sK5)) )),
% 0.21/0.53    inference(resolution,[],[f187,f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~sP4(X0,X1,X2) | ~sP3(X1,X0) | v2_compts_1(X0,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f42])).
% 0.21/0.53  fof(f230,plain,(
% 0.21/0.53    ( ! [X8,X7] : (v2_compts_1(X8,k1_pre_topc(X7,X8)) | ~v1_compts_1(k1_pre_topc(X7,X8)) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7))) | ~l1_pre_topc(X7)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f227,f144])).
% 0.21/0.53  fof(f227,plain,(
% 0.21/0.53    ( ! [X8,X7] : (v2_compts_1(X8,k1_pre_topc(X7,X8)) | ~v1_compts_1(k1_pre_topc(X7,X8)) | ~l1_pre_topc(k1_pre_topc(X7,X8)) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7))) | ~l1_pre_topc(X7)) )),
% 0.21/0.53    inference(superposition,[],[f63,f222])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X0] : (v2_compts_1(k2_struct_0(X0),X0) | ~v1_compts_1(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f271,plain,(
% 0.21/0.53    ~spl8_1 | spl8_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f270,f132,f89])).
% 0.21/0.53  fof(f270,plain,(
% 0.21/0.53    ~sP0(sK6,sK5) | spl8_5),
% 0.21/0.53    inference(subsumption_resolution,[],[f268,f133])).
% 0.21/0.53  fof(f268,plain,(
% 0.21/0.53    v2_compts_1(sK6,sK5) | ~sP0(sK6,sK5) | spl8_5),
% 0.21/0.53    inference(resolution,[],[f267,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_compts_1(k1_pre_topc(X1,X0)) | v2_compts_1(X0,X1) | ~sP0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    spl8_1 | spl8_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f60,f93,f89])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    sP2(sK5,sK6) | sP0(sK6,sK5)),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (12872)------------------------------
% 0.21/0.53  % (12872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12872)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (12872)Memory used [KB]: 6396
% 0.21/0.53  % (12872)Time elapsed: 0.105 s
% 0.21/0.53  % (12872)------------------------------
% 0.21/0.53  % (12872)------------------------------
% 0.21/0.53  % (12867)Success in time 0.173 s
%------------------------------------------------------------------------------
