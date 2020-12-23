%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 240 expanded)
%              Number of leaves         :   33 (  96 expanded)
%              Depth                    :   14
%              Number of atoms          :  485 (1232 expanded)
%              Number of equality atoms :  123 ( 259 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f231,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f89,f94,f99,f104,f119,f123,f146,f155,f165,f172,f187,f191,f207,f225,f226,f229,f230])).

fof(f230,plain,
    ( sK0 != k1_relat_1(sK1)
    | sK1 != k6_partfun1(k1_relat_1(sK1))
    | r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))
    | ~ r2_funct_2(sK0,sK0,sK1,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f229,plain,
    ( spl3_1
    | spl3_17
    | ~ spl3_19 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | spl3_1
    | spl3_17
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f83,f206,f224,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f224,plain,
    ( r2_hidden(sK2(sK0,sK1),sK0)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl3_19
  <=> r2_hidden(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f206,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),sK0)
    | spl3_17 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl3_17
  <=> m1_subset_1(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f83,plain,
    ( ~ v1_xboole_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f226,plain,
    ( k6_partfun1(sK0) != sK1
    | r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))
    | ~ r2_funct_2(sK0,sK0,sK1,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f225,plain,
    ( ~ spl3_7
    | ~ spl3_2
    | spl3_18
    | spl3_19
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f192,f169,f222,f218,f86,f116])).

fof(f116,plain,
    ( spl3_7
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f86,plain,
    ( spl3_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f218,plain,
    ( spl3_18
  <=> k6_partfun1(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f169,plain,
    ( spl3_15
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f192,plain,
    ( r2_hidden(sK2(sK0,sK1),sK0)
    | k6_partfun1(sK0) = sK1
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_15 ),
    inference(superposition,[],[f70,f171])).

fof(f171,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f169])).

fof(f70,plain,(
    ! [X1] :
      ( r2_hidden(sK2(k1_relat_1(X1),X1),k1_relat_1(X1))
      | k6_partfun1(k1_relat_1(X1)) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k6_partfun1(X0) = X1
      | r2_hidden(sK2(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f53,f44])).

fof(f44,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK2(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
            & r2_hidden(sK2(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f207,plain,
    ( ~ spl3_17
    | spl3_11
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f202,f169,f148,f204])).

fof(f148,plain,
    ( spl3_11
  <=> m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f202,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),sK0)
    | spl3_11
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f150,f171])).

fof(f150,plain,
    ( ~ m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f148])).

fof(f191,plain,(
    spl3_16 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | spl3_16 ),
    inference(unit_resulting_resolution,[],[f43,f186])).

fof(f186,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl3_16
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f187,plain,
    ( ~ spl3_16
    | spl3_1
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f174,f162,f81,f184])).

fof(f162,plain,
    ( spl3_14
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f174,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_1
    | ~ spl3_14 ),
    inference(backward_demodulation,[],[f83,f164])).

fof(f164,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f162])).

fof(f172,plain,
    ( ~ spl3_4
    | spl3_15
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f166,f158,f169,f96])).

fof(f96,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f158,plain,
    ( spl3_13
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f166,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_13 ),
    inference(superposition,[],[f160,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f160,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f158])).

fof(f165,plain,
    ( spl3_13
    | spl3_14
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f107,f96,f91,f162,f158])).

fof(f91,plain,
    ( spl3_3
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f107,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | k1_xboole_0 = sK0
    | sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f98,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f98,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f155,plain,
    ( ~ spl3_11
    | ~ spl3_7
    | spl3_12 ),
    inference(avatar_split_clause,[],[f141,f152,f116,f148])).

fof(f152,plain,
    ( spl3_12
  <=> sK1 = k6_partfun1(k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f141,plain,
    ( sK1 = k6_partfun1(k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0) ),
    inference(global_subsumption,[],[f38,f140])).

fof(f140,plain,
    ( sK1 = k6_partfun1(k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f139])).

fof(f139,plain,
    ( sK2(k1_relat_1(sK1),sK1) != sK2(k1_relat_1(sK1),sK1)
    | sK1 = k6_partfun1(k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0) ),
    inference(superposition,[],[f69,f137])).

% (18505)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
fof(f137,plain,(
    ! [X1] :
      ( k1_funct_1(sK1,X1) = X1
      | ~ m1_subset_1(X1,sK0) ) ),
    inference(global_subsumption,[],[f37,f38,f39,f40,f136])).

fof(f136,plain,(
    ! [X1] :
      ( k1_funct_1(sK1,X1) = X1
      | ~ m1_subset_1(X1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_1(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f133])).

fof(f133,plain,(
    ! [X1] :
      ( k1_funct_1(sK1,X1) = X1
      | ~ m1_subset_1(X1,sK0)
      | ~ m1_subset_1(X1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_1(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(superposition,[],[f41,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f41,plain,(
    ! [X2] :
      ( k3_funct_2(sK0,sK0,sK1,X2) = X2
      | ~ m1_subset_1(X2,sK0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))
    & ! [X2] :
        ( k3_funct_2(sK0,sK0,sK1,X2) = X2
        | ~ m1_subset_1(X2,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
            & ! [X2] :
                ( k3_funct_2(X0,X0,X1,X2) = X2
                | ~ m1_subset_1(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ~ r2_funct_2(sK0,sK0,X1,k6_partfun1(sK0))
          & ! [X2] :
              ( k3_funct_2(sK0,sK0,X1,X2) = X2
              | ~ m1_subset_1(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_2(X1,sK0,sK0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ~ r2_funct_2(sK0,sK0,X1,k6_partfun1(sK0))
        & ! [X2] :
            ( k3_funct_2(sK0,sK0,X1,X2) = X2
            | ~ m1_subset_1(X2,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v1_funct_2(X1,sK0,sK0)
        & v1_funct_1(X1) )
   => ( ~ r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))
      & ! [X2] :
          ( k3_funct_2(sK0,sK0,sK1,X2) = X2
          | ~ m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
          & ! [X2] :
              ( k3_funct_2(X0,X0,X1,X2) = X2
              | ~ m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
          & ! [X2] :
              ( k3_funct_2(X0,X0,X1,X2) = X2
              | ~ m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X1,X0,X0)
              & v1_funct_1(X1) )
           => ( ! [X2] :
                  ( m1_subset_1(X2,X0)
                 => k3_funct_2(X0,X0,X1,X2) = X2 )
             => r2_funct_2(X0,X0,X1,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,X0)
               => k3_funct_2(X0,X0,X1,X2) = X2 )
           => r2_funct_2(X0,X0,X1,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t201_funct_2)).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f37,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    ! [X1] :
      ( sK2(k1_relat_1(X1),X1) != k1_funct_1(X1,sK2(k1_relat_1(X1),X1))
      | k6_partfun1(k1_relat_1(X1)) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k6_partfun1(X0) = X1
      | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f54,f44])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f38,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f146,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | spl3_10
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f106,f96,f143,f91,f86])).

fof(f143,plain,
    ( spl3_10
  <=> r2_funct_2(sK0,sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f106,plain,
    ( r2_funct_2(sK0,sK0,sK1,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f98,f79])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f78])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f123,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | spl3_6 ),
    inference(unit_resulting_resolution,[],[f46,f114])).

fof(f114,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl3_6
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f119,plain,
    ( ~ spl3_6
    | spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f109,f96,f116,f112])).

fof(f109,plain,
    ( v1_relat_1(sK1)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | ~ spl3_4 ),
    inference(resolution,[],[f98,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f104,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f42,f101])).

fof(f101,plain,
    ( spl3_5
  <=> r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f42,plain,(
    ~ r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f99,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f40,f96])).

fof(f94,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f39,f91])).

fof(f89,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f38,f86])).

fof(f84,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f37,f81])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:03:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (18502)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (18500)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (18510)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (18508)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (18502)Refutation not found, incomplete strategy% (18502)------------------------------
% 0.22/0.52  % (18502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (18502)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (18502)Memory used [KB]: 1791
% 0.22/0.52  % (18502)Time elapsed: 0.119 s
% 0.22/0.52  % (18502)------------------------------
% 0.22/0.52  % (18502)------------------------------
% 0.22/0.52  % (18516)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.52  % (18527)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.53  % (18499)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (18508)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (18514)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  % (18499)Refutation not found, incomplete strategy% (18499)------------------------------
% 0.22/0.53  % (18499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (18499)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (18499)Memory used [KB]: 1791
% 0.22/0.53  % (18499)Time elapsed: 0.112 s
% 0.22/0.53  % (18499)------------------------------
% 0.22/0.53  % (18499)------------------------------
% 0.22/0.53  % (18510)Refutation not found, incomplete strategy% (18510)------------------------------
% 0.22/0.53  % (18510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (18510)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (18510)Memory used [KB]: 10746
% 0.22/0.53  % (18510)Time elapsed: 0.123 s
% 0.22/0.53  % (18510)------------------------------
% 0.22/0.53  % (18510)------------------------------
% 0.22/0.53  % (18504)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (18503)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f231,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f84,f89,f94,f99,f104,f119,f123,f146,f155,f165,f172,f187,f191,f207,f225,f226,f229,f230])).
% 0.22/0.53  fof(f230,plain,(
% 0.22/0.53    sK0 != k1_relat_1(sK1) | sK1 != k6_partfun1(k1_relat_1(sK1)) | r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) | ~r2_funct_2(sK0,sK0,sK1,sK1)),
% 0.22/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.53  fof(f229,plain,(
% 0.22/0.53    spl3_1 | spl3_17 | ~spl3_19),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f227])).
% 0.22/0.53  fof(f227,plain,(
% 0.22/0.53    $false | (spl3_1 | spl3_17 | ~spl3_19)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f83,f206,f224,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.22/0.53    inference(nnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.53  fof(f224,plain,(
% 0.22/0.53    r2_hidden(sK2(sK0,sK1),sK0) | ~spl3_19),
% 0.22/0.53    inference(avatar_component_clause,[],[f222])).
% 0.22/0.53  fof(f222,plain,(
% 0.22/0.53    spl3_19 <=> r2_hidden(sK2(sK0,sK1),sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.53  fof(f206,plain,(
% 0.22/0.53    ~m1_subset_1(sK2(sK0,sK1),sK0) | spl3_17),
% 0.22/0.53    inference(avatar_component_clause,[],[f204])).
% 0.22/0.53  fof(f204,plain,(
% 0.22/0.53    spl3_17 <=> m1_subset_1(sK2(sK0,sK1),sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    ~v1_xboole_0(sK0) | spl3_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f81])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    spl3_1 <=> v1_xboole_0(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.53  fof(f226,plain,(
% 0.22/0.53    k6_partfun1(sK0) != sK1 | r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) | ~r2_funct_2(sK0,sK0,sK1,sK1)),
% 0.22/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.53  fof(f225,plain,(
% 0.22/0.53    ~spl3_7 | ~spl3_2 | spl3_18 | spl3_19 | ~spl3_15),
% 0.22/0.53    inference(avatar_split_clause,[],[f192,f169,f222,f218,f86,f116])).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    spl3_7 <=> v1_relat_1(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    spl3_2 <=> v1_funct_1(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.53  fof(f218,plain,(
% 0.22/0.53    spl3_18 <=> k6_partfun1(sK0) = sK1),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.53  fof(f169,plain,(
% 0.22/0.53    spl3_15 <=> sK0 = k1_relat_1(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.53  fof(f192,plain,(
% 0.22/0.53    r2_hidden(sK2(sK0,sK1),sK0) | k6_partfun1(sK0) = sK1 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl3_15),
% 0.22/0.53    inference(superposition,[],[f70,f171])).
% 0.22/0.53  fof(f171,plain,(
% 0.22/0.53    sK0 = k1_relat_1(sK1) | ~spl3_15),
% 0.22/0.53    inference(avatar_component_clause,[],[f169])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ( ! [X1] : (r2_hidden(sK2(k1_relat_1(X1),X1),k1_relat_1(X1)) | k6_partfun1(k1_relat_1(X1)) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f66])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k6_partfun1(X0) = X1 | r2_hidden(sK2(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f53,f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(rectify,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).
% 0.22/0.53  fof(f207,plain,(
% 0.22/0.53    ~spl3_17 | spl3_11 | ~spl3_15),
% 0.22/0.53    inference(avatar_split_clause,[],[f202,f169,f148,f204])).
% 0.22/0.53  fof(f148,plain,(
% 0.22/0.53    spl3_11 <=> m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.53  fof(f202,plain,(
% 0.22/0.53    ~m1_subset_1(sK2(sK0,sK1),sK0) | (spl3_11 | ~spl3_15)),
% 0.22/0.53    inference(forward_demodulation,[],[f150,f171])).
% 0.22/0.53  fof(f150,plain,(
% 0.22/0.53    ~m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0) | spl3_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f148])).
% 0.22/0.54  fof(f191,plain,(
% 0.22/0.54    spl3_16),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f188])).
% 0.22/0.54  fof(f188,plain,(
% 0.22/0.54    $false | spl3_16),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f43,f186])).
% 0.22/0.54  fof(f186,plain,(
% 0.22/0.54    ~v1_xboole_0(k1_xboole_0) | spl3_16),
% 0.22/0.54    inference(avatar_component_clause,[],[f184])).
% 0.22/0.54  fof(f184,plain,(
% 0.22/0.54    spl3_16 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.54  fof(f187,plain,(
% 0.22/0.54    ~spl3_16 | spl3_1 | ~spl3_14),
% 0.22/0.54    inference(avatar_split_clause,[],[f174,f162,f81,f184])).
% 0.22/0.54  fof(f162,plain,(
% 0.22/0.54    spl3_14 <=> k1_xboole_0 = sK0),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.54  fof(f174,plain,(
% 0.22/0.54    ~v1_xboole_0(k1_xboole_0) | (spl3_1 | ~spl3_14)),
% 0.22/0.54    inference(backward_demodulation,[],[f83,f164])).
% 0.22/0.54  fof(f164,plain,(
% 0.22/0.54    k1_xboole_0 = sK0 | ~spl3_14),
% 0.22/0.54    inference(avatar_component_clause,[],[f162])).
% 0.22/0.54  fof(f172,plain,(
% 0.22/0.54    ~spl3_4 | spl3_15 | ~spl3_13),
% 0.22/0.54    inference(avatar_split_clause,[],[f166,f158,f169,f96])).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.54  fof(f158,plain,(
% 0.22/0.54    spl3_13 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.54  fof(f166,plain,(
% 0.22/0.54    sK0 = k1_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_13),
% 0.22/0.54    inference(superposition,[],[f160,f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.54  fof(f160,plain,(
% 0.22/0.54    sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl3_13),
% 0.22/0.54    inference(avatar_component_clause,[],[f158])).
% 0.22/0.54  fof(f165,plain,(
% 0.22/0.54    spl3_13 | spl3_14 | ~spl3_3 | ~spl3_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f107,f96,f91,f162,f158])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    spl3_3 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.54  fof(f107,plain,(
% 0.22/0.54    ~v1_funct_2(sK1,sK0,sK0) | k1_xboole_0 = sK0 | sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl3_4),
% 0.22/0.54    inference(resolution,[],[f98,f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(nnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(flattening,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f96])).
% 0.22/0.54  fof(f155,plain,(
% 0.22/0.54    ~spl3_11 | ~spl3_7 | spl3_12),
% 0.22/0.54    inference(avatar_split_clause,[],[f141,f152,f116,f148])).
% 0.22/0.54  fof(f152,plain,(
% 0.22/0.54    spl3_12 <=> sK1 = k6_partfun1(k1_relat_1(sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.54  fof(f141,plain,(
% 0.22/0.54    sK1 = k6_partfun1(k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0)),
% 0.22/0.54    inference(global_subsumption,[],[f38,f140])).
% 0.22/0.54  fof(f140,plain,(
% 0.22/0.54    sK1 = k6_partfun1(k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f139])).
% 0.22/0.54  fof(f139,plain,(
% 0.22/0.54    sK2(k1_relat_1(sK1),sK1) != sK2(k1_relat_1(sK1),sK1) | sK1 = k6_partfun1(k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0)),
% 0.22/0.54    inference(superposition,[],[f69,f137])).
% 0.22/0.54  % (18505)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  fof(f137,plain,(
% 0.22/0.54    ( ! [X1] : (k1_funct_1(sK1,X1) = X1 | ~m1_subset_1(X1,sK0)) )),
% 0.22/0.54    inference(global_subsumption,[],[f37,f38,f39,f40,f136])).
% 0.22/0.54  fof(f136,plain,(
% 0.22/0.54    ( ! [X1] : (k1_funct_1(sK1,X1) = X1 | ~m1_subset_1(X1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v1_xboole_0(sK0)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f133])).
% 0.22/0.54  fof(f133,plain,(
% 0.22/0.54    ( ! [X1] : (k1_funct_1(sK1,X1) = X1 | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v1_xboole_0(sK0)) )),
% 0.22/0.54    inference(superposition,[],[f41,f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.22/0.54    inference(flattening,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X2] : (k3_funct_2(sK0,sK0,sK1,X2) = X2 | ~m1_subset_1(X2,sK0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    (~r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) & ! [X2] : (k3_funct_2(sK0,sK0,sK1,X2) = X2 | ~m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)) & ~v1_xboole_0(sK0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f27,f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (~r2_funct_2(sK0,sK0,X1,k6_partfun1(sK0)) & ! [X2] : (k3_funct_2(sK0,sK0,X1,X2) = X2 | ~m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X1,sK0,sK0) & v1_funct_1(X1)) & ~v1_xboole_0(sK0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ? [X1] : (~r2_funct_2(sK0,sK0,X1,k6_partfun1(sK0)) & ! [X2] : (k3_funct_2(sK0,sK0,X1,X2) = X2 | ~m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X1,sK0,sK0) & v1_funct_1(X1)) => (~r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) & ! [X2] : (k3_funct_2(sK0,sK0,sK1,X2) = X2 | ~m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.54    inference(flattening,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : ((~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))) & ~v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,negated_conjecture,(
% 0.22/0.54    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (! [X2] : (m1_subset_1(X2,X0) => k3_funct_2(X0,X0,X1,X2) = X2) => r2_funct_2(X0,X0,X1,k6_partfun1(X0)))))),
% 0.22/0.54    inference(negated_conjecture,[],[f11])).
% 0.22/0.54  fof(f11,conjecture,(
% 0.22/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (! [X2] : (m1_subset_1(X2,X0) => k3_funct_2(X0,X0,X1,X2) = X2) => r2_funct_2(X0,X0,X1,k6_partfun1(X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t201_funct_2)).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ~v1_xboole_0(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ( ! [X1] : (sK2(k1_relat_1(X1),X1) != k1_funct_1(X1,sK2(k1_relat_1(X1),X1)) | k6_partfun1(k1_relat_1(X1)) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f65])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k6_partfun1(X0) = X1 | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f54,f44])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    v1_funct_1(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f146,plain,(
% 0.22/0.54    ~spl3_2 | ~spl3_3 | spl3_10 | ~spl3_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f106,f96,f143,f91,f86])).
% 0.22/0.54  fof(f143,plain,(
% 0.22/0.54    spl3_10 <=> r2_funct_2(sK0,sK0,sK1,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.54  fof(f106,plain,(
% 0.22/0.54    r2_funct_2(sK0,sK0,sK1,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl3_4),
% 0.22/0.54    inference(resolution,[],[f98,f79])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f78])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.54    inference(equality_resolution,[],[f64])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.54    inference(nnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.54    inference(flattening,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    spl3_6),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f120])).
% 0.22/0.54  fof(f120,plain,(
% 0.22/0.54    $false | spl3_6),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f46,f114])).
% 0.22/0.54  fof(f114,plain,(
% 0.22/0.54    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | spl3_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f112])).
% 0.22/0.54  fof(f112,plain,(
% 0.22/0.54    spl3_6 <=> v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.54  fof(f119,plain,(
% 0.22/0.54    ~spl3_6 | spl3_7 | ~spl3_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f109,f96,f116,f112])).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    v1_relat_1(sK1) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | ~spl3_4),
% 0.22/0.54    inference(resolution,[],[f98,f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    ~spl3_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f42,f101])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    spl3_5 <=> r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ~r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    spl3_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f40,f96])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    spl3_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f39,f91])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    spl3_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f38,f86])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    ~spl3_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f37,f81])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (18508)------------------------------
% 0.22/0.54  % (18508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18508)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (18508)Memory used [KB]: 10874
% 0.22/0.54  % (18508)Time elapsed: 0.123 s
% 0.22/0.54  % (18508)------------------------------
% 0.22/0.54  % (18508)------------------------------
% 0.22/0.54  % (18495)Success in time 0.172 s
%------------------------------------------------------------------------------
