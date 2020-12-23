%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1020+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 375 expanded)
%              Number of leaves         :   42 ( 157 expanded)
%              Depth                    :   15
%              Number of atoms          :  717 (1679 expanded)
%              Number of equality atoms :  102 ( 129 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f435,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f84,f89,f99,f104,f109,f114,f119,f124,f132,f137,f150,f158,f184,f201,f211,f218,f240,f253,f277,f287,f360,f393,f422,f431,f434])).

fof(f434,plain,
    ( sK2 != k2_funct_1(sK1)
    | k2_funct_2(sK0,sK1) != k2_funct_1(sK1)
    | r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    | ~ r2_relset_1(sK0,sK0,sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f431,plain,
    ( ~ spl3_12
    | ~ spl3_14
    | ~ spl3_20
    | spl3_41 ),
    inference(avatar_contradiction_clause,[],[f429])).

fof(f429,plain,
    ( $false
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_20
    | spl3_41 ),
    inference(unit_resulting_resolution,[],[f136,f149,f200,f421,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f421,plain,
    ( sK0 != k2_relat_1(sK1)
    | spl3_41 ),
    inference(avatar_component_clause,[],[f419])).

fof(f419,plain,
    ( spl3_41
  <=> sK0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f200,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl3_20
  <=> v2_funct_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f149,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl3_14
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f136,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl3_12
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f422,plain,
    ( spl3_40
    | ~ spl3_41
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_18
    | ~ spl3_26
    | ~ spl3_27
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f413,f357,f282,f272,f181,f134,f129,f121,f101,f419,f415])).

fof(f415,plain,
    ( spl3_40
  <=> sK2 = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f101,plain,
    ( spl3_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f121,plain,
    ( spl3_10
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f129,plain,
    ( spl3_11
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f181,plain,
    ( spl3_18
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f272,plain,
    ( spl3_26
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f282,plain,
    ( spl3_27
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f357,plain,
    ( spl3_39
  <=> k6_partfun1(sK0) = k5_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f413,plain,
    ( sK0 != k2_relat_1(sK1)
    | sK2 = k2_funct_1(sK1)
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_18
    | ~ spl3_26
    | ~ spl3_27
    | ~ spl3_39 ),
    inference(forward_demodulation,[],[f412,f274])).

fof(f274,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f272])).

fof(f412,plain,
    ( sK2 = k2_funct_1(sK1)
    | k2_relat_1(sK1) != k1_relat_1(sK2)
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_18
    | ~ spl3_27
    | ~ spl3_39 ),
    inference(trivial_inequality_removal,[],[f411])).

fof(f411,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | sK2 = k2_funct_1(sK1)
    | k2_relat_1(sK1) != k1_relat_1(sK2)
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_18
    | ~ spl3_27
    | ~ spl3_39 ),
    inference(forward_demodulation,[],[f410,f284])).

fof(f284,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f282])).

fof(f410,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK1))
    | sK2 = k2_funct_1(sK1)
    | k2_relat_1(sK1) != k1_relat_1(sK2)
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_18
    | ~ spl3_39 ),
    inference(subsumption_resolution,[],[f409,f136])).

fof(f409,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK1))
    | sK2 = k2_funct_1(sK1)
    | k2_relat_1(sK1) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_18
    | ~ spl3_39 ),
    inference(subsumption_resolution,[],[f408,f123])).

fof(f123,plain,
    ( v1_funct_1(sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f408,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK1))
    | sK2 = k2_funct_1(sK1)
    | k2_relat_1(sK1) != k1_relat_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_6
    | ~ spl3_11
    | ~ spl3_18
    | ~ spl3_39 ),
    inference(subsumption_resolution,[],[f407,f131])).

fof(f131,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f129])).

fof(f407,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK1))
    | sK2 = k2_funct_1(sK1)
    | k2_relat_1(sK1) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_6
    | ~ spl3_18
    | ~ spl3_39 ),
    inference(subsumption_resolution,[],[f406,f103])).

fof(f103,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f101])).

fof(f406,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK1))
    | sK2 = k2_funct_1(sK1)
    | k2_relat_1(sK1) != k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_18
    | ~ spl3_39 ),
    inference(subsumption_resolution,[],[f403,f183])).

fof(f183,plain,
    ( v2_funct_1(sK1)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f181])).

fof(f403,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK1))
    | sK2 = k2_funct_1(sK1)
    | k2_relat_1(sK1) != k1_relat_1(sK2)
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_39 ),
    inference(superposition,[],[f241,f359])).

fof(f359,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK1,sK2)
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f357])).

fof(f241,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f67,f58])).

fof(f58,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

fof(f393,plain,
    ( ~ spl3_3
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10
    | spl3_38 ),
    inference(avatar_contradiction_clause,[],[f380])).

fof(f380,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10
    | spl3_38 ),
    inference(unit_resulting_resolution,[],[f123,f103,f108,f88,f355,f263])).

fof(f263,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f262])).

fof(f262,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f60,f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f355,plain,
    ( ~ m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl3_38 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl3_38
  <=> m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f88,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f108,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl3_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f360,plain,
    ( ~ spl3_38
    | spl3_39
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f341,f250,f357,f353])).

fof(f250,plain,
    ( spl3_25
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f341,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK1,sK2)
    | ~ m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_25 ),
    inference(resolution,[],[f221,f252])).

fof(f252,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_partfun1(sK0))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f250])).

fof(f221,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_partfun1(X2))
      | k6_partfun1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f55,f57])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f287,plain,
    ( spl3_27
    | ~ spl3_7
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f286,f215,f106,f282])).

fof(f215,plain,
    ( spl3_22
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f286,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl3_7
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f279,f108])).

fof(f279,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_22 ),
    inference(superposition,[],[f68,f217])).

fof(f217,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f215])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f277,plain,
    ( spl3_26
    | ~ spl3_3
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f276,f208,f86,f272])).

fof(f208,plain,
    ( spl3_21
  <=> sK0 = k1_relset_1(sK0,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f276,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_3
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f269,f88])).

fof(f269,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_21 ),
    inference(superposition,[],[f68,f210])).

fof(f210,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f208])).

fof(f253,plain,
    ( spl3_25
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f248,f121,f106,f101,f86,f81,f250])).

fof(f81,plain,
    ( spl3_2
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f248,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_partfun1(sK0))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f247,f123])).

fof(f247,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_partfun1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f246,f108])).

fof(f246,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_partfun1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f245,f103])).

fof(f245,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_partfun1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f242,f88])).

fof(f242,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_partfun1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl3_2 ),
    inference(superposition,[],[f83,f61])).

fof(f83,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f240,plain,
    ( spl3_24
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f235,f121,f116,f111,f106,f237])).

fof(f237,plain,
    ( spl3_24
  <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f111,plain,
    ( spl3_8
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f116,plain,
    ( spl3_9
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f235,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f234,f123])).

fof(f234,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f233,f118])).

fof(f118,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f116])).

fof(f233,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f223,f113])).

fof(f113,plain,
    ( v3_funct_2(sK1,sK0,sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f111])).

fof(f223,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f54,f108])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f218,plain,
    ( spl3_22
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f213,f121,f116,f106,f215])).

fof(f213,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f212,f123])).

fof(f212,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f203,f118])).

fof(f203,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f66,f108])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(f211,plain,
    ( spl3_21
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f206,f101,f96,f86,f208])).

fof(f96,plain,
    ( spl3_5
  <=> v1_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f206,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f205,f103])).

fof(f205,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f202,f98])).

fof(f98,plain,
    ( v1_funct_2(sK2,sK0,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f202,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f66,f88])).

fof(f201,plain,
    ( spl3_20
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f196,f121,f111,f106,f198])).

fof(f196,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f195,f123])).

fof(f195,plain,
    ( ~ v1_funct_1(sK1)
    | v2_funct_2(sK1,sK0)
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f186,f113])).

fof(f186,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_2(sK1,sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f65,f108])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f184,plain,
    ( spl3_18
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f179,f121,f111,f106,f181])).

fof(f179,plain,
    ( v2_funct_1(sK1)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f178,f123])).

fof(f178,plain,
    ( ~ v1_funct_1(sK1)
    | v2_funct_1(sK1)
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f169,f113])).

fof(f169,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f64,f108])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f158,plain,
    ( spl3_15
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f151,f86,f155])).

fof(f155,plain,
    ( spl3_15
  <=> r2_relset_1(sK0,sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f151,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f74,f88])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f150,plain,
    ( spl3_14
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f139,f106,f147])).

fof(f139,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f71,f108])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f137,plain,
    ( spl3_12
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f126,f106,f134])).

fof(f126,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f62,f108])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

% (30360)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f132,plain,
    ( spl3_11
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f125,f86,f129])).

fof(f125,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f62,f88])).

fof(f124,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f44,f121])).

fof(f44,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f40,f39])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v3_funct_2(X2,sK0,sK0)
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v3_funct_2(X2,sK0,sK0)
        & v1_funct_2(X2,sK0,sK0)
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK2,sK0,sK0)
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v3_funct_2(X2,X0,X0)
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
             => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
           => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

fof(f119,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f45,f116])).

fof(f45,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f114,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f46,f111])).

fof(f46,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f109,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f47,f106])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f104,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f48,f101])).

fof(f48,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f99,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f49,f96])).

fof(f49,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f89,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f51,f86])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f84,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f52,f81])).

fof(f52,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f79,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f53,f76])).

fof(f76,plain,
    ( spl3_1
  <=> r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f53,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f41])).

%------------------------------------------------------------------------------
