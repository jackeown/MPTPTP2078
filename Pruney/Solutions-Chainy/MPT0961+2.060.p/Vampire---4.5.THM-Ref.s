%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 395 expanded)
%              Number of leaves         :   26 ( 121 expanded)
%              Depth                    :   21
%              Number of atoms          :  421 (1198 expanded)
%              Number of equality atoms :  107 ( 460 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f489,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f69,f73,f77,f93,f96,f276,f284,f338,f400,f409,f427,f447,f485,f488])).

fof(f488,plain,
    ( spl2_27
    | ~ spl2_33 ),
    inference(avatar_contradiction_clause,[],[f487])).

fof(f487,plain,
    ( $false
    | spl2_27
    | ~ spl2_33 ),
    inference(subsumption_resolution,[],[f426,f484])).

fof(f484,plain,
    ( ! [X3] : v1_funct_2(k1_xboole_0,k1_xboole_0,X3)
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f483])).

fof(f483,plain,
    ( spl2_33
  <=> ! [X3] : v1_funct_2(k1_xboole_0,k1_xboole_0,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f426,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k2_relat_1(k1_xboole_0))
    | spl2_27 ),
    inference(avatar_component_clause,[],[f425])).

fof(f425,plain,
    ( spl2_27
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f485,plain,
    ( ~ spl2_7
    | spl2_33
    | ~ spl2_13
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f481,f407,f336,f483,f83])).

fof(f83,plain,
    ( spl2_7
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f336,plain,
    ( spl2_13
  <=> k1_xboole_0 = k1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f407,plain,
    ( spl2_25
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f481,plain,
    ( ! [X3] :
        ( v1_funct_2(k1_xboole_0,k1_xboole_0,X3)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl2_13
    | ~ spl2_25 ),
    inference(forward_demodulation,[],[f480,f408])).

fof(f408,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f407])).

fof(f480,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(sK0,k1_xboole_0,X3) )
    | ~ spl2_13
    | ~ spl2_25 ),
    inference(forward_demodulation,[],[f462,f408])).

fof(f462,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(sK0,k1_xboole_0,X3) )
    | ~ spl2_13 ),
    inference(trivial_inequality_removal,[],[f459])).

fof(f459,plain,
    ( ! [X3] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(sK0,k1_xboole_0,X3) )
    | ~ spl2_13 ),
    inference(superposition,[],[f153,f337])).

fof(f337,plain,
    ( k1_xboole_0 = k1_relat_1(sK0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f336])).

fof(f153,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X1,k1_xboole_0,X0) ) ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f151,f52])).

fof(f52,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

% (8433)Refutation not found, incomplete strategy% (8433)------------------------------
% (8433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

% (8433)Termination reason: Refutation not found, incomplete strategy

% (8433)Memory used [KB]: 10618
% (8433)Time elapsed: 0.084 s
% (8433)------------------------------
% (8433)------------------------------
fof(f151,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(superposition,[],[f87,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f87,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f56,f52])).

fof(f56,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f447,plain,
    ( spl2_7
    | ~ spl2_10
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f420,f407,f282,f83])).

fof(f282,plain,
    ( spl2_10
  <=> m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f420,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_10
    | ~ spl2_25 ),
    inference(superposition,[],[f283,f408])).

fof(f283,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f282])).

fof(f427,plain,
    ( ~ spl2_27
    | spl2_2
    | ~ spl2_15
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f423,f407,f345,f62,f425])).

fof(f62,plain,
    ( spl2_2
  <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f345,plain,
    ( spl2_15
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f423,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k2_relat_1(k1_xboole_0))
    | spl2_2
    | ~ spl2_15
    | ~ spl2_25 ),
    inference(forward_demodulation,[],[f414,f346])).

fof(f346,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f345])).

fof(f414,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))
    | spl2_2
    | ~ spl2_25 ),
    inference(superposition,[],[f63,f408])).

fof(f63,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f409,plain,
    ( spl2_25
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f405,f282,f75,f407])).

fof(f75,plain,
    ( spl2_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f405,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(resolution,[],[f295,f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f295,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(resolution,[],[f283,f97])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl2_5 ),
    inference(resolution,[],[f50,f76])).

fof(f76,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f400,plain,
    ( spl2_15
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f399,f282,f75,f345])).

fof(f399,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f332,f324])).

fof(f324,plain,
    ( ! [X39] : k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X39,k1_relat_1(k1_relat_1(k1_relat_1(sK0)))))
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(resolution,[],[f283,f173])).

fof(f173,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(k1_relat_1(X4))))) )
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f171,f52])).

fof(f171,plain,
    ( ! [X4,X5,X3] :
        ( k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(k1_relat_1(X4)))))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5))) )
    | ~ spl2_5 ),
    inference(resolution,[],[f146,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f43,f42])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f146,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(X4)))) )
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f144,f52])).

fof(f144,plain,
    ( ! [X4,X5,X3] :
        ( k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(X4))))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5))) )
    | ~ spl2_5 ),
    inference(resolution,[],[f130,f102])).

fof(f130,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(X4))) )
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f128,f52])).

fof(f128,plain,
    ( ! [X4,X5,X3] :
        ( k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(X4)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5))) )
    | ~ spl2_5 ),
    inference(resolution,[],[f109,f102])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X0,X1)) )
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f107,f52])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
    | ~ spl2_5 ),
    inference(resolution,[],[f106,f43])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k1_relat_1(X0) )
    | ~ spl2_5 ),
    inference(resolution,[],[f105,f35])).

fof(f105,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,k1_relat_1(X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f104,f52])).

fof(f104,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | ~ r2_hidden(X2,k1_relat_1(X0)) )
    | ~ spl2_5 ),
    inference(resolution,[],[f102,f97])).

fof(f332,plain,
    ( ! [X52] : k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relset_1(k1_xboole_0,X52,k1_relat_1(k1_relat_1(k1_relat_1(sK0))))))
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(resolution,[],[f283,f205])).

fof(f205,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(k1_relat_1(X4)))))) )
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f203,f52])).

fof(f203,plain,
    ( ! [X4,X5,X3] :
        ( k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(k1_relat_1(X4))))))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5))) )
    | ~ spl2_5 ),
    inference(resolution,[],[f169,f102])).

fof(f169,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(X4))))) )
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f167,f52])).

fof(f167,plain,
    ( ! [X4,X5,X3] :
        ( k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(X4)))))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5))) )
    | ~ spl2_5 ),
    inference(resolution,[],[f142,f102])).

fof(f142,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(X4)))) )
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f140,f52])).

fof(f140,plain,
    ( ! [X4,X5,X3] :
        ( k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(X4))))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5))) )
    | ~ spl2_5 ),
    inference(resolution,[],[f113,f102])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relset_1(k1_xboole_0,X0,X1))) )
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f111,f52])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relset_1(k1_xboole_0,X0,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
    | ~ spl2_5 ),
    inference(resolution,[],[f110,f43])).

fof(f110,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k1_relat_1(k1_relat_1(X2)) )
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f108,f52])).

fof(f108,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 = k1_relat_1(k1_relat_1(X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3))) )
    | ~ spl2_5 ),
    inference(resolution,[],[f106,f102])).

fof(f338,plain,
    ( spl2_13
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f297,f282,f75,f336])).

fof(f297,plain,
    ( k1_xboole_0 = k1_relat_1(sK0)
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(resolution,[],[f283,f106])).

fof(f284,plain,
    ( spl2_10
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f280,f274,f65,f282])).

fof(f65,plain,
    ( spl2_3
  <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f274,plain,
    ( spl2_9
  <=> k1_xboole_0 = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f280,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f277,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f277,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)))
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(superposition,[],[f95,f275])).

fof(f275,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f274])).

fof(f95,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f276,plain,
    ( spl2_2
    | spl2_9
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f269,f65,f274,f62])).

fof(f269,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl2_3 ),
    inference(resolution,[],[f268,f95])).

fof(f268,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
      | k1_xboole_0 = X1
      | v1_funct_2(X0,k1_relat_1(X0),X1) ) ),
    inference(equality_resolution,[],[f231])).

fof(f231,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f230])).

fof(f230,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f46,f42])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f96,plain,
    ( spl2_3
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f94,f91,f65])).

fof(f91,plain,
    ( spl2_8
  <=> r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f94,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ spl2_8 ),
    inference(resolution,[],[f92,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f92,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f91])).

fof(f93,plain,
    ( spl2_8
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f89,f71,f91])).

fof(f71,plain,
    ( spl2_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f89,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl2_4 ),
    inference(resolution,[],[f34,f72])).

fof(f72,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f77,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f33,f75])).

fof(f33,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f73,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f30,f71])).

fof(f30,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
      | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
      | ~ v1_funct_1(sK0) )
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          | ~ v1_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
        | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
        | ~ v1_funct_1(sK0) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f69,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f31,f59])).

fof(f59,plain,
    ( spl2_1
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f31,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f32,f65,f62,f59])).

fof(f32,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:44:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (8427)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.46  % (8428)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (8435)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (8435)Refutation not found, incomplete strategy% (8435)------------------------------
% 0.21/0.48  % (8435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (8435)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (8435)Memory used [KB]: 1663
% 0.21/0.48  % (8435)Time elapsed: 0.073 s
% 0.21/0.48  % (8435)------------------------------
% 0.21/0.48  % (8435)------------------------------
% 0.21/0.49  % (8436)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (8433)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (8431)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (8432)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (8428)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f489,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f67,f69,f73,f77,f93,f96,f276,f284,f338,f400,f409,f427,f447,f485,f488])).
% 0.21/0.49  fof(f488,plain,(
% 0.21/0.49    spl2_27 | ~spl2_33),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f487])).
% 0.21/0.49  fof(f487,plain,(
% 0.21/0.49    $false | (spl2_27 | ~spl2_33)),
% 0.21/0.49    inference(subsumption_resolution,[],[f426,f484])).
% 0.21/0.49  fof(f484,plain,(
% 0.21/0.49    ( ! [X3] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X3)) ) | ~spl2_33),
% 0.21/0.49    inference(avatar_component_clause,[],[f483])).
% 0.21/0.49  fof(f483,plain,(
% 0.21/0.49    spl2_33 <=> ! [X3] : v1_funct_2(k1_xboole_0,k1_xboole_0,X3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 0.21/0.49  fof(f426,plain,(
% 0.21/0.49    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k2_relat_1(k1_xboole_0)) | spl2_27),
% 0.21/0.49    inference(avatar_component_clause,[],[f425])).
% 0.21/0.49  fof(f425,plain,(
% 0.21/0.49    spl2_27 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k2_relat_1(k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.21/0.49  fof(f485,plain,(
% 0.21/0.49    ~spl2_7 | spl2_33 | ~spl2_13 | ~spl2_25),
% 0.21/0.49    inference(avatar_split_clause,[],[f481,f407,f336,f483,f83])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    spl2_7 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.49  fof(f336,plain,(
% 0.21/0.49    spl2_13 <=> k1_xboole_0 = k1_relat_1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.49  fof(f407,plain,(
% 0.21/0.49    spl2_25 <=> k1_xboole_0 = sK0),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.21/0.49  fof(f481,plain,(
% 0.21/0.49    ( ! [X3] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X3) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))) ) | (~spl2_13 | ~spl2_25)),
% 0.21/0.49    inference(forward_demodulation,[],[f480,f408])).
% 0.21/0.49  fof(f408,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | ~spl2_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f407])).
% 0.21/0.49  fof(f480,plain,(
% 0.21/0.49    ( ! [X3] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(sK0,k1_xboole_0,X3)) ) | (~spl2_13 | ~spl2_25)),
% 0.21/0.49    inference(forward_demodulation,[],[f462,f408])).
% 0.21/0.49  fof(f462,plain,(
% 0.21/0.49    ( ! [X3] : (~m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(sK0,k1_xboole_0,X3)) ) | ~spl2_13),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f459])).
% 0.21/0.49  fof(f459,plain,(
% 0.21/0.49    ( ! [X3] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(sK0,k1_xboole_0,X3)) ) | ~spl2_13),
% 0.21/0.49    inference(superposition,[],[f153,f337])).
% 0.21/0.49  fof(f337,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(sK0) | ~spl2_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f336])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X1,k1_xboole_0,X0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f152])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f151,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.49    inference(flattening,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f2])).
% 0.21/0.49  % (8433)Refutation not found, incomplete strategy% (8433)------------------------------
% 0.21/0.49  % (8433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.49  % (8433)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (8433)Memory used [KB]: 10618
% 0.21/0.49  % (8433)Time elapsed: 0.084 s
% 0.21/0.49  % (8433)------------------------------
% 0.21/0.49  % (8433)------------------------------
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 0.21/0.49    inference(superposition,[],[f87,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f56,f52])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.49    inference(equality_resolution,[],[f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.49  fof(f447,plain,(
% 0.21/0.49    spl2_7 | ~spl2_10 | ~spl2_25),
% 0.21/0.49    inference(avatar_split_clause,[],[f420,f407,f282,f83])).
% 0.21/0.49  fof(f282,plain,(
% 0.21/0.49    spl2_10 <=> m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.49  fof(f420,plain,(
% 0.21/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl2_10 | ~spl2_25)),
% 0.21/0.49    inference(superposition,[],[f283,f408])).
% 0.21/0.49  fof(f283,plain,(
% 0.21/0.49    m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) | ~spl2_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f282])).
% 0.21/0.49  fof(f427,plain,(
% 0.21/0.49    ~spl2_27 | spl2_2 | ~spl2_15 | ~spl2_25),
% 0.21/0.49    inference(avatar_split_clause,[],[f423,f407,f345,f62,f425])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl2_2 <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.49  fof(f345,plain,(
% 0.21/0.49    spl2_15 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.49  fof(f423,plain,(
% 0.21/0.49    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k2_relat_1(k1_xboole_0)) | (spl2_2 | ~spl2_15 | ~spl2_25)),
% 0.21/0.49    inference(forward_demodulation,[],[f414,f346])).
% 0.21/0.49  fof(f346,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl2_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f345])).
% 0.21/0.49  fof(f414,plain,(
% 0.21/0.49    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) | (spl2_2 | ~spl2_25)),
% 0.21/0.49    inference(superposition,[],[f63,f408])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | spl2_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f62])).
% 0.21/0.49  fof(f409,plain,(
% 0.21/0.49    spl2_25 | ~spl2_5 | ~spl2_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f405,f282,f75,f407])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    spl2_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.49  fof(f405,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | (~spl2_5 | ~spl2_10)),
% 0.21/0.49    inference(resolution,[],[f295,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)) | k1_xboole_0 = X0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).
% 0.21/0.49  fof(f295,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | (~spl2_5 | ~spl2_10)),
% 0.21/0.49    inference(resolution,[],[f283,f97])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) ) | ~spl2_5),
% 0.21/0.49    inference(resolution,[],[f50,f76])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0) | ~spl2_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f75])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.49  fof(f400,plain,(
% 0.21/0.49    spl2_15 | ~spl2_5 | ~spl2_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f399,f282,f75,f345])).
% 0.21/0.49  fof(f399,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl2_5 | ~spl2_10)),
% 0.21/0.49    inference(forward_demodulation,[],[f332,f324])).
% 0.21/0.49  fof(f324,plain,(
% 0.21/0.49    ( ! [X39] : (k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X39,k1_relat_1(k1_relat_1(k1_relat_1(sK0)))))) ) | (~spl2_5 | ~spl2_10)),
% 0.21/0.49    inference(resolution,[],[f283,f173])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    ( ! [X4,X3] : (~m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(k1_relat_1(X4)))))) ) | ~spl2_5),
% 0.21/0.49    inference(forward_demodulation,[],[f171,f52])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(k1_relat_1(X4))))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))) ) | ~spl2_5),
% 0.21/0.49    inference(resolution,[],[f146,f102])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f101])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(superposition,[],[f43,f42])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    ( ! [X4,X3] : (~m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(X4))))) ) | ~spl2_5),
% 0.21/0.49    inference(forward_demodulation,[],[f144,f52])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))) ) | ~spl2_5),
% 0.21/0.49    inference(resolution,[],[f130,f102])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ( ! [X4,X3] : (~m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(X4)))) ) | ~spl2_5),
% 0.21/0.49    inference(forward_demodulation,[],[f128,f52])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))) ) | ~spl2_5),
% 0.21/0.49    inference(resolution,[],[f109,f102])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X0,X1))) ) | ~spl2_5),
% 0.21/0.49    inference(forward_demodulation,[],[f107,f52])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | ~spl2_5),
% 0.21/0.49    inference(resolution,[],[f106,f43])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(X0)) ) | ~spl2_5),
% 0.21/0.49    inference(resolution,[],[f105,f35])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~r2_hidden(X2,k1_relat_1(X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl2_5),
% 0.21/0.49    inference(forward_demodulation,[],[f104,f52])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~r2_hidden(X2,k1_relat_1(X0))) ) | ~spl2_5),
% 0.21/0.49    inference(resolution,[],[f102,f97])).
% 0.21/0.49  fof(f332,plain,(
% 0.21/0.49    ( ! [X52] : (k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relset_1(k1_xboole_0,X52,k1_relat_1(k1_relat_1(k1_relat_1(sK0))))))) ) | (~spl2_5 | ~spl2_10)),
% 0.21/0.49    inference(resolution,[],[f283,f205])).
% 0.21/0.49  fof(f205,plain,(
% 0.21/0.49    ( ! [X4,X3] : (~m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(k1_relat_1(X4))))))) ) | ~spl2_5),
% 0.21/0.49    inference(forward_demodulation,[],[f203,f52])).
% 0.21/0.49  fof(f203,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(k1_relat_1(X4)))))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))) ) | ~spl2_5),
% 0.21/0.49    inference(resolution,[],[f169,f102])).
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    ( ! [X4,X3] : (~m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(X4)))))) ) | ~spl2_5),
% 0.21/0.49    inference(forward_demodulation,[],[f167,f52])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(X4))))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))) ) | ~spl2_5),
% 0.21/0.49    inference(resolution,[],[f142,f102])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    ( ! [X4,X3] : (~m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(X4))))) ) | ~spl2_5),
% 0.21/0.49    inference(forward_demodulation,[],[f140,f52])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))) ) | ~spl2_5),
% 0.21/0.49    inference(resolution,[],[f113,f102])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relset_1(k1_xboole_0,X0,X1)))) ) | ~spl2_5),
% 0.21/0.49    inference(forward_demodulation,[],[f111,f52])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relset_1(k1_xboole_0,X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | ~spl2_5),
% 0.21/0.49    inference(resolution,[],[f110,f43])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(k1_relat_1(X2))) ) | ~spl2_5),
% 0.21/0.49    inference(forward_demodulation,[],[f108,f52])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k1_xboole_0 = k1_relat_1(k1_relat_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))) ) | ~spl2_5),
% 0.21/0.49    inference(resolution,[],[f106,f102])).
% 0.21/0.49  fof(f338,plain,(
% 0.21/0.49    spl2_13 | ~spl2_5 | ~spl2_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f297,f282,f75,f336])).
% 0.21/0.49  fof(f297,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(sK0) | (~spl2_5 | ~spl2_10)),
% 0.21/0.49    inference(resolution,[],[f283,f106])).
% 0.21/0.49  fof(f284,plain,(
% 0.21/0.49    spl2_10 | ~spl2_3 | ~spl2_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f280,f274,f65,f282])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    spl2_3 <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.49  fof(f274,plain,(
% 0.21/0.49    spl2_9 <=> k1_xboole_0 = k2_relat_1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.49  fof(f280,plain,(
% 0.21/0.49    m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) | (~spl2_3 | ~spl2_9)),
% 0.21/0.49    inference(forward_demodulation,[],[f277,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f277,plain,(
% 0.21/0.49    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) | (~spl2_3 | ~spl2_9)),
% 0.21/0.49    inference(superposition,[],[f95,f275])).
% 0.21/0.49  fof(f275,plain,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(sK0) | ~spl2_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f274])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~spl2_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f65])).
% 0.21/0.49  fof(f276,plain,(
% 0.21/0.49    spl2_2 | spl2_9 | ~spl2_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f269,f65,f274,f62])).
% 0.21/0.49  fof(f269,plain,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(sK0) | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~spl2_3),
% 0.21/0.49    inference(resolution,[],[f268,f95])).
% 0.21/0.49  fof(f268,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) | k1_xboole_0 = X1 | v1_funct_2(X0,k1_relat_1(X0),X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f231])).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f230])).
% 0.21/0.49  fof(f230,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(superposition,[],[f46,f42])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    spl2_3 | ~spl2_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f94,f91,f65])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    spl2_8 <=> r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~spl2_8),
% 0.21/0.49    inference(resolution,[],[f92,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.49    inference(unused_predicate_definition_removal,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~spl2_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f91])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    spl2_8 | ~spl2_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f89,f71,f91])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    spl2_4 <=> v1_relat_1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~spl2_4),
% 0.21/0.49    inference(resolution,[],[f34,f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    v1_relat_1(sK0) | ~spl2_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f71])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    spl2_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f33,f75])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    spl2_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f30,f71])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    v1_relat_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    (~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.49    inference(negated_conjecture,[],[f10])).
% 0.21/0.49  fof(f10,conjecture,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    spl2_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f31,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    spl2_1 <=> v1_funct_1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    v1_funct_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ~spl2_1 | ~spl2_2 | ~spl2_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f32,f65,f62,f59])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (8428)------------------------------
% 0.21/0.49  % (8428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (8428)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (8428)Memory used [KB]: 10874
% 0.21/0.49  % (8428)Time elapsed: 0.065 s
% 0.21/0.49  % (8428)------------------------------
% 0.21/0.49  % (8428)------------------------------
% 0.21/0.49  % (8441)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.49  % (8437)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (8421)Success in time 0.135 s
%------------------------------------------------------------------------------
