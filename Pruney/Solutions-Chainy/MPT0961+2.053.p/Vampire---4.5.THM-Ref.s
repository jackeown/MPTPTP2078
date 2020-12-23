%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:18 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 168 expanded)
%              Number of leaves         :   24 (  65 expanded)
%              Depth                    :    9
%              Number of atoms          :  320 ( 544 expanded)
%              Number of equality atoms :   77 ( 125 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f191,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f95,f107,f116,f123,f131,f135,f140,f146,f164,f165,f178])).

fof(f178,plain,
    ( ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | spl1_8
    | ~ spl1_12 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | spl1_8
    | ~ spl1_12 ),
    inference(subsumption_resolution,[],[f176,f130])).

fof(f130,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl1_12
  <=> ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f176,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | spl1_8 ),
    inference(forward_demodulation,[],[f175,f67])).

fof(f67,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl1_3
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f175,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl1_4
    | ~ spl1_5
    | spl1_8 ),
    inference(forward_demodulation,[],[f170,f72])).

fof(f72,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl1_4
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f170,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))
    | ~ spl1_5
    | spl1_8 ),
    inference(backward_demodulation,[],[f102,f79])).

fof(f79,plain,
    ( k1_xboole_0 = sK0
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl1_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f102,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | spl1_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl1_8
  <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f165,plain,
    ( ~ spl1_16
    | spl1_7
    | spl1_8
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f152,f104,f100,f92,f161])).

fof(f161,plain,
    ( spl1_16
  <=> k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f92,plain,
    ( spl1_7
  <=> k1_xboole_0 = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f104,plain,
    ( spl1_9
  <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f152,plain,
    ( k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | spl1_7
    | spl1_8
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f151,f102])).

fof(f151,plain,
    ( k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | spl1_7
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f147,f94])).

fof(f94,plain,
    ( k1_xboole_0 != k2_relat_1(sK0)
    | spl1_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f147,plain,
    ( k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | k1_xboole_0 = k2_relat_1(sK0)
    | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl1_9 ),
    inference(resolution,[],[f105,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f105,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f104])).

fof(f164,plain,
    ( spl1_16
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f149,f104,f161])).

fof(f149,plain,
    ( k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | ~ spl1_9 ),
    inference(resolution,[],[f105,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f146,plain,
    ( spl1_9
    | ~ spl1_14 ),
    inference(avatar_split_clause,[],[f143,f138,f104])).

fof(f138,plain,
    ( spl1_14
  <=> ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK0),X0)
        | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f143,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ spl1_14 ),
    inference(resolution,[],[f139,f47])).

fof(f47,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f139,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK0),X0)
        | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK0)))) )
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f138])).

fof(f140,plain,
    ( spl1_14
    | ~ spl1_13 ),
    inference(avatar_split_clause,[],[f136,f133,f138])).

fof(f133,plain,
    ( spl1_13
  <=> ! [X1,X0] :
        ( ~ r1_tarski(k2_relat_1(sK0),X0)
        | ~ r1_tarski(k1_relat_1(sK0),X1)
        | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f136,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK0),X0)
        | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK0)))) )
    | ~ spl1_13 ),
    inference(resolution,[],[f134,f47])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK0),X0)
        | ~ r1_tarski(k1_relat_1(sK0),X1)
        | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f133])).

fof(f135,plain,
    ( spl1_13
    | ~ spl1_1 ),
    inference(avatar_split_clause,[],[f108,f55,f133])).

fof(f55,plain,
    ( spl1_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK0),X0)
        | ~ r1_tarski(k1_relat_1(sK0),X1)
        | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl1_1 ),
    inference(resolution,[],[f39,f57])).

fof(f57,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f131,plain,
    ( spl1_12
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f126,f121,f129])).

fof(f121,plain,
    ( spl1_11
  <=> ! [X0] :
        ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f126,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl1_11 ),
    inference(subsumption_resolution,[],[f125,f31])).

fof(f31,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f125,plain,
    ( ! [X0] :
        ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,X0)) )
    | ~ spl1_11 ),
    inference(resolution,[],[f122,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f122,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) )
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f121])).

fof(f123,plain,
    ( spl1_11
    | ~ spl1_10 ),
    inference(avatar_split_clause,[],[f118,f114,f121])).

fof(f114,plain,
    ( spl1_10
  <=> ! [X1,X0] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f118,plain,
    ( ! [X0] :
        ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
    | ~ spl1_10 ),
    inference(trivial_inequality_removal,[],[f117])).

fof(f117,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
    | ~ spl1_10 ),
    inference(superposition,[],[f52,f115])).

fof(f115,plain,
    ( ! [X0,X1] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f52,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f116,plain,
    ( spl1_10
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f111,f65,f114])).

fof(f111,plain,
    ( ! [X0,X1] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)
    | ~ spl1_3 ),
    inference(forward_demodulation,[],[f109,f67])).

fof(f109,plain,(
    ! [X0,X1] : k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0) ),
    inference(resolution,[],[f90,f31])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(resolution,[],[f40,f38])).

fof(f107,plain,
    ( ~ spl1_8
    | ~ spl1_9
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f98,f60,f104,f100])).

fof(f60,plain,
    ( spl1_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

% (13936)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f98,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl1_2 ),
    inference(subsumption_resolution,[],[f28,f62])).

fof(f62,plain,
    ( v1_funct_1(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f28,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
      | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
      | ~ v1_funct_1(sK0) )
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f20])).

fof(f20,plain,
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

fof(f12,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f95,plain,
    ( spl1_5
    | ~ spl1_7
    | ~ spl1_1 ),
    inference(avatar_split_clause,[],[f85,f55,f92,f77])).

fof(f85,plain,
    ( k1_xboole_0 != k2_relat_1(sK0)
    | k1_xboole_0 = sK0
    | ~ spl1_1 ),
    inference(resolution,[],[f33,f57])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f73,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f30,f70])).

fof(f30,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f68,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f29,f65])).

fof(f29,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f63,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f27,f60])).

fof(f27,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

% (13941)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% (13930)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% (13930)Refutation not found, incomplete strategy% (13930)------------------------------
% (13930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (13930)Termination reason: Refutation not found, incomplete strategy

% (13930)Memory used [KB]: 6140
% (13930)Time elapsed: 0.106 s
% (13930)------------------------------
% (13930)------------------------------
% (13928)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
fof(f58,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f26,f55])).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:39:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (13925)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (13935)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.22/0.52  % (13927)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.22/0.52  % (13943)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.22/0.52  % (13947)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.22/0.52  % (13950)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.22/0.52  % (13931)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.22/0.52  % (13929)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.22/0.52  % (13927)Refutation found. Thanks to Tanya!
% 1.22/0.52  % SZS status Theorem for theBenchmark
% 1.22/0.52  % SZS output start Proof for theBenchmark
% 1.22/0.52  fof(f191,plain,(
% 1.22/0.52    $false),
% 1.22/0.52    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f95,f107,f116,f123,f131,f135,f140,f146,f164,f165,f178])).
% 1.22/0.52  fof(f178,plain,(
% 1.22/0.52    ~spl1_3 | ~spl1_4 | ~spl1_5 | spl1_8 | ~spl1_12),
% 1.22/0.52    inference(avatar_contradiction_clause,[],[f177])).
% 1.22/0.52  fof(f177,plain,(
% 1.22/0.52    $false | (~spl1_3 | ~spl1_4 | ~spl1_5 | spl1_8 | ~spl1_12)),
% 1.22/0.52    inference(subsumption_resolution,[],[f176,f130])).
% 1.22/0.52  fof(f130,plain,(
% 1.22/0.52    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl1_12),
% 1.22/0.52    inference(avatar_component_clause,[],[f129])).
% 1.22/0.52  fof(f129,plain,(
% 1.22/0.52    spl1_12 <=> ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 1.22/0.52  fof(f176,plain,(
% 1.22/0.52    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl1_3 | ~spl1_4 | ~spl1_5 | spl1_8)),
% 1.22/0.52    inference(forward_demodulation,[],[f175,f67])).
% 1.22/0.52  fof(f67,plain,(
% 1.22/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_3),
% 1.22/0.52    inference(avatar_component_clause,[],[f65])).
% 1.22/0.52  fof(f65,plain,(
% 1.22/0.52    spl1_3 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 1.22/0.52  fof(f175,plain,(
% 1.22/0.52    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl1_4 | ~spl1_5 | spl1_8)),
% 1.22/0.52    inference(forward_demodulation,[],[f170,f72])).
% 1.22/0.52  fof(f72,plain,(
% 1.22/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_4),
% 1.22/0.52    inference(avatar_component_clause,[],[f70])).
% 1.22/0.52  fof(f70,plain,(
% 1.22/0.52    spl1_4 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 1.22/0.52  fof(f170,plain,(
% 1.22/0.52    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) | (~spl1_5 | spl1_8)),
% 1.22/0.52    inference(backward_demodulation,[],[f102,f79])).
% 1.22/0.52  fof(f79,plain,(
% 1.22/0.52    k1_xboole_0 = sK0 | ~spl1_5),
% 1.22/0.52    inference(avatar_component_clause,[],[f77])).
% 1.22/0.52  fof(f77,plain,(
% 1.22/0.52    spl1_5 <=> k1_xboole_0 = sK0),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 1.22/0.52  fof(f102,plain,(
% 1.22/0.52    ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | spl1_8),
% 1.22/0.52    inference(avatar_component_clause,[],[f100])).
% 1.22/0.52  fof(f100,plain,(
% 1.22/0.52    spl1_8 <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 1.22/0.52  fof(f165,plain,(
% 1.22/0.52    ~spl1_16 | spl1_7 | spl1_8 | ~spl1_9),
% 1.22/0.52    inference(avatar_split_clause,[],[f152,f104,f100,f92,f161])).
% 1.22/0.52  fof(f161,plain,(
% 1.22/0.52    spl1_16 <=> k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).
% 1.22/0.52  fof(f92,plain,(
% 1.22/0.52    spl1_7 <=> k1_xboole_0 = k2_relat_1(sK0)),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 1.22/0.52  fof(f104,plain,(
% 1.22/0.52    spl1_9 <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 1.22/0.52  fof(f152,plain,(
% 1.22/0.52    k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | (spl1_7 | spl1_8 | ~spl1_9)),
% 1.22/0.52    inference(subsumption_resolution,[],[f151,f102])).
% 1.22/0.52  fof(f151,plain,(
% 1.22/0.52    k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | (spl1_7 | ~spl1_9)),
% 1.22/0.52    inference(subsumption_resolution,[],[f147,f94])).
% 1.22/0.52  fof(f94,plain,(
% 1.22/0.52    k1_xboole_0 != k2_relat_1(sK0) | spl1_7),
% 1.22/0.52    inference(avatar_component_clause,[],[f92])).
% 1.22/0.52  fof(f147,plain,(
% 1.22/0.52    k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | k1_xboole_0 = k2_relat_1(sK0) | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~spl1_9),
% 1.22/0.52    inference(resolution,[],[f105,f43])).
% 1.22/0.52  fof(f43,plain,(
% 1.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | v1_funct_2(X2,X0,X1)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f25])).
% 1.22/0.52  fof(f25,plain,(
% 1.22/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.22/0.52    inference(nnf_transformation,[],[f19])).
% 1.22/0.52  fof(f19,plain,(
% 1.22/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.22/0.52    inference(flattening,[],[f18])).
% 1.22/0.52  fof(f18,plain,(
% 1.22/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.22/0.52    inference(ennf_transformation,[],[f8])).
% 1.22/0.52  fof(f8,axiom,(
% 1.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.22/0.52  fof(f105,plain,(
% 1.22/0.52    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~spl1_9),
% 1.22/0.52    inference(avatar_component_clause,[],[f104])).
% 1.22/0.52  fof(f164,plain,(
% 1.22/0.52    spl1_16 | ~spl1_9),
% 1.22/0.52    inference(avatar_split_clause,[],[f149,f104,f161])).
% 1.22/0.52  fof(f149,plain,(
% 1.22/0.52    k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | ~spl1_9),
% 1.22/0.52    inference(resolution,[],[f105,f40])).
% 1.22/0.52  fof(f40,plain,(
% 1.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f17])).
% 1.22/0.52  fof(f17,plain,(
% 1.22/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.22/0.52    inference(ennf_transformation,[],[f6])).
% 1.22/0.52  fof(f6,axiom,(
% 1.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.22/0.52  fof(f146,plain,(
% 1.22/0.52    spl1_9 | ~spl1_14),
% 1.22/0.52    inference(avatar_split_clause,[],[f143,f138,f104])).
% 1.22/0.52  fof(f138,plain,(
% 1.22/0.52    spl1_14 <=> ! [X0] : (~r1_tarski(k1_relat_1(sK0),X0) | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK0)))))),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 1.22/0.52  fof(f143,plain,(
% 1.22/0.52    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~spl1_14),
% 1.22/0.52    inference(resolution,[],[f139,f47])).
% 1.22/0.52  fof(f47,plain,(
% 1.22/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.22/0.52    inference(equality_resolution,[],[f35])).
% 1.22/0.52  fof(f35,plain,(
% 1.22/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.22/0.52    inference(cnf_transformation,[],[f23])).
% 1.22/0.52  fof(f23,plain,(
% 1.22/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.22/0.52    inference(flattening,[],[f22])).
% 1.22/0.52  fof(f22,plain,(
% 1.22/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.22/0.52    inference(nnf_transformation,[],[f1])).
% 1.22/0.52  fof(f1,axiom,(
% 1.22/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.22/0.52  fof(f139,plain,(
% 1.22/0.52    ( ! [X0] : (~r1_tarski(k1_relat_1(sK0),X0) | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK0))))) ) | ~spl1_14),
% 1.22/0.52    inference(avatar_component_clause,[],[f138])).
% 1.22/0.52  fof(f140,plain,(
% 1.22/0.52    spl1_14 | ~spl1_13),
% 1.22/0.52    inference(avatar_split_clause,[],[f136,f133,f138])).
% 1.22/0.52  fof(f133,plain,(
% 1.22/0.52    spl1_13 <=> ! [X1,X0] : (~r1_tarski(k2_relat_1(sK0),X0) | ~r1_tarski(k1_relat_1(sK0),X1) | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 1.22/0.52  fof(f136,plain,(
% 1.22/0.52    ( ! [X0] : (~r1_tarski(k1_relat_1(sK0),X0) | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK0))))) ) | ~spl1_13),
% 1.22/0.52    inference(resolution,[],[f134,f47])).
% 1.22/0.52  fof(f134,plain,(
% 1.22/0.52    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK0),X0) | ~r1_tarski(k1_relat_1(sK0),X1) | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | ~spl1_13),
% 1.22/0.52    inference(avatar_component_clause,[],[f133])).
% 1.22/0.52  fof(f135,plain,(
% 1.22/0.52    spl1_13 | ~spl1_1),
% 1.22/0.52    inference(avatar_split_clause,[],[f108,f55,f133])).
% 1.22/0.52  fof(f55,plain,(
% 1.22/0.52    spl1_1 <=> v1_relat_1(sK0)),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 1.22/0.52  fof(f108,plain,(
% 1.22/0.52    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK0),X0) | ~r1_tarski(k1_relat_1(sK0),X1) | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | ~spl1_1),
% 1.22/0.52    inference(resolution,[],[f39,f57])).
% 1.22/0.52  fof(f57,plain,(
% 1.22/0.52    v1_relat_1(sK0) | ~spl1_1),
% 1.22/0.52    inference(avatar_component_clause,[],[f55])).
% 1.22/0.52  fof(f39,plain,(
% 1.22/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.22/0.52    inference(cnf_transformation,[],[f16])).
% 1.22/0.52  fof(f16,plain,(
% 1.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.22/0.52    inference(flattening,[],[f15])).
% 1.22/0.52  fof(f15,plain,(
% 1.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.22/0.52    inference(ennf_transformation,[],[f7])).
% 1.22/0.52  fof(f7,axiom,(
% 1.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 1.22/0.52  fof(f131,plain,(
% 1.22/0.52    spl1_12 | ~spl1_11),
% 1.22/0.52    inference(avatar_split_clause,[],[f126,f121,f129])).
% 1.22/0.52  fof(f121,plain,(
% 1.22/0.52    spl1_11 <=> ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))))),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 1.22/0.52  fof(f126,plain,(
% 1.22/0.52    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl1_11),
% 1.22/0.52    inference(subsumption_resolution,[],[f125,f31])).
% 1.22/0.52  fof(f31,plain,(
% 1.22/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f2])).
% 1.22/0.52  fof(f2,axiom,(
% 1.22/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.22/0.52  fof(f125,plain,(
% 1.22/0.52    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,X0))) ) | ~spl1_11),
% 1.22/0.52    inference(resolution,[],[f122,f38])).
% 1.22/0.52  fof(f38,plain,(
% 1.22/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f24])).
% 1.22/0.52  fof(f24,plain,(
% 1.22/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.22/0.52    inference(nnf_transformation,[],[f3])).
% 1.22/0.52  fof(f3,axiom,(
% 1.22/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.22/0.52  fof(f122,plain,(
% 1.22/0.52    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl1_11),
% 1.22/0.52    inference(avatar_component_clause,[],[f121])).
% 1.22/0.52  fof(f123,plain,(
% 1.22/0.52    spl1_11 | ~spl1_10),
% 1.22/0.52    inference(avatar_split_clause,[],[f118,f114,f121])).
% 1.22/0.52  fof(f114,plain,(
% 1.22/0.52    spl1_10 <=> ! [X1,X0] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 1.22/0.52  fof(f118,plain,(
% 1.22/0.52    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | ~spl1_10),
% 1.22/0.52    inference(trivial_inequality_removal,[],[f117])).
% 1.22/0.52  fof(f117,plain,(
% 1.22/0.52    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | ~spl1_10),
% 1.22/0.52    inference(superposition,[],[f52,f115])).
% 1.22/0.52  fof(f115,plain,(
% 1.22/0.52    ( ! [X0,X1] : (k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)) ) | ~spl1_10),
% 1.22/0.52    inference(avatar_component_clause,[],[f114])).
% 1.22/0.52  fof(f52,plain,(
% 1.22/0.52    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.22/0.52    inference(equality_resolution,[],[f44])).
% 1.22/0.52  fof(f44,plain,(
% 1.22/0.52    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.22/0.52    inference(cnf_transformation,[],[f25])).
% 1.22/0.52  fof(f116,plain,(
% 1.22/0.52    spl1_10 | ~spl1_3),
% 1.22/0.52    inference(avatar_split_clause,[],[f111,f65,f114])).
% 1.22/0.52  fof(f111,plain,(
% 1.22/0.52    ( ! [X0,X1] : (k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)) ) | ~spl1_3),
% 1.22/0.52    inference(forward_demodulation,[],[f109,f67])).
% 1.22/0.52  fof(f109,plain,(
% 1.22/0.52    ( ! [X0,X1] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)) )),
% 1.22/0.52    inference(resolution,[],[f90,f31])).
% 1.22/0.52  fof(f90,plain,(
% 1.22/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.22/0.52    inference(resolution,[],[f40,f38])).
% 1.22/0.52  fof(f107,plain,(
% 1.22/0.52    ~spl1_8 | ~spl1_9 | ~spl1_2),
% 1.22/0.52    inference(avatar_split_clause,[],[f98,f60,f104,f100])).
% 1.22/0.52  fof(f60,plain,(
% 1.22/0.52    spl1_2 <=> v1_funct_1(sK0)),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 1.22/0.52  % (13936)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.22/0.52  fof(f98,plain,(
% 1.22/0.52    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~spl1_2),
% 1.22/0.52    inference(subsumption_resolution,[],[f28,f62])).
% 1.22/0.52  fof(f62,plain,(
% 1.22/0.52    v1_funct_1(sK0) | ~spl1_2),
% 1.22/0.52    inference(avatar_component_clause,[],[f60])).
% 1.22/0.52  fof(f28,plain,(
% 1.22/0.52    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)),
% 1.22/0.52    inference(cnf_transformation,[],[f21])).
% 1.22/0.52  fof(f21,plain,(
% 1.22/0.52    (~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f20])).
% 1.22/0.52  fof(f20,plain,(
% 1.22/0.52    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.22/0.52    introduced(choice_axiom,[])).
% 1.22/0.52  fof(f12,plain,(
% 1.22/0.52    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.22/0.52    inference(flattening,[],[f11])).
% 1.22/0.52  fof(f11,plain,(
% 1.22/0.52    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.22/0.52    inference(ennf_transformation,[],[f10])).
% 1.22/0.52  fof(f10,negated_conjecture,(
% 1.22/0.52    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.22/0.52    inference(negated_conjecture,[],[f9])).
% 1.22/0.52  fof(f9,conjecture,(
% 1.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 1.22/0.52  fof(f95,plain,(
% 1.22/0.52    spl1_5 | ~spl1_7 | ~spl1_1),
% 1.22/0.52    inference(avatar_split_clause,[],[f85,f55,f92,f77])).
% 1.22/0.52  fof(f85,plain,(
% 1.22/0.52    k1_xboole_0 != k2_relat_1(sK0) | k1_xboole_0 = sK0 | ~spl1_1),
% 1.22/0.52    inference(resolution,[],[f33,f57])).
% 1.22/0.52  fof(f33,plain,(
% 1.22/0.52    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.22/0.52    inference(cnf_transformation,[],[f14])).
% 1.22/0.52  fof(f14,plain,(
% 1.22/0.52    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.22/0.52    inference(flattening,[],[f13])).
% 1.22/0.52  fof(f13,plain,(
% 1.22/0.52    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.22/0.52    inference(ennf_transformation,[],[f5])).
% 1.22/0.52  fof(f5,axiom,(
% 1.22/0.52    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.22/0.52  fof(f73,plain,(
% 1.22/0.52    spl1_4),
% 1.22/0.52    inference(avatar_split_clause,[],[f30,f70])).
% 1.22/0.52  fof(f30,plain,(
% 1.22/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.22/0.52    inference(cnf_transformation,[],[f4])).
% 1.22/0.52  fof(f4,axiom,(
% 1.22/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.22/0.52  fof(f68,plain,(
% 1.22/0.52    spl1_3),
% 1.22/0.52    inference(avatar_split_clause,[],[f29,f65])).
% 1.22/0.52  fof(f29,plain,(
% 1.22/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.22/0.52    inference(cnf_transformation,[],[f4])).
% 1.22/0.52  fof(f63,plain,(
% 1.22/0.52    spl1_2),
% 1.22/0.52    inference(avatar_split_clause,[],[f27,f60])).
% 1.22/0.52  fof(f27,plain,(
% 1.22/0.52    v1_funct_1(sK0)),
% 1.22/0.52    inference(cnf_transformation,[],[f21])).
% 1.22/0.52  % (13941)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.22/0.53  % (13930)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.22/0.53  % (13930)Refutation not found, incomplete strategy% (13930)------------------------------
% 1.22/0.53  % (13930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (13930)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.53  
% 1.22/0.53  % (13930)Memory used [KB]: 6140
% 1.22/0.53  % (13930)Time elapsed: 0.106 s
% 1.22/0.53  % (13930)------------------------------
% 1.22/0.53  % (13930)------------------------------
% 1.22/0.53  % (13928)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.22/0.53  fof(f58,plain,(
% 1.22/0.53    spl1_1),
% 1.22/0.53    inference(avatar_split_clause,[],[f26,f55])).
% 1.22/0.53  fof(f26,plain,(
% 1.22/0.53    v1_relat_1(sK0)),
% 1.22/0.53    inference(cnf_transformation,[],[f21])).
% 1.22/0.53  % SZS output end Proof for theBenchmark
% 1.22/0.53  % (13927)------------------------------
% 1.22/0.53  % (13927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (13927)Termination reason: Refutation
% 1.22/0.53  
% 1.22/0.53  % (13927)Memory used [KB]: 6268
% 1.22/0.53  % (13927)Time elapsed: 0.102 s
% 1.22/0.53  % (13927)------------------------------
% 1.22/0.53  % (13927)------------------------------
% 1.22/0.53  % (13924)Success in time 0.164 s
%------------------------------------------------------------------------------
