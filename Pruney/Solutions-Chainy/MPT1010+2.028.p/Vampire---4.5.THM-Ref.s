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
% DateTime   : Thu Dec  3 13:04:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 153 expanded)
%              Number of leaves         :   23 (  52 expanded)
%              Depth                    :   16
%              Number of atoms          :  348 ( 573 expanded)
%              Number of equality atoms :   90 ( 147 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f441,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f105,f110,f115,f120,f148,f201,f238,f244,f245,f440])).

fof(f440,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(avatar_contradiction_clause,[],[f439])).

fof(f439,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f438,f153])).

fof(f153,plain,
    ( v5_relat_1(sK3,k1_tarski(sK1))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl6_10
  <=> v5_relat_1(sK3,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f438,plain,
    ( ~ v5_relat_1(sK3,k1_tarski(sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_13 ),
    inference(equality_resolution,[],[f437])).

fof(f437,plain,
    ( ! [X0] :
        ( sK1 != X0
        | ~ v5_relat_1(sK3,k1_tarski(X0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f436,f104])).

fof(f104,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl6_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f436,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2,sK0)
        | sK1 != X0
        | ~ v5_relat_1(sK3,k1_tarski(X0)) )
    | spl6_1
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_13 ),
    inference(forward_demodulation,[],[f435,f198])).

fof(f198,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl6_13
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f435,plain,
    ( ! [X0] :
        ( sK1 != X0
        | ~ v5_relat_1(sK3,k1_tarski(X0))
        | ~ r2_hidden(sK2,k1_relat_1(sK3)) )
    | spl6_1
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f434,f119])).

fof(f119,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl6_5
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f434,plain,
    ( ! [X0] :
        ( sK1 != X0
        | ~ v5_relat_1(sK3,k1_tarski(X0))
        | ~ r2_hidden(sK2,k1_relat_1(sK3))
        | ~ v1_funct_1(sK3) )
    | spl6_1
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f422,f147])).

fof(f147,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl6_9
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f422,plain,
    ( ! [X0] :
        ( sK1 != X0
        | ~ v5_relat_1(sK3,k1_tarski(X0))
        | ~ v1_relat_1(sK3)
        | ~ r2_hidden(sK2,k1_relat_1(sK3))
        | ~ v1_funct_1(sK3) )
    | spl6_1 ),
    inference(superposition,[],[f99,f295])).

fof(f295,plain,(
    ! [X4,X5,X3] :
      ( k1_funct_1(X3,X5) = X4
      | ~ v5_relat_1(X3,k1_tarski(X4))
      | ~ v1_relat_1(X3)
      | ~ r2_hidden(X5,k1_relat_1(X3))
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f292,f77])).

fof(f77,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f292,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_1(X3)
      | ~ v5_relat_1(X3,k1_tarski(X4))
      | ~ v1_relat_1(X3)
      | v1_xboole_0(k1_tarski(X4))
      | ~ r2_hidden(X5,k1_relat_1(X3))
      | k1_funct_1(X3,X5) = X4 ) ),
    inference(resolution,[],[f166,f95])).

fof(f95,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),X2)
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X2)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X2)
      | ~ r2_hidden(X0,k1_relat_1(X1)) ) ),
    inference(resolution,[],[f72,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

fof(f99,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl6_1
  <=> sK1 = k1_funct_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f245,plain,
    ( spl6_10
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f240,f107,f151])).

fof(f107,plain,
    ( spl6_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f240,plain,
    ( v5_relat_1(sK3,k1_tarski(sK1))
    | ~ spl6_3 ),
    inference(resolution,[],[f109,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f109,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f244,plain,
    ( spl6_11
    | spl6_12
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f243,f112,f107,f184,f180])).

fof(f180,plain,
    ( spl6_11
  <=> sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f184,plain,
    ( spl6_12
  <=> k1_xboole_0 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f112,plain,
    ( spl6_4
  <=> v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f243,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f239,f114])).

fof(f114,plain,
    ( v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f239,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | k1_xboole_0 = k1_tarski(sK1)
    | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)
    | ~ spl6_3 ),
    inference(resolution,[],[f109,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f238,plain,(
    ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f214,f78])).

fof(f78,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f214,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | ~ spl6_12 ),
    inference(superposition,[],[f122,f186])).

fof(f186,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f184])).

fof(f122,plain,(
    ! [X0] : ~ r1_tarski(k1_tarski(X0),X0) ),
    inference(resolution,[],[f73,f94])).

fof(f94,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f201,plain,
    ( spl6_13
    | ~ spl6_3
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f200,f180,f107,f196])).

fof(f200,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_3
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f192,f109])).

fof(f192,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl6_11 ),
    inference(superposition,[],[f64,f182])).

fof(f182,plain,
    ( sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f180])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f148,plain,
    ( spl6_9
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f143,f107,f145])).

fof(f143,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_3 ),
    inference(resolution,[],[f75,f109])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f120,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f43,f117])).

fof(f43,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( sK1 != k1_funct_1(sK3,sK2)
      & r2_hidden(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_2(sK3,sK0,k1_tarski(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

fof(f115,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f44,f112])).

fof(f44,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f110,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f45,f107])).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f105,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f46,f102])).

fof(f46,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f100,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f47,f97])).

fof(f47,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:57:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (16269)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (16277)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (16272)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (16290)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.53  % (16287)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (16274)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (16275)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (16271)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (16292)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (16280)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (16284)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (16296)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (16290)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (16297)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (16287)Refutation not found, incomplete strategy% (16287)------------------------------
% 0.22/0.54  % (16287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (16288)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (16276)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (16287)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (16287)Memory used [KB]: 1791
% 0.22/0.55  % (16287)Time elapsed: 0.130 s
% 0.22/0.55  % (16287)------------------------------
% 0.22/0.55  % (16287)------------------------------
% 0.22/0.55  % (16286)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (16270)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.55  % (16270)Refutation not found, incomplete strategy% (16270)------------------------------
% 0.22/0.55  % (16270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (16270)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (16270)Memory used [KB]: 1663
% 0.22/0.55  % (16270)Time elapsed: 0.134 s
% 0.22/0.55  % (16270)------------------------------
% 0.22/0.55  % (16270)------------------------------
% 0.22/0.55  % (16289)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (16294)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (16279)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.56  % (16298)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.56  % (16298)Refutation not found, incomplete strategy% (16298)------------------------------
% 0.22/0.56  % (16298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (16298)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (16298)Memory used [KB]: 1663
% 0.22/0.56  % (16298)Time elapsed: 0.116 s
% 0.22/0.56  % (16298)------------------------------
% 0.22/0.56  % (16298)------------------------------
% 0.22/0.56  % (16273)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f441,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f100,f105,f110,f115,f120,f148,f201,f238,f244,f245,f440])).
% 0.22/0.56  fof(f440,plain,(
% 0.22/0.56    spl6_1 | ~spl6_2 | ~spl6_5 | ~spl6_9 | ~spl6_10 | ~spl6_13),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f439])).
% 0.22/0.56  fof(f439,plain,(
% 0.22/0.56    $false | (spl6_1 | ~spl6_2 | ~spl6_5 | ~spl6_9 | ~spl6_10 | ~spl6_13)),
% 0.22/0.56    inference(subsumption_resolution,[],[f438,f153])).
% 0.22/0.56  fof(f153,plain,(
% 0.22/0.56    v5_relat_1(sK3,k1_tarski(sK1)) | ~spl6_10),
% 0.22/0.56    inference(avatar_component_clause,[],[f151])).
% 0.22/0.56  fof(f151,plain,(
% 0.22/0.56    spl6_10 <=> v5_relat_1(sK3,k1_tarski(sK1))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.56  fof(f438,plain,(
% 0.22/0.56    ~v5_relat_1(sK3,k1_tarski(sK1)) | (spl6_1 | ~spl6_2 | ~spl6_5 | ~spl6_9 | ~spl6_13)),
% 0.22/0.56    inference(equality_resolution,[],[f437])).
% 0.22/0.56  fof(f437,plain,(
% 0.22/0.56    ( ! [X0] : (sK1 != X0 | ~v5_relat_1(sK3,k1_tarski(X0))) ) | (spl6_1 | ~spl6_2 | ~spl6_5 | ~spl6_9 | ~spl6_13)),
% 0.22/0.56    inference(subsumption_resolution,[],[f436,f104])).
% 0.22/0.56  fof(f104,plain,(
% 0.22/0.56    r2_hidden(sK2,sK0) | ~spl6_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f102])).
% 0.22/0.56  fof(f102,plain,(
% 0.22/0.56    spl6_2 <=> r2_hidden(sK2,sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.56  fof(f436,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(sK2,sK0) | sK1 != X0 | ~v5_relat_1(sK3,k1_tarski(X0))) ) | (spl6_1 | ~spl6_5 | ~spl6_9 | ~spl6_13)),
% 0.22/0.56    inference(forward_demodulation,[],[f435,f198])).
% 0.22/0.56  fof(f198,plain,(
% 0.22/0.56    sK0 = k1_relat_1(sK3) | ~spl6_13),
% 0.22/0.56    inference(avatar_component_clause,[],[f196])).
% 0.22/0.56  fof(f196,plain,(
% 0.22/0.56    spl6_13 <=> sK0 = k1_relat_1(sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.56  fof(f435,plain,(
% 0.22/0.56    ( ! [X0] : (sK1 != X0 | ~v5_relat_1(sK3,k1_tarski(X0)) | ~r2_hidden(sK2,k1_relat_1(sK3))) ) | (spl6_1 | ~spl6_5 | ~spl6_9)),
% 0.22/0.56    inference(subsumption_resolution,[],[f434,f119])).
% 0.22/0.56  fof(f119,plain,(
% 0.22/0.56    v1_funct_1(sK3) | ~spl6_5),
% 0.22/0.56    inference(avatar_component_clause,[],[f117])).
% 0.22/0.56  fof(f117,plain,(
% 0.22/0.56    spl6_5 <=> v1_funct_1(sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.56  fof(f434,plain,(
% 0.22/0.56    ( ! [X0] : (sK1 != X0 | ~v5_relat_1(sK3,k1_tarski(X0)) | ~r2_hidden(sK2,k1_relat_1(sK3)) | ~v1_funct_1(sK3)) ) | (spl6_1 | ~spl6_9)),
% 0.22/0.56    inference(subsumption_resolution,[],[f422,f147])).
% 0.22/0.56  fof(f147,plain,(
% 0.22/0.56    v1_relat_1(sK3) | ~spl6_9),
% 0.22/0.56    inference(avatar_component_clause,[],[f145])).
% 0.22/0.56  fof(f145,plain,(
% 0.22/0.56    spl6_9 <=> v1_relat_1(sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.56  fof(f422,plain,(
% 0.22/0.56    ( ! [X0] : (sK1 != X0 | ~v5_relat_1(sK3,k1_tarski(X0)) | ~v1_relat_1(sK3) | ~r2_hidden(sK2,k1_relat_1(sK3)) | ~v1_funct_1(sK3)) ) | spl6_1),
% 0.22/0.56    inference(superposition,[],[f99,f295])).
% 0.22/0.56  fof(f295,plain,(
% 0.22/0.56    ( ! [X4,X5,X3] : (k1_funct_1(X3,X5) = X4 | ~v5_relat_1(X3,k1_tarski(X4)) | ~v1_relat_1(X3) | ~r2_hidden(X5,k1_relat_1(X3)) | ~v1_funct_1(X3)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f292,f77])).
% 0.22/0.56  fof(f77,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.22/0.56  fof(f292,plain,(
% 0.22/0.56    ( ! [X4,X5,X3] : (~v1_funct_1(X3) | ~v5_relat_1(X3,k1_tarski(X4)) | ~v1_relat_1(X3) | v1_xboole_0(k1_tarski(X4)) | ~r2_hidden(X5,k1_relat_1(X3)) | k1_funct_1(X3,X5) = X4) )),
% 0.22/0.56    inference(resolution,[],[f166,f95])).
% 0.22/0.56  fof(f95,plain,(
% 0.22/0.56    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.22/0.56    inference(equality_resolution,[],[f66])).
% 0.22/0.56  fof(f66,plain,(
% 0.22/0.56    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.56    inference(rectify,[],[f39])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.56    inference(nnf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.56  fof(f166,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X0),X2) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X2) | ~v1_relat_1(X1) | v1_xboole_0(X2) | ~r2_hidden(X0,k1_relat_1(X1))) )),
% 0.22/0.56    inference(resolution,[],[f72,f74])).
% 0.22/0.56  fof(f74,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.56    inference(flattening,[],[f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.56  fof(f72,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2))),
% 0.22/0.56    inference(flattening,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2))) | (~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)))),
% 0.22/0.56    inference(ennf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).
% 0.22/0.56  fof(f99,plain,(
% 0.22/0.56    sK1 != k1_funct_1(sK3,sK2) | spl6_1),
% 0.22/0.56    inference(avatar_component_clause,[],[f97])).
% 0.22/0.56  fof(f97,plain,(
% 0.22/0.56    spl6_1 <=> sK1 = k1_funct_1(sK3,sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.56  fof(f245,plain,(
% 0.22/0.56    spl6_10 | ~spl6_3),
% 0.22/0.56    inference(avatar_split_clause,[],[f240,f107,f151])).
% 0.22/0.56  fof(f107,plain,(
% 0.22/0.56    spl6_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.56  fof(f240,plain,(
% 0.22/0.56    v5_relat_1(sK3,k1_tarski(sK1)) | ~spl6_3),
% 0.22/0.56    inference(resolution,[],[f109,f76])).
% 0.22/0.56  fof(f76,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.22/0.56    inference(pure_predicate_removal,[],[f12])).
% 0.22/0.56  fof(f12,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.56  fof(f109,plain,(
% 0.22/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~spl6_3),
% 0.22/0.56    inference(avatar_component_clause,[],[f107])).
% 0.22/0.56  fof(f244,plain,(
% 0.22/0.56    spl6_11 | spl6_12 | ~spl6_3 | ~spl6_4),
% 0.22/0.56    inference(avatar_split_clause,[],[f243,f112,f107,f184,f180])).
% 0.22/0.56  fof(f180,plain,(
% 0.22/0.56    spl6_11 <=> sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.56  fof(f184,plain,(
% 0.22/0.56    spl6_12 <=> k1_xboole_0 = k1_tarski(sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.56  fof(f112,plain,(
% 0.22/0.56    spl6_4 <=> v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.56  fof(f243,plain,(
% 0.22/0.56    k1_xboole_0 = k1_tarski(sK1) | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) | (~spl6_3 | ~spl6_4)),
% 0.22/0.56    inference(subsumption_resolution,[],[f239,f114])).
% 0.22/0.56  fof(f114,plain,(
% 0.22/0.56    v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~spl6_4),
% 0.22/0.56    inference(avatar_component_clause,[],[f112])).
% 0.22/0.56  fof(f239,plain,(
% 0.22/0.56    ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | k1_xboole_0 = k1_tarski(sK1) | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) | ~spl6_3),
% 0.22/0.56    inference(resolution,[],[f109,f58])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f38])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(nnf_transformation,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(flattening,[],[f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.56  fof(f238,plain,(
% 0.22/0.56    ~spl6_12),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f237])).
% 0.22/0.56  fof(f237,plain,(
% 0.22/0.56    $false | ~spl6_12),
% 0.22/0.56    inference(subsumption_resolution,[],[f214,f78])).
% 0.22/0.56  fof(f78,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.56  fof(f214,plain,(
% 0.22/0.56    ~r1_tarski(k1_xboole_0,sK1) | ~spl6_12),
% 0.22/0.56    inference(superposition,[],[f122,f186])).
% 0.22/0.56  fof(f186,plain,(
% 0.22/0.56    k1_xboole_0 = k1_tarski(sK1) | ~spl6_12),
% 0.22/0.56    inference(avatar_component_clause,[],[f184])).
% 0.22/0.56  fof(f122,plain,(
% 0.22/0.56    ( ! [X0] : (~r1_tarski(k1_tarski(X0),X0)) )),
% 0.22/0.56    inference(resolution,[],[f73,f94])).
% 0.22/0.56  fof(f94,plain,(
% 0.22/0.56    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.22/0.56    inference(equality_resolution,[],[f93])).
% 0.22/0.56  fof(f93,plain,(
% 0.22/0.56    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.22/0.56    inference(equality_resolution,[],[f67])).
% 0.22/0.56  fof(f67,plain,(
% 0.22/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f73,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.56  fof(f201,plain,(
% 0.22/0.56    spl6_13 | ~spl6_3 | ~spl6_11),
% 0.22/0.56    inference(avatar_split_clause,[],[f200,f180,f107,f196])).
% 0.22/0.56  fof(f200,plain,(
% 0.22/0.56    sK0 = k1_relat_1(sK3) | (~spl6_3 | ~spl6_11)),
% 0.22/0.56    inference(subsumption_resolution,[],[f192,f109])).
% 0.22/0.56  fof(f192,plain,(
% 0.22/0.56    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~spl6_11),
% 0.22/0.56    inference(superposition,[],[f64,f182])).
% 0.22/0.56  fof(f182,plain,(
% 0.22/0.56    sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) | ~spl6_11),
% 0.22/0.56    inference(avatar_component_clause,[],[f180])).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.56  fof(f148,plain,(
% 0.22/0.56    spl6_9 | ~spl6_3),
% 0.22/0.56    inference(avatar_split_clause,[],[f143,f107,f145])).
% 0.22/0.56  fof(f143,plain,(
% 0.22/0.56    v1_relat_1(sK3) | ~spl6_3),
% 0.22/0.56    inference(resolution,[],[f75,f109])).
% 0.22/0.56  fof(f75,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.56  fof(f120,plain,(
% 0.22/0.56    spl6_5),
% 0.22/0.56    inference(avatar_split_clause,[],[f43,f117])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    v1_funct_1(sK3)),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3)),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 0.22/0.56    inference(flattening,[],[f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 0.22/0.56    inference(ennf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.22/0.56    inference(negated_conjecture,[],[f15])).
% 0.22/0.56  fof(f15,conjecture,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).
% 0.22/0.56  fof(f115,plain,(
% 0.22/0.56    spl6_4),
% 0.22/0.56    inference(avatar_split_clause,[],[f44,f112])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  fof(f110,plain,(
% 0.22/0.56    spl6_3),
% 0.22/0.56    inference(avatar_split_clause,[],[f45,f107])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  fof(f105,plain,(
% 0.22/0.56    spl6_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f46,f102])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    r2_hidden(sK2,sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  fof(f100,plain,(
% 0.22/0.56    ~spl6_1),
% 0.22/0.56    inference(avatar_split_clause,[],[f47,f97])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    sK1 != k1_funct_1(sK3,sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (16290)------------------------------
% 0.22/0.56  % (16290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (16290)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (16290)Memory used [KB]: 6524
% 0.22/0.56  % (16290)Time elapsed: 0.125 s
% 0.22/0.56  % (16290)------------------------------
% 0.22/0.56  % (16290)------------------------------
% 0.22/0.56  % (16282)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (16268)Success in time 0.194 s
%------------------------------------------------------------------------------
