%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 252 expanded)
%              Number of leaves         :   31 ( 103 expanded)
%              Depth                    :   12
%              Number of atoms          :  447 ( 845 expanded)
%              Number of equality atoms :  126 ( 231 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f788,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f107,f108,f113,f143,f145,f179,f185,f212,f222,f227,f229,f372,f408,f593,f598,f673,f716,f722,f787])).

fof(f787,plain,
    ( ~ spl3_36
    | ~ spl3_51
    | spl3_52 ),
    inference(avatar_contradiction_clause,[],[f786])).

fof(f786,plain,
    ( $false
    | ~ spl3_36
    | ~ spl3_51
    | spl3_52 ),
    inference(subsumption_resolution,[],[f785,f407])).

fof(f407,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f405])).

fof(f405,plain,
    ( spl3_36
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f785,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_51
    | spl3_52 ),
    inference(forward_demodulation,[],[f784,f77])).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f784,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_51
    | spl3_52 ),
    inference(subsumption_resolution,[],[f780,f721])).

fof(f721,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl3_52 ),
    inference(avatar_component_clause,[],[f719])).

fof(f719,plain,
    ( spl3_52
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f780,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_51 ),
    inference(trivial_inequality_removal,[],[f779])).

fof(f779,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_51 ),
    inference(superposition,[],[f82,f683])).

fof(f683,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f681])).

fof(f681,plain,
    ( spl3_51
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f82,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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

fof(f722,plain,
    ( ~ spl3_52
    | spl3_19
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f717,f250,f219,f719])).

fof(f219,plain,
    ( spl3_19
  <=> v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f250,plain,
    ( spl3_22
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f717,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl3_19
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f707,f66])).

fof(f66,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f707,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | spl3_19
    | ~ spl3_22 ),
    inference(backward_demodulation,[],[f221,f252])).

fof(f252,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f250])).

fof(f221,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)
    | spl3_19 ),
    inference(avatar_component_clause,[],[f219])).

fof(f716,plain,
    ( spl3_51
    | ~ spl3_14
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f715,f250,f188,f681])).

fof(f188,plain,
    ( spl3_14
  <=> k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f715,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_14
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f705,f66])).

fof(f705,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relset_1(k1_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ spl3_14
    | ~ spl3_22 ),
    inference(backward_demodulation,[],[f190,f252])).

fof(f190,plain,
    ( k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),k1_xboole_0,sK1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f188])).

fof(f673,plain,
    ( spl3_22
    | ~ spl3_5
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f672,f287,f110,f250])).

fof(f110,plain,
    ( spl3_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f287,plain,
    ( spl3_27
  <=> k1_xboole_0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f672,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_5
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f670,f112])).

fof(f112,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f110])).

fof(f670,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_relat_1(sK1)
    | ~ spl3_27 ),
    inference(trivial_inequality_removal,[],[f667])).

fof(f667,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | ~ v1_relat_1(sK1)
    | ~ spl3_27 ),
    inference(superposition,[],[f65,f289])).

fof(f289,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f287])).

fof(f65,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f598,plain,
    ( spl3_27
    | ~ spl3_18
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f443,f224,f214,f287])).

fof(f214,plain,
    ( spl3_18
  <=> r1_tarski(k1_xboole_0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f224,plain,
    ( spl3_20
  <=> r1_tarski(k2_relat_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f443,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK1))
    | k1_xboole_0 = k2_relat_1(sK1)
    | ~ spl3_20 ),
    inference(resolution,[],[f226,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f226,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_xboole_0)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f224])).

fof(f593,plain,
    ( spl3_18
    | spl3_27
    | ~ spl3_34 ),
    inference(avatar_contradiction_clause,[],[f592])).

fof(f592,plain,
    ( $false
    | spl3_18
    | spl3_27
    | ~ spl3_34 ),
    inference(subsumption_resolution,[],[f591,f216])).

fof(f216,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK1))
    | spl3_18 ),
    inference(avatar_component_clause,[],[f214])).

fof(f591,plain,
    ( r1_tarski(k1_xboole_0,k2_relat_1(sK1))
    | spl3_27
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f590,f67])).

fof(f67,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f590,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),k2_relat_1(sK1))
    | spl3_27
    | ~ spl3_34 ),
    inference(subsumption_resolution,[],[f572,f288])).

fof(f288,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | spl3_27 ),
    inference(avatar_component_clause,[],[f287])).

fof(f572,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),k2_relat_1(sK1))
    | k1_xboole_0 = k2_relat_1(sK1)
    | ~ spl3_34 ),
    inference(superposition,[],[f74,f371])).

fof(f371,plain,
    ( k1_xboole_0 = sK2(k2_relat_1(sK1),k1_xboole_0)
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f369])).

fof(f369,plain,
    ( spl3_34
  <=> k1_xboole_0 = sK2(k2_relat_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(sK2(X0,X1)),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k2_relat_1(sK2(X0,X1)),X0)
        & k1_relat_1(sK2(X0,X1)) = X1
        & v1_funct_1(sK2(X0,X1))
        & v1_relat_1(sK2(X0,X1)) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( r1_tarski(k2_relat_1(sK2(X0,X1)),X0)
        & k1_relat_1(sK2(X0,X1)) = X1
        & v1_funct_1(sK2(X0,X1))
        & v1_relat_1(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f408,plain,
    ( spl3_36
    | ~ spl3_17
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f394,f287,f209,f405])).

fof(f209,plain,
    ( spl3_17
  <=> m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f394,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_17
    | ~ spl3_27 ),
    inference(backward_demodulation,[],[f211,f289])).

fof(f211,plain,
    ( m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f209])).

fof(f372,plain,
    ( spl3_34
    | spl3_27 ),
    inference(avatar_split_clause,[],[f367,f287,f369])).

fof(f367,plain,
    ( k1_xboole_0 = sK2(k2_relat_1(sK1),k1_xboole_0)
    | spl3_27 ),
    inference(unit_resulting_resolution,[],[f87,f302,f64])).

fof(f64,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f302,plain,
    ( ! [X0] : v1_relat_1(sK2(k2_relat_1(sK1),X0))
    | spl3_27 ),
    inference(unit_resulting_resolution,[],[f288,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k1_relat_1(sK2(X0,k1_xboole_0)) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X1
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f229,plain,
    ( spl3_14
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f228,f182,f175,f188])).

fof(f175,plain,
    ( spl3_12
  <=> k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f182,plain,
    ( spl3_13
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f228,plain,
    ( k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),k1_xboole_0,sK1)
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f177,f184])).

fof(f184,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f182])).

fof(f177,plain,
    ( k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f175])).

fof(f227,plain,
    ( spl3_20
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f196,f182,f104,f224])).

fof(f104,plain,
    ( spl3_4
  <=> r1_tarski(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f196,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f106,f184])).

fof(f106,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f222,plain,
    ( ~ spl3_19
    | spl3_2
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f195,f182,f95,f219])).

fof(f95,plain,
    ( spl3_2
  <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f195,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)
    | spl3_2
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f97,f184])).

fof(f97,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f212,plain,
    ( spl3_17
    | ~ spl3_7
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f193,f182,f140,f209])).

fof(f140,plain,
    ( spl3_7
  <=> m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f193,plain,
    ( m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_7
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f142,f184])).

fof(f142,plain,
    ( m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(sK0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f140])).

fof(f185,plain,
    ( spl3_13
    | ~ spl3_12
    | spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f180,f99,f95,f175,f182])).

fof(f99,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f180,plain,
    ( k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | k1_xboole_0 = sK0
    | spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f167,f97])).

fof(f167,plain,
    ( k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | k1_xboole_0 = sK0
    | v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f100,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f100,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f179,plain,
    ( spl3_12
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f165,f99,f175])).

fof(f165,plain,
    ( k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f100,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f145,plain,
    ( spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f134,f110,f104,f99])).

% (17927)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f134,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f112,f85,f106,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f85,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f143,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f136,f104,f140])).

fof(f136,plain,
    ( m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f106,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f113,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f41,f110])).

fof(f41,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
      | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
      | ~ v1_funct_1(sK1) )
    & r1_tarski(k2_relat_1(sK1),sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
        | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
        | ~ v1_funct_1(sK1) )
      & r1_tarski(k2_relat_1(sK1),sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f108,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f42,f91])).

fof(f91,plain,
    ( spl3_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f42,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f107,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f43,f104])).

fof(f43,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f102,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f44,f99,f95,f91])).

fof(f44,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:25:10 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.49  % (17925)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (17926)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (17923)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (17926)Refutation not found, incomplete strategy% (17926)------------------------------
% 0.20/0.50  % (17926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (17926)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (17926)Memory used [KB]: 6140
% 0.20/0.50  % (17926)Time elapsed: 0.085 s
% 0.20/0.50  % (17926)------------------------------
% 0.20/0.50  % (17926)------------------------------
% 0.20/0.51  % (17939)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (17940)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.51  % (17934)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (17941)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.52  % (17942)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.52  % (17932)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.52  % (17924)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.52  % (17933)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.52  % (17931)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.52  % (17929)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.52  % (17934)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (17943)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f788,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f102,f107,f108,f113,f143,f145,f179,f185,f212,f222,f227,f229,f372,f408,f593,f598,f673,f716,f722,f787])).
% 0.20/0.53  fof(f787,plain,(
% 0.20/0.53    ~spl3_36 | ~spl3_51 | spl3_52),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f786])).
% 0.20/0.53  fof(f786,plain,(
% 0.20/0.53    $false | (~spl3_36 | ~spl3_51 | spl3_52)),
% 0.20/0.53    inference(subsumption_resolution,[],[f785,f407])).
% 0.20/0.53  fof(f407,plain,(
% 0.20/0.53    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl3_36),
% 0.20/0.53    inference(avatar_component_clause,[],[f405])).
% 0.20/0.53  fof(f405,plain,(
% 0.20/0.53    spl3_36 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.20/0.53  fof(f785,plain,(
% 0.20/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl3_51 | spl3_52)),
% 0.20/0.53    inference(forward_demodulation,[],[f784,f77])).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.53    inference(equality_resolution,[],[f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.20/0.53    inference(flattening,[],[f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.20/0.53    inference(nnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.53  fof(f784,plain,(
% 0.20/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_51 | spl3_52)),
% 0.20/0.53    inference(subsumption_resolution,[],[f780,f721])).
% 0.20/0.53  fof(f721,plain,(
% 0.20/0.53    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | spl3_52),
% 0.20/0.53    inference(avatar_component_clause,[],[f719])).
% 0.20/0.53  fof(f719,plain,(
% 0.20/0.53    spl3_52 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 0.20/0.53  fof(f780,plain,(
% 0.20/0.53    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl3_51),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f779])).
% 0.20/0.53  fof(f779,plain,(
% 0.20/0.53    k1_xboole_0 != k1_xboole_0 | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl3_51),
% 0.20/0.53    inference(superposition,[],[f82,f683])).
% 0.20/0.53  fof(f683,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl3_51),
% 0.20/0.53    inference(avatar_component_clause,[],[f681])).
% 0.20/0.53  fof(f681,plain,(
% 0.20/0.53    spl3_51 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.20/0.53    inference(equality_resolution,[],[f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(nnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(flattening,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.53  fof(f722,plain,(
% 0.20/0.53    ~spl3_52 | spl3_19 | ~spl3_22),
% 0.20/0.53    inference(avatar_split_clause,[],[f717,f250,f219,f719])).
% 0.20/0.53  fof(f219,plain,(
% 0.20/0.53    spl3_19 <=> v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.53  fof(f250,plain,(
% 0.20/0.53    spl3_22 <=> k1_xboole_0 = sK1),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.53  fof(f717,plain,(
% 0.20/0.53    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl3_19 | ~spl3_22)),
% 0.20/0.53    inference(forward_demodulation,[],[f707,f66])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.53    inference(cnf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.53  fof(f707,plain,(
% 0.20/0.53    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (spl3_19 | ~spl3_22)),
% 0.20/0.53    inference(backward_demodulation,[],[f221,f252])).
% 0.20/0.53  fof(f252,plain,(
% 0.20/0.53    k1_xboole_0 = sK1 | ~spl3_22),
% 0.20/0.53    inference(avatar_component_clause,[],[f250])).
% 0.20/0.53  fof(f221,plain,(
% 0.20/0.53    ~v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) | spl3_19),
% 0.20/0.53    inference(avatar_component_clause,[],[f219])).
% 0.20/0.53  fof(f716,plain,(
% 0.20/0.53    spl3_51 | ~spl3_14 | ~spl3_22),
% 0.20/0.53    inference(avatar_split_clause,[],[f715,f250,f188,f681])).
% 0.20/0.53  fof(f188,plain,(
% 0.20/0.53    spl3_14 <=> k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),k1_xboole_0,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.53  fof(f715,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl3_14 | ~spl3_22)),
% 0.20/0.53    inference(forward_demodulation,[],[f705,f66])).
% 0.20/0.53  fof(f705,plain,(
% 0.20/0.53    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | (~spl3_14 | ~spl3_22)),
% 0.20/0.53    inference(backward_demodulation,[],[f190,f252])).
% 0.20/0.53  fof(f190,plain,(
% 0.20/0.53    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),k1_xboole_0,sK1) | ~spl3_14),
% 0.20/0.53    inference(avatar_component_clause,[],[f188])).
% 0.20/0.53  fof(f673,plain,(
% 0.20/0.53    spl3_22 | ~spl3_5 | ~spl3_27),
% 0.20/0.53    inference(avatar_split_clause,[],[f672,f287,f110,f250])).
% 0.20/0.53  fof(f110,plain,(
% 0.20/0.53    spl3_5 <=> v1_relat_1(sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.53  fof(f287,plain,(
% 0.20/0.53    spl3_27 <=> k1_xboole_0 = k2_relat_1(sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.53  fof(f672,plain,(
% 0.20/0.53    k1_xboole_0 = sK1 | (~spl3_5 | ~spl3_27)),
% 0.20/0.53    inference(subsumption_resolution,[],[f670,f112])).
% 0.20/0.53  fof(f112,plain,(
% 0.20/0.53    v1_relat_1(sK1) | ~spl3_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f110])).
% 0.20/0.53  fof(f670,plain,(
% 0.20/0.53    k1_xboole_0 = sK1 | ~v1_relat_1(sK1) | ~spl3_27),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f667])).
% 0.20/0.53  fof(f667,plain,(
% 0.20/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | ~v1_relat_1(sK1) | ~spl3_27),
% 0.20/0.53    inference(superposition,[],[f65,f289])).
% 0.20/0.53  fof(f289,plain,(
% 0.20/0.53    k1_xboole_0 = k2_relat_1(sK1) | ~spl3_27),
% 0.20/0.53    inference(avatar_component_clause,[],[f287])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(flattening,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.20/0.53  fof(f598,plain,(
% 0.20/0.53    spl3_27 | ~spl3_18 | ~spl3_20),
% 0.20/0.53    inference(avatar_split_clause,[],[f443,f224,f214,f287])).
% 0.20/0.53  fof(f214,plain,(
% 0.20/0.53    spl3_18 <=> r1_tarski(k1_xboole_0,k2_relat_1(sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.53  fof(f224,plain,(
% 0.20/0.53    spl3_20 <=> r1_tarski(k2_relat_1(sK1),k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.53  fof(f443,plain,(
% 0.20/0.53    ~r1_tarski(k1_xboole_0,k2_relat_1(sK1)) | k1_xboole_0 = k2_relat_1(sK1) | ~spl3_20),
% 0.20/0.53    inference(resolution,[],[f226,f63])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(flattening,[],[f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.53  fof(f226,plain,(
% 0.20/0.53    r1_tarski(k2_relat_1(sK1),k1_xboole_0) | ~spl3_20),
% 0.20/0.53    inference(avatar_component_clause,[],[f224])).
% 0.20/0.53  fof(f593,plain,(
% 0.20/0.53    spl3_18 | spl3_27 | ~spl3_34),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f592])).
% 0.20/0.53  fof(f592,plain,(
% 0.20/0.53    $false | (spl3_18 | spl3_27 | ~spl3_34)),
% 0.20/0.53    inference(subsumption_resolution,[],[f591,f216])).
% 0.20/0.53  fof(f216,plain,(
% 0.20/0.53    ~r1_tarski(k1_xboole_0,k2_relat_1(sK1)) | spl3_18),
% 0.20/0.53    inference(avatar_component_clause,[],[f214])).
% 0.20/0.53  fof(f591,plain,(
% 0.20/0.53    r1_tarski(k1_xboole_0,k2_relat_1(sK1)) | (spl3_27 | ~spl3_34)),
% 0.20/0.53    inference(forward_demodulation,[],[f590,f67])).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.53    inference(cnf_transformation,[],[f9])).
% 0.20/0.53  fof(f590,plain,(
% 0.20/0.53    r1_tarski(k2_relat_1(k1_xboole_0),k2_relat_1(sK1)) | (spl3_27 | ~spl3_34)),
% 0.20/0.53    inference(subsumption_resolution,[],[f572,f288])).
% 0.20/0.53  fof(f288,plain,(
% 0.20/0.53    k1_xboole_0 != k2_relat_1(sK1) | spl3_27),
% 0.20/0.53    inference(avatar_component_clause,[],[f287])).
% 0.20/0.53  fof(f572,plain,(
% 0.20/0.53    r1_tarski(k2_relat_1(k1_xboole_0),k2_relat_1(sK1)) | k1_xboole_0 = k2_relat_1(sK1) | ~spl3_34),
% 0.20/0.53    inference(superposition,[],[f74,f371])).
% 0.20/0.53  fof(f371,plain,(
% 0.20/0.53    k1_xboole_0 = sK2(k2_relat_1(sK1),k1_xboole_0) | ~spl3_34),
% 0.20/0.53    inference(avatar_component_clause,[],[f369])).
% 0.20/0.53  fof(f369,plain,(
% 0.20/0.53    spl3_34 <=> k1_xboole_0 = sK2(k2_relat_1(sK1),k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(k2_relat_1(sK2(X0,X1)),X0) | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_tarski(k2_relat_1(sK2(X0,X1)),X0) & k1_relat_1(sK2(X0,X1)) = X1 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))) | (k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X2] : (r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1 & v1_funct_1(X2) & v1_relat_1(X2)) => (r1_tarski(k2_relat_1(sK2(X0,X1)),X0) & k1_relat_1(sK2(X0,X1)) = X1 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1] : (? [X2] : (r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1 & v1_funct_1(X2) & v1_relat_1(X2)) | (k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.20/0.53    inference(flattening,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1] : (? [X2] : ((r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1) & (v1_funct_1(X2) & v1_relat_1(X2))) | (k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 0.20/0.53  fof(f408,plain,(
% 0.20/0.53    spl3_36 | ~spl3_17 | ~spl3_27),
% 0.20/0.53    inference(avatar_split_clause,[],[f394,f287,f209,f405])).
% 0.20/0.53  fof(f209,plain,(
% 0.20/0.53    spl3_17 <=> m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.53  fof(f394,plain,(
% 0.20/0.53    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl3_17 | ~spl3_27)),
% 0.20/0.53    inference(backward_demodulation,[],[f211,f289])).
% 0.20/0.53  fof(f211,plain,(
% 0.20/0.53    m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(k1_xboole_0)) | ~spl3_17),
% 0.20/0.53    inference(avatar_component_clause,[],[f209])).
% 0.20/0.53  fof(f372,plain,(
% 0.20/0.53    spl3_34 | spl3_27),
% 0.20/0.53    inference(avatar_split_clause,[],[f367,f287,f369])).
% 0.20/0.53  fof(f367,plain,(
% 0.20/0.53    k1_xboole_0 = sK2(k2_relat_1(sK1),k1_xboole_0) | spl3_27),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f87,f302,f64])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f302,plain,(
% 0.20/0.53    ( ! [X0] : (v1_relat_1(sK2(k2_relat_1(sK1),X0))) ) | spl3_27),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f288,f68])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f40])).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k1_relat_1(sK2(X0,k1_xboole_0))) )),
% 0.20/0.53    inference(equality_resolution,[],[f73])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X1 | k1_xboole_0 != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f40])).
% 0.20/0.53  fof(f229,plain,(
% 0.20/0.53    spl3_14 | ~spl3_12 | ~spl3_13),
% 0.20/0.53    inference(avatar_split_clause,[],[f228,f182,f175,f188])).
% 0.20/0.53  fof(f175,plain,(
% 0.20/0.53    spl3_12 <=> k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.53  fof(f182,plain,(
% 0.20/0.53    spl3_13 <=> k1_xboole_0 = sK0),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.53  fof(f228,plain,(
% 0.20/0.53    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),k1_xboole_0,sK1) | (~spl3_12 | ~spl3_13)),
% 0.20/0.53    inference(forward_demodulation,[],[f177,f184])).
% 0.20/0.53  fof(f184,plain,(
% 0.20/0.53    k1_xboole_0 = sK0 | ~spl3_13),
% 0.20/0.53    inference(avatar_component_clause,[],[f182])).
% 0.20/0.53  fof(f177,plain,(
% 0.20/0.53    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1) | ~spl3_12),
% 0.20/0.53    inference(avatar_component_clause,[],[f175])).
% 0.20/0.53  fof(f227,plain,(
% 0.20/0.53    spl3_20 | ~spl3_4 | ~spl3_13),
% 0.20/0.53    inference(avatar_split_clause,[],[f196,f182,f104,f224])).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    spl3_4 <=> r1_tarski(k2_relat_1(sK1),sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.53  fof(f196,plain,(
% 0.20/0.53    r1_tarski(k2_relat_1(sK1),k1_xboole_0) | (~spl3_4 | ~spl3_13)),
% 0.20/0.53    inference(backward_demodulation,[],[f106,f184])).
% 0.20/0.53  fof(f106,plain,(
% 0.20/0.53    r1_tarski(k2_relat_1(sK1),sK0) | ~spl3_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f104])).
% 0.20/0.53  fof(f222,plain,(
% 0.20/0.53    ~spl3_19 | spl3_2 | ~spl3_13),
% 0.20/0.53    inference(avatar_split_clause,[],[f195,f182,f95,f219])).
% 0.20/0.53  fof(f95,plain,(
% 0.20/0.53    spl3_2 <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.53  fof(f195,plain,(
% 0.20/0.53    ~v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) | (spl3_2 | ~spl3_13)),
% 0.20/0.53    inference(backward_demodulation,[],[f97,f184])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | spl3_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f95])).
% 0.20/0.53  fof(f212,plain,(
% 0.20/0.53    spl3_17 | ~spl3_7 | ~spl3_13),
% 0.20/0.53    inference(avatar_split_clause,[],[f193,f182,f140,f209])).
% 0.20/0.53  fof(f140,plain,(
% 0.20/0.53    spl3_7 <=> m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.53  fof(f193,plain,(
% 0.20/0.53    m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(k1_xboole_0)) | (~spl3_7 | ~spl3_13)),
% 0.20/0.53    inference(backward_demodulation,[],[f142,f184])).
% 0.20/0.53  fof(f142,plain,(
% 0.20/0.53    m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(sK0)) | ~spl3_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f140])).
% 0.20/0.53  fof(f185,plain,(
% 0.20/0.53    spl3_13 | ~spl3_12 | spl3_2 | ~spl3_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f180,f99,f95,f175,f182])).
% 0.20/0.53  fof(f99,plain,(
% 0.20/0.53    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.53  fof(f180,plain,(
% 0.20/0.53    k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1) | k1_xboole_0 = sK0 | (spl3_2 | ~spl3_3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f167,f97])).
% 0.20/0.53  fof(f167,plain,(
% 0.20/0.53    k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1) | k1_xboole_0 = sK0 | v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~spl3_3),
% 0.20/0.53    inference(resolution,[],[f100,f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | v1_funct_2(X2,X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f100,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~spl3_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f99])).
% 0.20/0.53  fof(f179,plain,(
% 0.20/0.53    spl3_12 | ~spl3_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f165,f99,f175])).
% 0.20/0.53  fof(f165,plain,(
% 0.20/0.53    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1) | ~spl3_3),
% 0.20/0.53    inference(resolution,[],[f100,f76])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.53  fof(f145,plain,(
% 0.20/0.53    spl3_3 | ~spl3_4 | ~spl3_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f134,f110,f104,f99])).
% 0.20/0.53  % (17927)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.53  fof(f134,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | (~spl3_4 | ~spl3_5)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f112,f85,f106,f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(flattening,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(ennf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.53    inference(equality_resolution,[],[f61])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f38])).
% 0.20/0.53  fof(f143,plain,(
% 0.20/0.53    spl3_7 | ~spl3_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f136,f104,f140])).
% 0.20/0.53  fof(f136,plain,(
% 0.20/0.53    m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(sK0)) | ~spl3_4),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f106,f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.53    inference(nnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.53  fof(f113,plain,(
% 0.20/0.53    spl3_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f41,f110])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    v1_relat_1(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.53    inference(flattening,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.20/0.53    inference(negated_conjecture,[],[f15])).
% 0.20/0.53  fof(f15,conjecture,(
% 0.20/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.20/0.53  fof(f108,plain,(
% 0.20/0.53    spl3_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f42,f91])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    spl3_1 <=> v1_funct_1(sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    v1_funct_1(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f32])).
% 0.20/0.53  fof(f107,plain,(
% 0.20/0.53    spl3_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f43,f104])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    r1_tarski(k2_relat_1(sK1),sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f32])).
% 0.20/0.53  fof(f102,plain,(
% 0.20/0.53    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f44,f99,f95,f91])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f32])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (17934)------------------------------
% 0.20/0.53  % (17934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (17934)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (17934)Memory used [KB]: 6524
% 0.20/0.53  % (17934)Time elapsed: 0.109 s
% 0.20/0.53  % (17934)------------------------------
% 0.20/0.53  % (17934)------------------------------
% 0.20/0.53  % (17920)Success in time 0.173 s
%------------------------------------------------------------------------------
