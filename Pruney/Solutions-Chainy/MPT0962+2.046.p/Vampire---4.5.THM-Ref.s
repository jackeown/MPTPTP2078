%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 260 expanded)
%              Number of leaves         :   35 ( 105 expanded)
%              Depth                    :   14
%              Number of atoms          :  452 ( 816 expanded)
%              Number of equality atoms :   78 ( 130 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f265,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f81,f83,f87,f92,f101,f106,f109,f140,f143,f154,f160,f166,f171,f176,f182,f189,f205,f218,f251,f257])).

fof(f257,plain,
    ( spl3_20
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f253,f249,f216])).

fof(f216,plain,
    ( spl3_20
  <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f249,plain,
    ( spl3_24
  <=> ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | v1_funct_2(sK1,k1_xboole_0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f253,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl3_24 ),
    inference(resolution,[],[f252,f88])).

fof(f88,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f42,f41])).

fof(f41,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f42,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f252,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
        | v1_funct_2(sK1,k1_xboole_0,X0) )
    | ~ spl3_24 ),
    inference(resolution,[],[f250,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f250,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | v1_funct_2(sK1,k1_xboole_0,X0) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f249])).

fof(f251,plain,
    ( ~ spl3_5
    | spl3_24
    | ~ spl3_8
    | ~ spl3_18
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f247,f203,f187,f99,f249,f85])).

fof(f85,plain,
    ( spl3_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f99,plain,
    ( spl3_8
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f187,plain,
    ( spl3_18
  <=> k1_xboole_0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f203,plain,
    ( spl3_19
  <=> k1_xboole_0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f247,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
        | ~ r1_tarski(k1_xboole_0,X0)
        | v1_funct_2(sK1,k1_xboole_0,X0)
        | ~ v1_relat_1(sK1) )
    | ~ spl3_18
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f246,f204])).

fof(f204,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f203])).

fof(f246,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | v1_funct_2(sK1,k1_xboole_0,X0)
        | ~ r1_tarski(k1_relat_1(sK1),k1_xboole_0)
        | ~ v1_relat_1(sK1) )
    | ~ spl3_18
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f244,f188])).

fof(f188,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f187])).

fof(f244,plain,
    ( ! [X0] :
        ( v1_funct_2(sK1,k1_xboole_0,X0)
        | ~ r1_tarski(k2_relat_1(sK1),X0)
        | ~ r1_tarski(k1_relat_1(sK1),k1_xboole_0)
        | ~ v1_relat_1(sK1) )
    | ~ spl3_19 ),
    inference(resolution,[],[f214,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f214,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))
        | v1_funct_2(sK1,k1_xboole_0,X5) )
    | ~ spl3_19 ),
    inference(trivial_inequality_removal,[],[f211])).

fof(f211,plain,
    ( ! [X5] :
        ( k1_xboole_0 != k1_xboole_0
        | v1_funct_2(sK1,k1_xboole_0,X5)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5))) )
    | ~ spl3_19 ),
    inference(superposition,[],[f121,f204])).

fof(f121,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(superposition,[],[f66,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f66,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f218,plain,
    ( ~ spl3_20
    | spl3_15
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f206,f203,f169,f216])).

fof(f169,plain,
    ( spl3_15
  <=> v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f206,plain,
    ( ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | spl3_15
    | ~ spl3_19 ),
    inference(superposition,[],[f170,f204])).

fof(f170,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)
    | spl3_15 ),
    inference(avatar_component_clause,[],[f169])).

fof(f205,plain,
    ( ~ spl3_5
    | spl3_19
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f197,f187,f203,f85])).

fof(f197,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_18 ),
    inference(trivial_inequality_removal,[],[f196])).

fof(f196,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_18 ),
    inference(superposition,[],[f46,f188])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f189,plain,
    ( spl3_18
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f185,f180,f187])).

fof(f180,plain,
    ( spl3_17
  <=> v1_xboole_0(k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f185,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ spl3_17 ),
    inference(resolution,[],[f181,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f181,plain,
    ( v1_xboole_0(k2_relat_1(sK1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f180])).

fof(f182,plain,
    ( spl3_17
    | ~ spl3_7
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f178,f174,f96,f180])).

fof(f96,plain,
    ( spl3_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f174,plain,
    ( spl3_16
  <=> r1_tarski(k2_relat_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f178,plain,
    ( v1_xboole_0(k2_relat_1(sK1))
    | ~ spl3_7
    | ~ spl3_16 ),
    inference(resolution,[],[f175,f116])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | v1_xboole_0(X0) )
    | ~ spl3_7 ),
    inference(resolution,[],[f114,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl3_7 ),
    inference(resolution,[],[f113,f49])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f113,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl3_7 ),
    inference(resolution,[],[f61,f97])).

fof(f97,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f175,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_xboole_0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f174])).

fof(f176,plain,
    ( spl3_16
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f172,f151,f79,f174])).

fof(f79,plain,
    ( spl3_4
  <=> r1_tarski(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f151,plain,
    ( spl3_13
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f172,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(superposition,[],[f80,f152])).

fof(f152,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f151])).

fof(f80,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f171,plain,
    ( ~ spl3_15
    | spl3_2
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f167,f151,f72,f169])).

fof(f72,plain,
    ( spl3_2
  <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f167,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)
    | spl3_2
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f73,f152])).

fof(f73,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f166,plain,
    ( ~ spl3_10
    | spl3_12 ),
    inference(avatar_split_clause,[],[f165,f145,f135])).

fof(f135,plain,
    ( spl3_10
  <=> m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f145,plain,
    ( spl3_12
  <=> r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f165,plain,
    ( ~ m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(k1_relat_1(sK1)))
    | spl3_12 ),
    inference(resolution,[],[f146,f51])).

fof(f146,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f145])).

fof(f160,plain,
    ( ~ spl3_5
    | ~ spl3_12
    | ~ spl3_4
    | spl3_3 ),
    inference(avatar_split_clause,[],[f156,f75,f79,f145,f85])).

fof(f75,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f156,plain,
    ( ~ r1_tarski(k2_relat_1(sK1),sK0)
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | spl3_3 ),
    inference(resolution,[],[f76,f53])).

fof(f76,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f154,plain,
    ( spl3_13
    | spl3_2
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f148,f138,f79,f72,f151])).

fof(f138,plain,
    ( spl3_11
  <=> ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK1),X0)
        | v1_funct_2(sK1,k1_relat_1(sK1),X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f148,plain,
    ( v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | k1_xboole_0 = sK0
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(resolution,[],[f139,f80])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK1),X0)
        | v1_funct_2(sK1,k1_relat_1(sK1),X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f138])).

fof(f143,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | spl3_10 ),
    inference(resolution,[],[f136,f88])).

fof(f136,plain,
    ( ~ m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(k1_relat_1(sK1)))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f135])).

fof(f140,plain,
    ( ~ spl3_10
    | spl3_11
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f133,f85,f138,f135])).

fof(f133,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK1),X0)
        | k1_xboole_0 = X0
        | v1_funct_2(sK1,k1_relat_1(sK1),X0)
        | ~ m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(k1_relat_1(sK1))) )
    | ~ spl3_5 ),
    inference(resolution,[],[f132,f86])).

fof(f86,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1)
      | k1_xboole_0 = X1
      | v1_funct_2(X0,k1_relat_1(X0),X1)
      | ~ m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(k1_relat_1(X0))) ) ),
    inference(resolution,[],[f129,f51])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X1))
      | v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f128,f53])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
      | k1_xboole_0 = X1
      | v1_funct_2(X0,k1_relat_1(X0),X1) ) ),
    inference(equality_resolution,[],[f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f57,f54])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f109,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | spl3_9 ),
    inference(resolution,[],[f105,f88])).

fof(f105,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl3_9
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f106,plain,
    ( ~ spl3_9
    | spl3_8 ),
    inference(avatar_split_clause,[],[f102,f99,f104])).

fof(f102,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl3_8 ),
    inference(resolution,[],[f100,f51])).

fof(f100,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f99])).

fof(f101,plain,
    ( spl3_7
    | ~ spl3_8
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f94,f90,f99,f96])).

% (16476)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f90,plain,
    ( spl3_6
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f94,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0)
    | ~ spl3_6 ),
    inference(resolution,[],[f50,f91])).

fof(f91,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f92,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f62,f90])).

fof(f62,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f87,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f37,f85])).

fof(f37,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
      | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
      | ~ v1_funct_1(sK1) )
    & r1_tarski(k2_relat_1(sK1),sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f28])).

fof(f28,plain,
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

fof(f16,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f83,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f38,f69])).

fof(f69,plain,
    ( spl3_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f38,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f81,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f39,f79])).

fof(f39,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f77,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f40,f75,f72,f69])).

fof(f40,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (16478)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.45  % (16478)Refutation not found, incomplete strategy% (16478)------------------------------
% 0.20/0.45  % (16478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (16478)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.45  
% 0.20/0.45  % (16478)Memory used [KB]: 1918
% 0.20/0.45  % (16478)Time elapsed: 0.045 s
% 0.20/0.45  % (16478)------------------------------
% 0.20/0.45  % (16478)------------------------------
% 0.20/0.47  % (16468)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.47  % (16466)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (16470)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.47  % (16463)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (16474)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (16471)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.48  % (16465)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (16471)Refutation not found, incomplete strategy% (16471)------------------------------
% 0.20/0.48  % (16471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (16471)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (16471)Memory used [KB]: 10618
% 0.20/0.48  % (16471)Time elapsed: 0.074 s
% 0.20/0.48  % (16471)------------------------------
% 0.20/0.48  % (16471)------------------------------
% 0.20/0.48  % (16470)Refutation not found, incomplete strategy% (16470)------------------------------
% 0.20/0.48  % (16470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (16470)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (16470)Memory used [KB]: 6140
% 0.20/0.48  % (16470)Time elapsed: 0.067 s
% 0.20/0.48  % (16470)------------------------------
% 0.20/0.48  % (16470)------------------------------
% 0.20/0.48  % (16479)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.48  % (16467)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.49  % (16461)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (16462)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (16461)Refutation not found, incomplete strategy% (16461)------------------------------
% 0.20/0.49  % (16461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (16461)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (16461)Memory used [KB]: 10618
% 0.20/0.49  % (16461)Time elapsed: 0.070 s
% 0.20/0.49  % (16461)------------------------------
% 0.20/0.49  % (16461)------------------------------
% 0.20/0.49  % (16479)Refutation not found, incomplete strategy% (16479)------------------------------
% 0.20/0.49  % (16479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (16479)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (16479)Memory used [KB]: 6140
% 0.20/0.49  % (16479)Time elapsed: 0.080 s
% 0.20/0.49  % (16479)------------------------------
% 0.20/0.49  % (16479)------------------------------
% 0.20/0.49  % (16463)Refutation not found, incomplete strategy% (16463)------------------------------
% 0.20/0.49  % (16463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (16463)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (16463)Memory used [KB]: 10618
% 0.20/0.49  % (16463)Time elapsed: 0.074 s
% 0.20/0.49  % (16463)------------------------------
% 0.20/0.49  % (16463)------------------------------
% 0.20/0.49  % (16472)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (16473)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (16473)Refutation not found, incomplete strategy% (16473)------------------------------
% 0.20/0.49  % (16473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (16473)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (16473)Memory used [KB]: 1663
% 0.20/0.49  % (16473)Time elapsed: 0.089 s
% 0.20/0.49  % (16473)------------------------------
% 0.20/0.49  % (16473)------------------------------
% 0.20/0.49  % (16466)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f265,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f77,f81,f83,f87,f92,f101,f106,f109,f140,f143,f154,f160,f166,f171,f176,f182,f189,f205,f218,f251,f257])).
% 0.20/0.50  fof(f257,plain,(
% 0.20/0.50    spl3_20 | ~spl3_24),
% 0.20/0.50    inference(avatar_split_clause,[],[f253,f249,f216])).
% 0.20/0.50  fof(f216,plain,(
% 0.20/0.50    spl3_20 <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.50  fof(f249,plain,(
% 0.20/0.50    spl3_24 <=> ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(sK1,k1_xboole_0,X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.20/0.50  fof(f253,plain,(
% 0.20/0.50    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~spl3_24),
% 0.20/0.50    inference(resolution,[],[f252,f88])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f42,f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.50  fof(f252,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) | v1_funct_2(sK1,k1_xboole_0,X0)) ) | ~spl3_24),
% 0.20/0.50    inference(resolution,[],[f250,f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.50    inference(nnf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.50  fof(f250,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(sK1,k1_xboole_0,X0)) ) | ~spl3_24),
% 0.20/0.50    inference(avatar_component_clause,[],[f249])).
% 0.20/0.50  fof(f251,plain,(
% 0.20/0.50    ~spl3_5 | spl3_24 | ~spl3_8 | ~spl3_18 | ~spl3_19),
% 0.20/0.50    inference(avatar_split_clause,[],[f247,f203,f187,f99,f249,f85])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    spl3_5 <=> v1_relat_1(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    spl3_8 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.50  fof(f187,plain,(
% 0.20/0.50    spl3_18 <=> k1_xboole_0 = k2_relat_1(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.50  fof(f203,plain,(
% 0.20/0.50    spl3_19 <=> k1_xboole_0 = k1_relat_1(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.50  fof(f247,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_xboole_0) | ~r1_tarski(k1_xboole_0,X0) | v1_funct_2(sK1,k1_xboole_0,X0) | ~v1_relat_1(sK1)) ) | (~spl3_18 | ~spl3_19)),
% 0.20/0.50    inference(forward_demodulation,[],[f246,f204])).
% 0.20/0.50  fof(f204,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(sK1) | ~spl3_19),
% 0.20/0.50    inference(avatar_component_clause,[],[f203])).
% 0.20/0.50  fof(f246,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(sK1,k1_xboole_0,X0) | ~r1_tarski(k1_relat_1(sK1),k1_xboole_0) | ~v1_relat_1(sK1)) ) | (~spl3_18 | ~spl3_19)),
% 0.20/0.50    inference(forward_demodulation,[],[f244,f188])).
% 0.20/0.50  fof(f188,plain,(
% 0.20/0.50    k1_xboole_0 = k2_relat_1(sK1) | ~spl3_18),
% 0.20/0.50    inference(avatar_component_clause,[],[f187])).
% 0.20/0.50  fof(f244,plain,(
% 0.20/0.50    ( ! [X0] : (v1_funct_2(sK1,k1_xboole_0,X0) | ~r1_tarski(k2_relat_1(sK1),X0) | ~r1_tarski(k1_relat_1(sK1),k1_xboole_0) | ~v1_relat_1(sK1)) ) | ~spl3_19),
% 0.20/0.50    inference(resolution,[],[f214,f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(flattening,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.20/0.50  fof(f214,plain,(
% 0.20/0.50    ( ! [X5] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5))) | v1_funct_2(sK1,k1_xboole_0,X5)) ) | ~spl3_19),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f211])).
% 0.20/0.50  fof(f211,plain,(
% 0.20/0.50    ( ! [X5] : (k1_xboole_0 != k1_xboole_0 | v1_funct_2(sK1,k1_xboole_0,X5) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))) ) | ~spl3_19),
% 0.20/0.50    inference(superposition,[],[f121,f204])).
% 0.20/0.50  fof(f121,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f120])).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 0.20/0.50    inference(superposition,[],[f66,f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.20/0.50    inference(equality_resolution,[],[f58])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(nnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(flattening,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.50  fof(f218,plain,(
% 0.20/0.50    ~spl3_20 | spl3_15 | ~spl3_19),
% 0.20/0.50    inference(avatar_split_clause,[],[f206,f203,f169,f216])).
% 0.20/0.50  fof(f169,plain,(
% 0.20/0.50    spl3_15 <=> v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.50  fof(f206,plain,(
% 0.20/0.50    ~v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | (spl3_15 | ~spl3_19)),
% 0.20/0.50    inference(superposition,[],[f170,f204])).
% 0.20/0.50  fof(f170,plain,(
% 0.20/0.50    ~v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) | spl3_15),
% 0.20/0.50    inference(avatar_component_clause,[],[f169])).
% 0.20/0.50  fof(f205,plain,(
% 0.20/0.50    ~spl3_5 | spl3_19 | ~spl3_18),
% 0.20/0.50    inference(avatar_split_clause,[],[f197,f187,f203,f85])).
% 0.20/0.50  fof(f197,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(sK1) | ~v1_relat_1(sK1) | ~spl3_18),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f196])).
% 0.20/0.50  fof(f196,plain,(
% 0.20/0.50    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_relat_1(sK1) | ~v1_relat_1(sK1) | ~spl3_18),
% 0.20/0.50    inference(superposition,[],[f46,f188])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.20/0.50  fof(f189,plain,(
% 0.20/0.50    spl3_18 | ~spl3_17),
% 0.20/0.50    inference(avatar_split_clause,[],[f185,f180,f187])).
% 0.20/0.50  fof(f180,plain,(
% 0.20/0.50    spl3_17 <=> v1_xboole_0(k2_relat_1(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.50  fof(f185,plain,(
% 0.20/0.50    k1_xboole_0 = k2_relat_1(sK1) | ~spl3_17),
% 0.20/0.50    inference(resolution,[],[f181,f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.50  fof(f181,plain,(
% 0.20/0.50    v1_xboole_0(k2_relat_1(sK1)) | ~spl3_17),
% 0.20/0.50    inference(avatar_component_clause,[],[f180])).
% 0.20/0.50  fof(f182,plain,(
% 0.20/0.50    spl3_17 | ~spl3_7 | ~spl3_16),
% 0.20/0.50    inference(avatar_split_clause,[],[f178,f174,f96,f180])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    spl3_7 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.50  fof(f174,plain,(
% 0.20/0.50    spl3_16 <=> r1_tarski(k2_relat_1(sK1),k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.50  fof(f178,plain,(
% 0.20/0.50    v1_xboole_0(k2_relat_1(sK1)) | (~spl3_7 | ~spl3_16)),
% 0.20/0.50    inference(resolution,[],[f175,f116])).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0)) ) | ~spl3_7),
% 0.20/0.50    inference(resolution,[],[f114,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f114,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) ) | ~spl3_7),
% 0.20/0.50    inference(resolution,[],[f113,f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.50    inference(rectify,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.50    inference(nnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl3_7),
% 0.20/0.50    inference(resolution,[],[f61,f97])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    v1_xboole_0(k1_xboole_0) | ~spl3_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f96])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.50  fof(f175,plain,(
% 0.20/0.50    r1_tarski(k2_relat_1(sK1),k1_xboole_0) | ~spl3_16),
% 0.20/0.50    inference(avatar_component_clause,[],[f174])).
% 0.20/0.50  fof(f176,plain,(
% 0.20/0.50    spl3_16 | ~spl3_4 | ~spl3_13),
% 0.20/0.50    inference(avatar_split_clause,[],[f172,f151,f79,f174])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    spl3_4 <=> r1_tarski(k2_relat_1(sK1),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.50  fof(f151,plain,(
% 0.20/0.50    spl3_13 <=> k1_xboole_0 = sK0),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.50  fof(f172,plain,(
% 0.20/0.50    r1_tarski(k2_relat_1(sK1),k1_xboole_0) | (~spl3_4 | ~spl3_13)),
% 0.20/0.50    inference(superposition,[],[f80,f152])).
% 0.20/0.50  fof(f152,plain,(
% 0.20/0.50    k1_xboole_0 = sK0 | ~spl3_13),
% 0.20/0.50    inference(avatar_component_clause,[],[f151])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    r1_tarski(k2_relat_1(sK1),sK0) | ~spl3_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f79])).
% 0.20/0.50  fof(f171,plain,(
% 0.20/0.50    ~spl3_15 | spl3_2 | ~spl3_13),
% 0.20/0.50    inference(avatar_split_clause,[],[f167,f151,f72,f169])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    spl3_2 <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.50  fof(f167,plain,(
% 0.20/0.50    ~v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) | (spl3_2 | ~spl3_13)),
% 0.20/0.50    inference(forward_demodulation,[],[f73,f152])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | spl3_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f72])).
% 0.20/0.50  fof(f166,plain,(
% 0.20/0.50    ~spl3_10 | spl3_12),
% 0.20/0.50    inference(avatar_split_clause,[],[f165,f145,f135])).
% 0.20/0.50  fof(f135,plain,(
% 0.20/0.50    spl3_10 <=> m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(k1_relat_1(sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.50  fof(f145,plain,(
% 0.20/0.50    spl3_12 <=> r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.50  fof(f165,plain,(
% 0.20/0.50    ~m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(k1_relat_1(sK1))) | spl3_12),
% 0.20/0.50    inference(resolution,[],[f146,f51])).
% 0.20/0.50  fof(f146,plain,(
% 0.20/0.50    ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) | spl3_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f145])).
% 0.20/0.50  fof(f160,plain,(
% 0.20/0.50    ~spl3_5 | ~spl3_12 | ~spl3_4 | spl3_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f156,f75,f79,f145,f85])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.50  fof(f156,plain,(
% 0.20/0.50    ~r1_tarski(k2_relat_1(sK1),sK0) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | spl3_3),
% 0.20/0.50    inference(resolution,[],[f76,f53])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | spl3_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f75])).
% 0.20/0.50  fof(f154,plain,(
% 0.20/0.50    spl3_13 | spl3_2 | ~spl3_4 | ~spl3_11),
% 0.20/0.50    inference(avatar_split_clause,[],[f148,f138,f79,f72,f151])).
% 0.20/0.50  fof(f138,plain,(
% 0.20/0.50    spl3_11 <=> ! [X0] : (~r1_tarski(k2_relat_1(sK1),X0) | v1_funct_2(sK1,k1_relat_1(sK1),X0) | k1_xboole_0 = X0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.50  fof(f148,plain,(
% 0.20/0.50    v1_funct_2(sK1,k1_relat_1(sK1),sK0) | k1_xboole_0 = sK0 | (~spl3_4 | ~spl3_11)),
% 0.20/0.50    inference(resolution,[],[f139,f80])).
% 0.20/0.50  fof(f139,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(k2_relat_1(sK1),X0) | v1_funct_2(sK1,k1_relat_1(sK1),X0) | k1_xboole_0 = X0) ) | ~spl3_11),
% 0.20/0.50    inference(avatar_component_clause,[],[f138])).
% 0.20/0.50  fof(f143,plain,(
% 0.20/0.50    spl3_10),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f141])).
% 0.20/0.50  fof(f141,plain,(
% 0.20/0.50    $false | spl3_10),
% 0.20/0.50    inference(resolution,[],[f136,f88])).
% 0.20/0.50  fof(f136,plain,(
% 0.20/0.50    ~m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(k1_relat_1(sK1))) | spl3_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f135])).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    ~spl3_10 | spl3_11 | ~spl3_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f133,f85,f138,f135])).
% 0.20/0.50  fof(f133,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(k2_relat_1(sK1),X0) | k1_xboole_0 = X0 | v1_funct_2(sK1,k1_relat_1(sK1),X0) | ~m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(k1_relat_1(sK1)))) ) | ~spl3_5),
% 0.20/0.50    inference(resolution,[],[f132,f86])).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    v1_relat_1(sK1) | ~spl3_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f85])).
% 0.20/0.50  fof(f132,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1) | k1_xboole_0 = X1 | v1_funct_2(X0,k1_relat_1(X0),X1) | ~m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(k1_relat_1(X0)))) )),
% 0.20/0.50    inference(resolution,[],[f129,f51])).
% 0.20/0.50  fof(f129,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),k1_relat_1(X1)) | v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(resolution,[],[f128,f53])).
% 0.20/0.50  fof(f128,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) | k1_xboole_0 = X1 | v1_funct_2(X0,k1_relat_1(X0),X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f127])).
% 0.20/0.50  fof(f127,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f126])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(superposition,[],[f57,f54])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f36])).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    spl3_9),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f107])).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    $false | spl3_9),
% 0.20/0.50    inference(resolution,[],[f105,f88])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl3_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f104])).
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    spl3_9 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    ~spl3_9 | spl3_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f102,f99,f104])).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl3_8),
% 0.20/0.50    inference(resolution,[],[f100,f51])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl3_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f99])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    spl3_7 | ~spl3_8 | ~spl3_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f94,f90,f99,f96])).
% 0.20/0.50  % (16476)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    spl3_6 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    ~r1_tarski(k1_xboole_0,k1_xboole_0) | v1_xboole_0(k1_xboole_0) | ~spl3_6),
% 0.20/0.50    inference(resolution,[],[f50,f91])).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f90])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.20/0.50    inference(flattening,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.20/0.50  fof(f92,plain,(
% 0.20/0.50    spl3_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f62,f90])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.20/0.50    inference(equality_resolution,[],[f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    spl3_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f37,f85])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    v1_relat_1(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.20/0.50    inference(negated_conjecture,[],[f13])).
% 0.20/0.50  fof(f13,conjecture,(
% 0.20/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    spl3_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f38,f69])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    spl3_1 <=> v1_funct_1(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    v1_funct_1(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    spl3_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f39,f79])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    r1_tarski(k2_relat_1(sK1),sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f40,f75,f72,f69])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (16466)------------------------------
% 0.20/0.50  % (16466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (16466)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (16466)Memory used [KB]: 10746
% 0.20/0.50  % (16466)Time elapsed: 0.054 s
% 0.20/0.50  % (16466)------------------------------
% 0.20/0.50  % (16466)------------------------------
% 0.20/0.50  % (16464)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (16480)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (16459)Success in time 0.142 s
%------------------------------------------------------------------------------
