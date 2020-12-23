%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 158 expanded)
%              Number of leaves         :   24 (  53 expanded)
%              Depth                    :   16
%              Number of atoms          :  368 ( 593 expanded)
%              Number of equality atoms :  108 ( 165 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f409,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f108,f113,f118,f123,f159,f245,f276,f282,f283,f408])).

fof(f408,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_16 ),
    inference(avatar_contradiction_clause,[],[f407])).

fof(f407,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f406,f166])).

fof(f166,plain,
    ( v5_relat_1(sK3,k1_tarski(sK1))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl6_11
  <=> v5_relat_1(sK3,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f406,plain,
    ( ~ v5_relat_1(sK3,k1_tarski(sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(equality_resolution,[],[f405])).

fof(f405,plain,
    ( ! [X0] :
        ( sK1 != X0
        | ~ v5_relat_1(sK3,k1_tarski(X0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f404,f107])).

fof(f107,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl6_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f404,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2,sK0)
        | sK1 != X0
        | ~ v5_relat_1(sK3,k1_tarski(X0)) )
    | spl6_1
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f403,f242])).

fof(f242,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl6_16
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f403,plain,
    ( ! [X0] :
        ( sK1 != X0
        | ~ v5_relat_1(sK3,k1_tarski(X0))
        | ~ r2_hidden(sK2,k1_relat_1(sK3)) )
    | spl6_1
    | ~ spl6_5
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f402,f122])).

fof(f122,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl6_5
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f402,plain,
    ( ! [X0] :
        ( sK1 != X0
        | ~ v5_relat_1(sK3,k1_tarski(X0))
        | ~ r2_hidden(sK2,k1_relat_1(sK3))
        | ~ v1_funct_1(sK3) )
    | spl6_1
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f392,f158])).

fof(f158,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl6_10
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f392,plain,
    ( ! [X0] :
        ( sK1 != X0
        | ~ v5_relat_1(sK3,k1_tarski(X0))
        | ~ v1_relat_1(sK3)
        | ~ r2_hidden(sK2,k1_relat_1(sK3))
        | ~ v1_funct_1(sK3) )
    | spl6_1 ),
    inference(superposition,[],[f102,f316])).

fof(f316,plain,(
    ! [X6,X7,X5] :
      ( k1_funct_1(X5,X7) = X6
      | ~ v5_relat_1(X5,k1_tarski(X6))
      | ~ v1_relat_1(X5)
      | ~ r2_hidden(X7,k1_relat_1(X5))
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f312,f80])).

fof(f80,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f312,plain,(
    ! [X6,X7,X5] :
      ( ~ v1_funct_1(X5)
      | ~ v5_relat_1(X5,k1_tarski(X6))
      | ~ v1_relat_1(X5)
      | v1_xboole_0(k1_tarski(X6))
      | ~ r2_hidden(X7,k1_relat_1(X5))
      | k1_funct_1(X5,X7) = X6 ) ),
    inference(resolution,[],[f189,f98])).

fof(f98,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).

fof(f43,plain,(
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

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

% (11872)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
fof(f41,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),X2)
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X2)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X2)
      | ~ r2_hidden(X0,k1_relat_1(X1)) ) ),
    inference(resolution,[],[f74,f75])).

fof(f75,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

fof(f102,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl6_1
  <=> sK1 = k1_funct_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f283,plain,
    ( spl6_11
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f278,f110,f164])).

fof(f110,plain,
    ( spl6_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f278,plain,
    ( v5_relat_1(sK3,k1_tarski(sK1))
    | ~ spl6_3 ),
    inference(resolution,[],[f112,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f112,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f282,plain,
    ( spl6_14
    | spl6_15
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f281,f115,f110,f227,f223])).

fof(f223,plain,
    ( spl6_14
  <=> sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f227,plain,
    ( spl6_15
  <=> k1_xboole_0 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f115,plain,
    ( spl6_4
  <=> v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f281,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f277,f117])).

fof(f117,plain,
    ( v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f115])).

fof(f277,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | k1_xboole_0 = k1_tarski(sK1)
    | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)
    | ~ spl6_3 ),
    inference(resolution,[],[f112,f58])).

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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f276,plain,(
    ~ spl6_15 ),
    inference(avatar_contradiction_clause,[],[f275])).

fof(f275,plain,
    ( $false
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f251,f124])).

fof(f124,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f76,f94])).

fof(f94,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f76,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f251,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl6_15 ),
    inference(superposition,[],[f97,f229])).

fof(f229,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f227])).

fof(f97,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f245,plain,
    ( spl6_16
    | ~ spl6_3
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f244,f223,f110,f240])).

fof(f244,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_3
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f236,f112])).

fof(f236,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl6_14 ),
    inference(superposition,[],[f64,f225])).

fof(f225,plain,
    ( sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f223])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f159,plain,
    ( spl6_10
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f154,f110,f156])).

fof(f154,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f153,f79])).

fof(f79,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f153,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))
    | ~ spl6_3 ),
    inference(resolution,[],[f77,f112])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f123,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f45,f120])).

fof(f45,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f31])).

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

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(f118,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f46,f115])).

fof(f46,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f113,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f47,f110])).

fof(f47,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f108,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f48,f105])).

fof(f48,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f103,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f49,f100])).

fof(f49,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:46:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (11874)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (11886)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.51  % (11870)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (11873)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (11878)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (11892)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.52  % (11875)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (11885)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (11894)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.52  % (11880)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.52  % (11882)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.52  % (11896)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.53  % (11900)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (11900)Refutation not found, incomplete strategy% (11900)------------------------------
% 0.22/0.53  % (11900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (11900)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (11900)Memory used [KB]: 1663
% 0.22/0.53  % (11900)Time elapsed: 0.118 s
% 0.22/0.53  % (11900)------------------------------
% 0.22/0.53  % (11900)------------------------------
% 0.22/0.53  % (11899)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.53  % (11881)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (11887)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.53  % (11893)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (11884)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.53  % (11892)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f409,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f103,f108,f113,f118,f123,f159,f245,f276,f282,f283,f408])).
% 0.22/0.53  fof(f408,plain,(
% 0.22/0.53    spl6_1 | ~spl6_2 | ~spl6_5 | ~spl6_10 | ~spl6_11 | ~spl6_16),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f407])).
% 0.22/0.53  fof(f407,plain,(
% 0.22/0.53    $false | (spl6_1 | ~spl6_2 | ~spl6_5 | ~spl6_10 | ~spl6_11 | ~spl6_16)),
% 0.22/0.53    inference(subsumption_resolution,[],[f406,f166])).
% 0.22/0.53  fof(f166,plain,(
% 0.22/0.53    v5_relat_1(sK3,k1_tarski(sK1)) | ~spl6_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f164])).
% 0.22/0.53  fof(f164,plain,(
% 0.22/0.53    spl6_11 <=> v5_relat_1(sK3,k1_tarski(sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.53  fof(f406,plain,(
% 0.22/0.53    ~v5_relat_1(sK3,k1_tarski(sK1)) | (spl6_1 | ~spl6_2 | ~spl6_5 | ~spl6_10 | ~spl6_16)),
% 0.22/0.53    inference(equality_resolution,[],[f405])).
% 0.22/0.53  fof(f405,plain,(
% 0.22/0.53    ( ! [X0] : (sK1 != X0 | ~v5_relat_1(sK3,k1_tarski(X0))) ) | (spl6_1 | ~spl6_2 | ~spl6_5 | ~spl6_10 | ~spl6_16)),
% 0.22/0.53    inference(subsumption_resolution,[],[f404,f107])).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    r2_hidden(sK2,sK0) | ~spl6_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f105])).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    spl6_2 <=> r2_hidden(sK2,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.53  fof(f404,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(sK2,sK0) | sK1 != X0 | ~v5_relat_1(sK3,k1_tarski(X0))) ) | (spl6_1 | ~spl6_5 | ~spl6_10 | ~spl6_16)),
% 0.22/0.53    inference(forward_demodulation,[],[f403,f242])).
% 0.22/0.53  fof(f242,plain,(
% 0.22/0.53    sK0 = k1_relat_1(sK3) | ~spl6_16),
% 0.22/0.53    inference(avatar_component_clause,[],[f240])).
% 0.22/0.53  fof(f240,plain,(
% 0.22/0.53    spl6_16 <=> sK0 = k1_relat_1(sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.22/0.53  fof(f403,plain,(
% 0.22/0.53    ( ! [X0] : (sK1 != X0 | ~v5_relat_1(sK3,k1_tarski(X0)) | ~r2_hidden(sK2,k1_relat_1(sK3))) ) | (spl6_1 | ~spl6_5 | ~spl6_10)),
% 0.22/0.53    inference(subsumption_resolution,[],[f402,f122])).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    v1_funct_1(sK3) | ~spl6_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f120])).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    spl6_5 <=> v1_funct_1(sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.53  fof(f402,plain,(
% 0.22/0.53    ( ! [X0] : (sK1 != X0 | ~v5_relat_1(sK3,k1_tarski(X0)) | ~r2_hidden(sK2,k1_relat_1(sK3)) | ~v1_funct_1(sK3)) ) | (spl6_1 | ~spl6_10)),
% 0.22/0.53    inference(subsumption_resolution,[],[f392,f158])).
% 0.22/0.53  fof(f158,plain,(
% 0.22/0.53    v1_relat_1(sK3) | ~spl6_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f156])).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    spl6_10 <=> v1_relat_1(sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.53  fof(f392,plain,(
% 0.22/0.53    ( ! [X0] : (sK1 != X0 | ~v5_relat_1(sK3,k1_tarski(X0)) | ~v1_relat_1(sK3) | ~r2_hidden(sK2,k1_relat_1(sK3)) | ~v1_funct_1(sK3)) ) | spl6_1),
% 0.22/0.53    inference(superposition,[],[f102,f316])).
% 0.22/0.53  fof(f316,plain,(
% 0.22/0.53    ( ! [X6,X7,X5] : (k1_funct_1(X5,X7) = X6 | ~v5_relat_1(X5,k1_tarski(X6)) | ~v1_relat_1(X5) | ~r2_hidden(X7,k1_relat_1(X5)) | ~v1_funct_1(X5)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f312,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.22/0.53  fof(f312,plain,(
% 0.22/0.53    ( ! [X6,X7,X5] : (~v1_funct_1(X5) | ~v5_relat_1(X5,k1_tarski(X6)) | ~v1_relat_1(X5) | v1_xboole_0(k1_tarski(X6)) | ~r2_hidden(X7,k1_relat_1(X5)) | k1_funct_1(X5,X7) = X6) )),
% 0.22/0.53    inference(resolution,[],[f189,f98])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.22/0.53    inference(equality_resolution,[],[f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.53    inference(rectify,[],[f41])).
% 0.22/0.53  % (11872)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.53  fof(f189,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X0),X2) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X2) | ~v1_relat_1(X1) | v1_xboole_0(X2) | ~r2_hidden(X0,k1_relat_1(X1))) )),
% 0.22/0.53    inference(resolution,[],[f74,f75])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.53    inference(flattening,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2))),
% 0.22/0.53    inference(flattening,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2))) | (~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    sK1 != k1_funct_1(sK3,sK2) | spl6_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f100])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    spl6_1 <=> sK1 = k1_funct_1(sK3,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.53  fof(f283,plain,(
% 0.22/0.53    spl6_11 | ~spl6_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f278,f110,f164])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    spl6_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.53  fof(f278,plain,(
% 0.22/0.53    v5_relat_1(sK3,k1_tarski(sK1)) | ~spl6_3),
% 0.22/0.53    inference(resolution,[],[f112,f78])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.22/0.53    inference(pure_predicate_removal,[],[f13])).
% 0.22/0.53  fof(f13,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~spl6_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f110])).
% 0.22/0.53  fof(f282,plain,(
% 0.22/0.53    spl6_14 | spl6_15 | ~spl6_3 | ~spl6_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f281,f115,f110,f227,f223])).
% 0.22/0.53  fof(f223,plain,(
% 0.22/0.53    spl6_14 <=> sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.22/0.53  fof(f227,plain,(
% 0.22/0.53    spl6_15 <=> k1_xboole_0 = k1_tarski(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    spl6_4 <=> v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.53  fof(f281,plain,(
% 0.22/0.53    k1_xboole_0 = k1_tarski(sK1) | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) | (~spl6_3 | ~spl6_4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f277,f117])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~spl6_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f115])).
% 0.22/0.53  fof(f277,plain,(
% 0.22/0.53    ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | k1_xboole_0 = k1_tarski(sK1) | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) | ~spl6_3),
% 0.22/0.53    inference(resolution,[],[f112,f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(nnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(flattening,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.53  fof(f276,plain,(
% 0.22/0.53    ~spl6_15),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f275])).
% 0.22/0.53  fof(f275,plain,(
% 0.22/0.53    $false | ~spl6_15),
% 0.22/0.53    inference(subsumption_resolution,[],[f251,f124])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(superposition,[],[f76,f94])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f67])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.22/0.53    inference(flattening,[],[f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.22/0.53    inference(nnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.22/0.53  fof(f251,plain,(
% 0.22/0.53    r2_hidden(sK1,k1_xboole_0) | ~spl6_15),
% 0.22/0.53    inference(superposition,[],[f97,f229])).
% 0.22/0.53  fof(f229,plain,(
% 0.22/0.53    k1_xboole_0 = k1_tarski(sK1) | ~spl6_15),
% 0.22/0.53    inference(avatar_component_clause,[],[f227])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.22/0.53    inference(equality_resolution,[],[f96])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.22/0.53    inference(equality_resolution,[],[f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f44])).
% 0.22/0.53  fof(f245,plain,(
% 0.22/0.53    spl6_16 | ~spl6_3 | ~spl6_14),
% 0.22/0.53    inference(avatar_split_clause,[],[f244,f223,f110,f240])).
% 0.22/0.53  fof(f244,plain,(
% 0.22/0.53    sK0 = k1_relat_1(sK3) | (~spl6_3 | ~spl6_14)),
% 0.22/0.53    inference(subsumption_resolution,[],[f236,f112])).
% 0.22/0.53  fof(f236,plain,(
% 0.22/0.53    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~spl6_14),
% 0.22/0.53    inference(superposition,[],[f64,f225])).
% 0.22/0.53  fof(f225,plain,(
% 0.22/0.53    sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) | ~spl6_14),
% 0.22/0.53    inference(avatar_component_clause,[],[f223])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.53  fof(f159,plain,(
% 0.22/0.53    spl6_10 | ~spl6_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f154,f110,f156])).
% 0.22/0.53  fof(f154,plain,(
% 0.22/0.53    v1_relat_1(sK3) | ~spl6_3),
% 0.22/0.53    inference(subsumption_resolution,[],[f153,f79])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.53  fof(f153,plain,(
% 0.22/0.53    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,k1_tarski(sK1))) | ~spl6_3),
% 0.22/0.53    inference(resolution,[],[f77,f112])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    spl6_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f45,f120])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    v1_funct_1(sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 0.22/0.53    inference(flattening,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 0.22/0.53    inference(ennf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.22/0.53    inference(negated_conjecture,[],[f16])).
% 0.22/0.53  fof(f16,conjecture,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    spl6_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f46,f115])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    spl6_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f47,f110])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    spl6_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f48,f105])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    r2_hidden(sK2,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    ~spl6_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f49,f100])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    sK1 != k1_funct_1(sK3,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (11892)------------------------------
% 0.22/0.53  % (11892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (11892)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (11892)Memory used [KB]: 6524
% 0.22/0.53  % (11892)Time elapsed: 0.085 s
% 0.22/0.53  % (11892)------------------------------
% 0.22/0.53  % (11892)------------------------------
% 0.22/0.53  % (11872)Refutation not found, incomplete strategy% (11872)------------------------------
% 0.22/0.53  % (11872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (11872)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (11872)Memory used [KB]: 1663
% 0.22/0.53  % (11872)Time elapsed: 0.114 s
% 0.22/0.53  % (11872)------------------------------
% 0.22/0.53  % (11872)------------------------------
% 0.22/0.53  % (11879)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (11877)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (11876)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (11866)Success in time 0.173 s
%------------------------------------------------------------------------------
