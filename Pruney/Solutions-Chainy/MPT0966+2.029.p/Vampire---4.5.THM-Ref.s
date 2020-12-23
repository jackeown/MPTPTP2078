%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 583 expanded)
%              Number of leaves         :   29 ( 169 expanded)
%              Depth                    :   19
%              Number of atoms          :  506 (2135 expanded)
%              Number of equality atoms :  135 ( 749 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1053,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f314,f316,f577,f580,f607,f834,f930,f1030])).

fof(f1030,plain,
    ( spl9_2
    | spl9_16
    | ~ spl9_17
    | ~ spl9_21 ),
    inference(avatar_contradiction_clause,[],[f1029])).

fof(f1029,plain,
    ( $false
    | spl9_2
    | spl9_16
    | ~ spl9_17
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f1028,f106])).

fof(f106,plain,
    ( k1_xboole_0 != sK4
    | spl9_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl9_2
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f1028,plain,
    ( k1_xboole_0 = sK4
    | spl9_16
    | ~ spl9_17
    | ~ spl9_21 ),
    inference(forward_demodulation,[],[f1012,f376])).

fof(f376,plain,(
    ! [X2,X3] : k1_xboole_0 = k1_relset_1(X2,X3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f370,f193])).

fof(f193,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f59,f177])).

fof(f177,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f176,f64])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( sP0(sK8(X0),X0)
        & r2_hidden(sK8(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f30,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP0(X1,X0)
          & r2_hidden(X1,X0) )
     => ( sP0(sK8(X0),X0)
        & r2_hidden(sK8(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP0(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f21,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ! [X2,X3,X4] :
          ( k3_mcart_1(X2,X3,X4) != X1
          | ( ~ r2_hidden(X3,X0)
            & ~ r2_hidden(X2,X0) ) )
      | ~ sP0(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f176,plain,(
    ! [X3] : ~ r2_hidden(X3,k6_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f174,f57])).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f174,plain,(
    ! [X3] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(X3,k6_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f87,f111])).

fof(f111,plain,(
    m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f58,f92])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f59,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f370,plain,(
    ! [X2,X3] : k1_relat_1(k1_xboole_0) = k1_relset_1(X2,X3,k1_xboole_0) ),
    inference(resolution,[],[f342,f199])).

fof(f199,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    inference(backward_demodulation,[],[f110,f192])).

fof(f192,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f60,f177])).

fof(f60,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f110,plain,(
    ! [X1] : r1_tarski(k2_relat_1(k1_xboole_0),X1) ),
    inference(superposition,[],[f67,f93])).

fof(f93,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).

fof(f342,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(X3,k2_zfmisc_1(X1,X2))
      | k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    inference(resolution,[],[f77,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f1012,plain,
    ( sK4 = k1_relset_1(sK4,k1_xboole_0,k1_xboole_0)
    | spl9_16
    | ~ spl9_17
    | ~ spl9_21 ),
    inference(backward_demodulation,[],[f966,f1005])).

fof(f1005,plain,
    ( k1_xboole_0 = sK7
    | spl9_16
    | ~ spl9_17
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f1004,f199])).

fof(f1004,plain,
    ( ~ r1_tarski(k1_xboole_0,sK7)
    | k1_xboole_0 = sK7
    | spl9_16
    | ~ spl9_17
    | ~ spl9_21 ),
    inference(forward_demodulation,[],[f1003,f92])).

fof(f1003,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK4,k1_xboole_0),sK7)
    | k1_xboole_0 = sK7
    | spl9_16
    | ~ spl9_17
    | ~ spl9_21 ),
    inference(forward_demodulation,[],[f978,f955])).

fof(f955,plain,
    ( k1_xboole_0 = sK6
    | spl9_16
    | ~ spl9_17
    | ~ spl9_21 ),
    inference(resolution,[],[f954,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f954,plain,
    ( sP1(sK4,sK6)
    | spl9_16
    | ~ spl9_17
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f953,f934])).

fof(f934,plain,
    ( sP2(sK4,sK7,sK6)
    | ~ spl9_17 ),
    inference(resolution,[],[f312,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X2,X1,X0)
        & sP2(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f27,f33,f32,f31])).

fof(f32,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP3(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

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

fof(f312,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f311])).

fof(f311,plain,
    ( spl9_17
  <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f953,plain,
    ( sP1(sK4,sK6)
    | ~ sP2(sK4,sK7,sK6)
    | spl9_16
    | ~ spl9_17
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f952,f309])).

fof(f309,plain,
    ( ~ v1_funct_2(sK7,sK4,sK6)
    | spl9_16 ),
    inference(avatar_component_clause,[],[f307])).

fof(f307,plain,
    ( spl9_16
  <=> v1_funct_2(sK7,sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f952,plain,
    ( v1_funct_2(sK7,sK4,sK6)
    | sP1(sK4,sK6)
    | ~ sP2(sK4,sK7,sK6)
    | ~ spl9_17
    | ~ spl9_21 ),
    inference(trivial_inequality_removal,[],[f951])).

fof(f951,plain,
    ( sK4 != sK4
    | v1_funct_2(sK7,sK4,sK6)
    | sP1(sK4,sK6)
    | ~ sP2(sK4,sK7,sK6)
    | ~ spl9_17
    | ~ spl9_21 ),
    inference(superposition,[],[f82,f938])).

fof(f938,plain,
    ( sK4 = k1_relset_1(sK4,sK6,sK7)
    | ~ spl9_17
    | ~ spl9_21 ),
    inference(forward_demodulation,[],[f932,f576])).

fof(f576,plain,
    ( sK4 = k1_relat_1(sK7)
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f574])).

fof(f574,plain,
    ( spl9_21
  <=> sK4 = k1_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f932,plain,
    ( k1_relat_1(sK7) = k1_relset_1(sK4,sK6,sK7)
    | ~ spl9_17 ),
    inference(resolution,[],[f312,f77])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) != X0
      | v1_funct_2(X1,X0,X2)
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f978,plain,
    ( k1_xboole_0 = sK7
    | ~ r1_tarski(k2_zfmisc_1(sK4,sK6),sK7)
    | spl9_16
    | ~ spl9_17
    | ~ spl9_21 ),
    inference(forward_demodulation,[],[f967,f92])).

fof(f967,plain,
    ( sK7 = k2_zfmisc_1(sK4,k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(sK4,sK6),sK7)
    | spl9_16
    | ~ spl9_17
    | ~ spl9_21 ),
    inference(backward_demodulation,[],[f945,f955])).

fof(f945,plain,
    ( sK7 = k2_zfmisc_1(sK4,sK6)
    | ~ r1_tarski(k2_zfmisc_1(sK4,sK6),sK7)
    | ~ spl9_17 ),
    inference(resolution,[],[f937,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f937,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(sK4,sK6))
    | ~ spl9_17 ),
    inference(resolution,[],[f312,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f966,plain,
    ( sK4 = k1_relset_1(sK4,k1_xboole_0,sK7)
    | spl9_16
    | ~ spl9_17
    | ~ spl9_21 ),
    inference(backward_demodulation,[],[f938,f955])).

fof(f930,plain,
    ( spl9_17
    | ~ spl9_21 ),
    inference(avatar_contradiction_clause,[],[f929])).

fof(f929,plain,
    ( $false
    | spl9_17
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f928,f90])).

fof(f90,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f928,plain,
    ( ~ r1_tarski(sK4,sK4)
    | spl9_17
    | ~ spl9_21 ),
    inference(forward_demodulation,[],[f927,f576])).

fof(f927,plain,
    ( ~ r1_tarski(k1_relat_1(sK7),sK4)
    | spl9_17 ),
    inference(subsumption_resolution,[],[f926,f123])).

fof(f123,plain,(
    v1_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f119,f66])).

fof(f66,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f119,plain,
    ( v1_relat_1(sK7)
    | ~ v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(resolution,[],[f61,f53])).

fof(f53,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
      | ~ v1_funct_2(sK7,sK4,sK6)
      | ~ v1_funct_1(sK7) )
    & ( k1_xboole_0 = sK4
      | k1_xboole_0 != sK5 )
    & r1_tarski(k2_relset_1(sK4,sK5,sK7),sK6)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK7,sK4,sK5)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f19,f35])).

fof(f35,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(k2_relset_1(X0,X1,X3),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
        | ~ v1_funct_2(sK7,sK4,sK6)
        | ~ v1_funct_1(sK7) )
      & ( k1_xboole_0 = sK4
        | k1_xboole_0 != sK5 )
      & r1_tarski(k2_relset_1(sK4,sK5,sK7),sK6)
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK7,sK4,sK5)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f926,plain,
    ( ~ r1_tarski(k1_relat_1(sK7),sK4)
    | ~ v1_relat_1(sK7)
    | spl9_17 ),
    inference(subsumption_resolution,[],[f924,f388])).

fof(f388,plain,(
    r1_tarski(k2_relat_1(sK7),sK6) ),
    inference(backward_demodulation,[],[f54,f382])).

fof(f382,plain,(
    k2_relset_1(sK4,sK5,sK7) = k2_relat_1(sK7) ),
    inference(resolution,[],[f78,f53])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f54,plain,(
    r1_tarski(k2_relset_1(sK4,sK5,sK7),sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f924,plain,
    ( ~ r1_tarski(k2_relat_1(sK7),sK6)
    | ~ r1_tarski(k1_relat_1(sK7),sK4)
    | ~ v1_relat_1(sK7)
    | spl9_17 ),
    inference(resolution,[],[f313,f76])).

fof(f76,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f313,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
    | spl9_17 ),
    inference(avatar_component_clause,[],[f311])).

fof(f834,plain,
    ( ~ spl9_2
    | spl9_16 ),
    inference(avatar_contradiction_clause,[],[f831])).

fof(f831,plain,
    ( $false
    | ~ spl9_2
    | spl9_16 ),
    inference(resolution,[],[f830,f615])).

fof(f615,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK6)
    | ~ spl9_2
    | spl9_16 ),
    inference(backward_demodulation,[],[f599,f610])).

fof(f610,plain,
    ( k1_xboole_0 = sK7
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f609,f57])).

fof(f609,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK7
    | ~ spl9_2 ),
    inference(forward_demodulation,[],[f608,f93])).

fof(f608,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK5))
    | k1_xboole_0 = sK7
    | ~ spl9_2 ),
    inference(forward_demodulation,[],[f226,f107])).

fof(f107,plain,
    ( k1_xboole_0 = sK4
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f226,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK4,sK5))
    | k1_xboole_0 = sK7 ),
    inference(resolution,[],[f218,f113])).

fof(f113,plain,(
    r1_tarski(sK7,k2_zfmisc_1(sK4,sK5)) ),
    inference(resolution,[],[f71,f53])).

fof(f218,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ v1_xboole_0(X0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f175,f64])).

fof(f175,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X5,X6)
      | ~ v1_xboole_0(X4)
      | ~ r1_tarski(X6,X4) ) ),
    inference(resolution,[],[f87,f72])).

fof(f599,plain,
    ( ~ v1_funct_2(sK7,k1_xboole_0,sK6)
    | ~ spl9_2
    | spl9_16 ),
    inference(backward_demodulation,[],[f309,f107])).

fof(f830,plain,(
    ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f829,f97])).

fof(f97,plain,(
    ! [X1] : ~ sP1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f829,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | sP1(k1_xboole_0,X0) ) ),
    inference(equality_resolution,[],[f825])).

fof(f825,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != X1
      | v1_funct_2(k1_xboole_0,X1,X2)
      | sP1(X1,X2) ) ),
    inference(subsumption_resolution,[],[f821,f259])).

fof(f259,plain,(
    ! [X2,X3] : sP2(X2,k1_xboole_0,X3) ),
    inference(resolution,[],[f250,f199])).

fof(f250,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X1,X3))
      | sP2(X1,X2,X3) ) ),
    inference(resolution,[],[f85,f72])).

fof(f821,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != X1
      | v1_funct_2(k1_xboole_0,X1,X2)
      | sP1(X1,X2)
      | ~ sP2(X1,k1_xboole_0,X2) ) ),
    inference(superposition,[],[f82,f376])).

fof(f607,plain,
    ( ~ spl9_2
    | ~ spl9_20 ),
    inference(avatar_contradiction_clause,[],[f606])).

fof(f606,plain,
    ( $false
    | ~ spl9_2
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f605,f97])).

fof(f605,plain,
    ( sP1(k1_xboole_0,k1_xboole_0)
    | ~ spl9_2
    | ~ spl9_20 ),
    inference(backward_demodulation,[],[f590,f107])).

fof(f590,plain,
    ( sP1(sK4,k1_xboole_0)
    | ~ spl9_20 ),
    inference(backward_demodulation,[],[f572,f578])).

fof(f578,plain,
    ( k1_xboole_0 = sK5
    | ~ spl9_20 ),
    inference(resolution,[],[f572,f83])).

fof(f572,plain,
    ( sP1(sK4,sK5)
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f570])).

fof(f570,plain,
    ( spl9_20
  <=> sP1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f580,plain,
    ( spl9_1
    | ~ spl9_20 ),
    inference(avatar_contradiction_clause,[],[f579])).

fof(f579,plain,
    ( $false
    | spl9_1
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f578,f103])).

fof(f103,plain,
    ( k1_xboole_0 != sK5
    | spl9_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl9_1
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f577,plain,
    ( spl9_20
    | spl9_21 ),
    inference(avatar_split_clause,[],[f568,f574,f570])).

fof(f568,plain,
    ( sK4 = k1_relat_1(sK7)
    | sP1(sK4,sK5) ),
    inference(forward_demodulation,[],[f567,f340])).

fof(f340,plain,(
    k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
    inference(resolution,[],[f77,f53])).

fof(f567,plain,
    ( sP1(sK4,sK5)
    | sK4 = k1_relset_1(sK4,sK5,sK7) ),
    inference(subsumption_resolution,[],[f561,f52])).

fof(f52,plain,(
    v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f561,plain,
    ( ~ v1_funct_2(sK7,sK4,sK5)
    | sP1(sK4,sK5)
    | sK4 = k1_relset_1(sK4,sK5,sK7) ),
    inference(resolution,[],[f81,f248])).

fof(f248,plain,(
    sP2(sK4,sK7,sK5) ),
    inference(resolution,[],[f85,f53])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | sP1(X0,X2)
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f316,plain,(
    spl9_15 ),
    inference(avatar_contradiction_clause,[],[f315])).

fof(f315,plain,
    ( $false
    | spl9_15 ),
    inference(subsumption_resolution,[],[f305,f51])).

fof(f51,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f36])).

fof(f305,plain,
    ( ~ v1_funct_1(sK7)
    | spl9_15 ),
    inference(avatar_component_clause,[],[f303])).

fof(f303,plain,
    ( spl9_15
  <=> v1_funct_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f314,plain,
    ( ~ spl9_15
    | ~ spl9_16
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f56,f311,f307,f303])).

fof(f56,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
    | ~ v1_funct_2(sK7,sK4,sK6)
    | ~ v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f36])).

fof(f108,plain,
    ( ~ spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f55,f105,f101])).

fof(f55,plain,
    ( k1_xboole_0 = sK4
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:13:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (10767)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (10769)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.49  % (10757)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  % (10761)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.50  % (10777)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (10756)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (10770)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.51  % (10776)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (10754)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (10768)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (10754)Refutation not found, incomplete strategy% (10754)------------------------------
% 0.21/0.52  % (10754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10754)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10754)Memory used [KB]: 10618
% 0.21/0.52  % (10754)Time elapsed: 0.105 s
% 0.21/0.52  % (10754)------------------------------
% 0.21/0.52  % (10754)------------------------------
% 0.21/0.52  % (10766)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (10765)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (10759)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (10762)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (10759)Refutation not found, incomplete strategy% (10759)------------------------------
% 0.21/0.52  % (10759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10759)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10759)Memory used [KB]: 10618
% 0.21/0.52  % (10759)Time elapsed: 0.108 s
% 0.21/0.52  % (10759)------------------------------
% 0.21/0.52  % (10759)------------------------------
% 0.21/0.52  % (10765)Refutation not found, incomplete strategy% (10765)------------------------------
% 0.21/0.52  % (10765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10765)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10765)Memory used [KB]: 10618
% 0.21/0.52  % (10765)Time elapsed: 0.109 s
% 0.21/0.52  % (10765)------------------------------
% 0.21/0.52  % (10765)------------------------------
% 0.21/0.52  % (10755)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (10758)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (10779)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (10758)Refutation not found, incomplete strategy% (10758)------------------------------
% 0.21/0.52  % (10758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10758)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10758)Memory used [KB]: 6140
% 0.21/0.52  % (10758)Time elapsed: 0.116 s
% 0.21/0.52  % (10758)------------------------------
% 0.21/0.52  % (10758)------------------------------
% 0.21/0.52  % (10773)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.53  % (10771)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.53  % (10778)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.53  % (10775)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (10774)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (10763)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.54  % (10753)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.54  % (10764)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.54  % (10772)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.55  % (10779)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f1053,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f108,f314,f316,f577,f580,f607,f834,f930,f1030])).
% 0.21/0.56  fof(f1030,plain,(
% 0.21/0.56    spl9_2 | spl9_16 | ~spl9_17 | ~spl9_21),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f1029])).
% 0.21/0.56  fof(f1029,plain,(
% 0.21/0.56    $false | (spl9_2 | spl9_16 | ~spl9_17 | ~spl9_21)),
% 0.21/0.56    inference(subsumption_resolution,[],[f1028,f106])).
% 0.21/0.56  fof(f106,plain,(
% 0.21/0.56    k1_xboole_0 != sK4 | spl9_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f105])).
% 0.21/0.56  fof(f105,plain,(
% 0.21/0.56    spl9_2 <=> k1_xboole_0 = sK4),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.56  fof(f1028,plain,(
% 0.21/0.56    k1_xboole_0 = sK4 | (spl9_16 | ~spl9_17 | ~spl9_21)),
% 0.21/0.56    inference(forward_demodulation,[],[f1012,f376])).
% 0.21/0.56  fof(f376,plain,(
% 0.21/0.56    ( ! [X2,X3] : (k1_xboole_0 = k1_relset_1(X2,X3,k1_xboole_0)) )),
% 0.21/0.56    inference(forward_demodulation,[],[f370,f193])).
% 0.21/0.56  fof(f193,plain,(
% 0.21/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.56    inference(superposition,[],[f59,f177])).
% 0.21/0.56  fof(f177,plain,(
% 0.21/0.56    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.56    inference(resolution,[],[f176,f64])).
% 0.21/0.56  fof(f64,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK8(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ! [X0] : ((sP0(sK8(X0),X0) & r2_hidden(sK8(X0),X0)) | k1_xboole_0 = X0)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f30,f39])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ! [X0] : (? [X1] : (sP0(X1,X0) & r2_hidden(X1,X0)) => (sP0(sK8(X0),X0) & r2_hidden(sK8(X0),X0)))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ! [X0] : (? [X1] : (sP0(X1,X0) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.56    inference(definition_folding,[],[f21,f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ! [X1,X0] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) | ~sP0(X1,X0))),
% 0.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.57    inference(ennf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,axiom,(
% 0.21/0.57    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).
% 0.21/0.57  fof(f176,plain,(
% 0.21/0.57    ( ! [X3] : (~r2_hidden(X3,k6_relat_1(k1_xboole_0))) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f174,f57])).
% 0.21/0.57  fof(f57,plain,(
% 0.21/0.57    v1_xboole_0(k1_xboole_0)),
% 0.21/0.57    inference(cnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    v1_xboole_0(k1_xboole_0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.57  fof(f174,plain,(
% 0.21/0.57    ( ! [X3] : (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(X3,k6_relat_1(k1_xboole_0))) )),
% 0.21/0.57    inference(resolution,[],[f87,f111])).
% 0.21/0.57  fof(f111,plain,(
% 0.21/0.57    m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.57    inference(superposition,[],[f58,f92])).
% 0.21/0.57  fof(f92,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.57    inference(equality_resolution,[],[f75])).
% 0.21/0.57  fof(f75,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.57    inference(flattening,[],[f44])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.57    inference(nnf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,axiom,(
% 0.21/0.57    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 0.21/0.57  fof(f87,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.57  fof(f59,plain,(
% 0.21/0.57    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.57  fof(f370,plain,(
% 0.21/0.57    ( ! [X2,X3] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X2,X3,k1_xboole_0)) )),
% 0.21/0.57    inference(resolution,[],[f342,f199])).
% 0.21/0.57  fof(f199,plain,(
% 0.21/0.57    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) )),
% 0.21/0.57    inference(backward_demodulation,[],[f110,f192])).
% 0.21/0.57  fof(f192,plain,(
% 0.21/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.57    inference(superposition,[],[f60,f177])).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f9])).
% 0.21/0.57  fof(f110,plain,(
% 0.21/0.57    ( ! [X1] : (r1_tarski(k2_relat_1(k1_xboole_0),X1)) )),
% 0.21/0.57    inference(superposition,[],[f67,f93])).
% 0.21/0.57  fof(f93,plain,(
% 0.21/0.57    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.57    inference(equality_resolution,[],[f74])).
% 0.21/0.57  fof(f74,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f45])).
% 0.21/0.57  fof(f67,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).
% 0.21/0.57  fof(f342,plain,(
% 0.21/0.57    ( ! [X2,X3,X1] : (~r1_tarski(X3,k2_zfmisc_1(X1,X2)) | k1_relset_1(X1,X2,X3) = k1_relat_1(X3)) )),
% 0.21/0.57    inference(resolution,[],[f77,f72])).
% 0.21/0.57  fof(f72,plain,(
% 0.21/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f43])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.57    inference(nnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.57  fof(f77,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.57  fof(f1012,plain,(
% 0.21/0.57    sK4 = k1_relset_1(sK4,k1_xboole_0,k1_xboole_0) | (spl9_16 | ~spl9_17 | ~spl9_21)),
% 0.21/0.57    inference(backward_demodulation,[],[f966,f1005])).
% 0.21/0.57  fof(f1005,plain,(
% 0.21/0.57    k1_xboole_0 = sK7 | (spl9_16 | ~spl9_17 | ~spl9_21)),
% 0.21/0.57    inference(subsumption_resolution,[],[f1004,f199])).
% 0.21/0.57  fof(f1004,plain,(
% 0.21/0.57    ~r1_tarski(k1_xboole_0,sK7) | k1_xboole_0 = sK7 | (spl9_16 | ~spl9_17 | ~spl9_21)),
% 0.21/0.57    inference(forward_demodulation,[],[f1003,f92])).
% 0.21/0.57  fof(f1003,plain,(
% 0.21/0.57    ~r1_tarski(k2_zfmisc_1(sK4,k1_xboole_0),sK7) | k1_xboole_0 = sK7 | (spl9_16 | ~spl9_17 | ~spl9_21)),
% 0.21/0.57    inference(forward_demodulation,[],[f978,f955])).
% 0.21/0.57  fof(f955,plain,(
% 0.21/0.57    k1_xboole_0 = sK6 | (spl9_16 | ~spl9_17 | ~spl9_21)),
% 0.21/0.57    inference(resolution,[],[f954,f83])).
% 0.21/0.57  fof(f83,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~sP1(X0,X1) | k1_xboole_0 = X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f50])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 0.21/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.57  fof(f954,plain,(
% 0.21/0.57    sP1(sK4,sK6) | (spl9_16 | ~spl9_17 | ~spl9_21)),
% 0.21/0.57    inference(subsumption_resolution,[],[f953,f934])).
% 0.21/0.57  fof(f934,plain,(
% 0.21/0.57    sP2(sK4,sK7,sK6) | ~spl9_17),
% 0.21/0.57    inference(resolution,[],[f312,f85])).
% 0.21/0.57  fof(f85,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X0,X2,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((sP3(X2,X1,X0) & sP2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(definition_folding,[],[f27,f33,f32,f31])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 0.21/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP3(X2,X1,X0))),
% 0.21/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(flattening,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.57  fof(f312,plain,(
% 0.21/0.57    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) | ~spl9_17),
% 0.21/0.57    inference(avatar_component_clause,[],[f311])).
% 0.21/0.57  fof(f311,plain,(
% 0.21/0.57    spl9_17 <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 0.21/0.57  fof(f953,plain,(
% 0.21/0.57    sP1(sK4,sK6) | ~sP2(sK4,sK7,sK6) | (spl9_16 | ~spl9_17 | ~spl9_21)),
% 0.21/0.57    inference(subsumption_resolution,[],[f952,f309])).
% 0.21/0.57  fof(f309,plain,(
% 0.21/0.57    ~v1_funct_2(sK7,sK4,sK6) | spl9_16),
% 0.21/0.57    inference(avatar_component_clause,[],[f307])).
% 0.21/0.57  fof(f307,plain,(
% 0.21/0.57    spl9_16 <=> v1_funct_2(sK7,sK4,sK6)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.21/0.57  fof(f952,plain,(
% 0.21/0.57    v1_funct_2(sK7,sK4,sK6) | sP1(sK4,sK6) | ~sP2(sK4,sK7,sK6) | (~spl9_17 | ~spl9_21)),
% 0.21/0.57    inference(trivial_inequality_removal,[],[f951])).
% 0.21/0.57  fof(f951,plain,(
% 0.21/0.57    sK4 != sK4 | v1_funct_2(sK7,sK4,sK6) | sP1(sK4,sK6) | ~sP2(sK4,sK7,sK6) | (~spl9_17 | ~spl9_21)),
% 0.21/0.57    inference(superposition,[],[f82,f938])).
% 0.21/0.57  fof(f938,plain,(
% 0.21/0.57    sK4 = k1_relset_1(sK4,sK6,sK7) | (~spl9_17 | ~spl9_21)),
% 0.21/0.57    inference(forward_demodulation,[],[f932,f576])).
% 0.21/0.57  fof(f576,plain,(
% 0.21/0.57    sK4 = k1_relat_1(sK7) | ~spl9_21),
% 0.21/0.57    inference(avatar_component_clause,[],[f574])).
% 0.21/0.57  fof(f574,plain,(
% 0.21/0.57    spl9_21 <=> sK4 = k1_relat_1(sK7)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 0.21/0.57  fof(f932,plain,(
% 0.21/0.57    k1_relat_1(sK7) = k1_relset_1(sK4,sK6,sK7) | ~spl9_17),
% 0.21/0.57    inference(resolution,[],[f312,f77])).
% 0.21/0.57  fof(f82,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) != X0 | v1_funct_2(X1,X0,X2) | sP1(X0,X2) | ~sP2(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f49])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP1(X0,X2) | ~sP2(X0,X1,X2))),
% 0.21/0.57    inference(rectify,[],[f48])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f32])).
% 0.21/0.57  fof(f978,plain,(
% 0.21/0.57    k1_xboole_0 = sK7 | ~r1_tarski(k2_zfmisc_1(sK4,sK6),sK7) | (spl9_16 | ~spl9_17 | ~spl9_21)),
% 0.21/0.57    inference(forward_demodulation,[],[f967,f92])).
% 0.21/0.57  fof(f967,plain,(
% 0.21/0.57    sK7 = k2_zfmisc_1(sK4,k1_xboole_0) | ~r1_tarski(k2_zfmisc_1(sK4,sK6),sK7) | (spl9_16 | ~spl9_17 | ~spl9_21)),
% 0.21/0.57    inference(backward_demodulation,[],[f945,f955])).
% 0.21/0.57  fof(f945,plain,(
% 0.21/0.57    sK7 = k2_zfmisc_1(sK4,sK6) | ~r1_tarski(k2_zfmisc_1(sK4,sK6),sK7) | ~spl9_17),
% 0.21/0.57    inference(resolution,[],[f937,f70])).
% 0.21/0.57  fof(f70,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f42])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.57    inference(flattening,[],[f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.57  fof(f937,plain,(
% 0.21/0.57    r1_tarski(sK7,k2_zfmisc_1(sK4,sK6)) | ~spl9_17),
% 0.21/0.57    inference(resolution,[],[f312,f71])).
% 0.21/0.57  fof(f71,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f43])).
% 0.21/0.57  fof(f966,plain,(
% 0.21/0.57    sK4 = k1_relset_1(sK4,k1_xboole_0,sK7) | (spl9_16 | ~spl9_17 | ~spl9_21)),
% 0.21/0.57    inference(backward_demodulation,[],[f938,f955])).
% 0.21/0.57  fof(f930,plain,(
% 0.21/0.57    spl9_17 | ~spl9_21),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f929])).
% 0.21/0.57  fof(f929,plain,(
% 0.21/0.57    $false | (spl9_17 | ~spl9_21)),
% 0.21/0.57    inference(subsumption_resolution,[],[f928,f90])).
% 0.21/0.57  fof(f90,plain,(
% 0.21/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.57    inference(equality_resolution,[],[f69])).
% 0.21/0.57  fof(f69,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f42])).
% 0.21/0.57  fof(f928,plain,(
% 0.21/0.57    ~r1_tarski(sK4,sK4) | (spl9_17 | ~spl9_21)),
% 0.21/0.57    inference(forward_demodulation,[],[f927,f576])).
% 0.21/0.57  fof(f927,plain,(
% 0.21/0.57    ~r1_tarski(k1_relat_1(sK7),sK4) | spl9_17),
% 0.21/0.57    inference(subsumption_resolution,[],[f926,f123])).
% 0.21/0.57  fof(f123,plain,(
% 0.21/0.57    v1_relat_1(sK7)),
% 0.21/0.57    inference(subsumption_resolution,[],[f119,f66])).
% 0.21/0.57  fof(f66,plain,(
% 0.21/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.57  fof(f119,plain,(
% 0.21/0.57    v1_relat_1(sK7) | ~v1_relat_1(k2_zfmisc_1(sK4,sK5))),
% 0.21/0.57    inference(resolution,[],[f61,f53])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 0.21/0.57    inference(cnf_transformation,[],[f36])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    (~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) | ~v1_funct_2(sK7,sK4,sK6) | ~v1_funct_1(sK7)) & (k1_xboole_0 = sK4 | k1_xboole_0 != sK5) & r1_tarski(k2_relset_1(sK4,sK5,sK7),sK6) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f19,f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) | ~v1_funct_2(sK7,sK4,sK6) | ~v1_funct_1(sK7)) & (k1_xboole_0 = sK4 | k1_xboole_0 != sK5) & r1_tarski(k2_relset_1(sK4,sK5,sK7),sK6) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.57    inference(flattening,[],[f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.57    inference(ennf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.57    inference(negated_conjecture,[],[f16])).
% 0.21/0.57  fof(f16,conjecture,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.57  fof(f926,plain,(
% 0.21/0.57    ~r1_tarski(k1_relat_1(sK7),sK4) | ~v1_relat_1(sK7) | spl9_17),
% 0.21/0.57    inference(subsumption_resolution,[],[f924,f388])).
% 0.21/0.57  fof(f388,plain,(
% 0.21/0.57    r1_tarski(k2_relat_1(sK7),sK6)),
% 0.21/0.57    inference(backward_demodulation,[],[f54,f382])).
% 0.21/0.57  fof(f382,plain,(
% 0.21/0.57    k2_relset_1(sK4,sK5,sK7) = k2_relat_1(sK7)),
% 0.21/0.57    inference(resolution,[],[f78,f53])).
% 0.21/0.57  fof(f78,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    r1_tarski(k2_relset_1(sK4,sK5,sK7),sK6)),
% 0.21/0.57    inference(cnf_transformation,[],[f36])).
% 0.21/0.57  fof(f924,plain,(
% 0.21/0.57    ~r1_tarski(k2_relat_1(sK7),sK6) | ~r1_tarski(k1_relat_1(sK7),sK4) | ~v1_relat_1(sK7) | spl9_17),
% 0.21/0.57    inference(resolution,[],[f313,f76])).
% 0.21/0.57  fof(f76,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.57    inference(flattening,[],[f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.57    inference(ennf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.57  fof(f313,plain,(
% 0.21/0.57    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) | spl9_17),
% 0.21/0.57    inference(avatar_component_clause,[],[f311])).
% 0.21/0.57  fof(f834,plain,(
% 0.21/0.57    ~spl9_2 | spl9_16),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f831])).
% 0.21/0.57  fof(f831,plain,(
% 0.21/0.57    $false | (~spl9_2 | spl9_16)),
% 0.21/0.57    inference(resolution,[],[f830,f615])).
% 0.21/0.57  fof(f615,plain,(
% 0.21/0.57    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK6) | (~spl9_2 | spl9_16)),
% 0.21/0.57    inference(backward_demodulation,[],[f599,f610])).
% 0.21/0.57  fof(f610,plain,(
% 0.21/0.57    k1_xboole_0 = sK7 | ~spl9_2),
% 0.21/0.57    inference(subsumption_resolution,[],[f609,f57])).
% 0.21/0.57  fof(f609,plain,(
% 0.21/0.57    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK7 | ~spl9_2),
% 0.21/0.57    inference(forward_demodulation,[],[f608,f93])).
% 0.21/0.57  fof(f608,plain,(
% 0.21/0.57    ~v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK5)) | k1_xboole_0 = sK7 | ~spl9_2),
% 0.21/0.57    inference(forward_demodulation,[],[f226,f107])).
% 0.21/0.57  fof(f107,plain,(
% 0.21/0.57    k1_xboole_0 = sK4 | ~spl9_2),
% 0.21/0.57    inference(avatar_component_clause,[],[f105])).
% 0.21/0.57  fof(f226,plain,(
% 0.21/0.57    ~v1_xboole_0(k2_zfmisc_1(sK4,sK5)) | k1_xboole_0 = sK7),
% 0.21/0.57    inference(resolution,[],[f218,f113])).
% 0.21/0.57  fof(f113,plain,(
% 0.21/0.57    r1_tarski(sK7,k2_zfmisc_1(sK4,sK5))),
% 0.21/0.57    inference(resolution,[],[f71,f53])).
% 0.21/0.57  fof(f218,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~v1_xboole_0(X0) | k1_xboole_0 = X1) )),
% 0.21/0.57    inference(resolution,[],[f175,f64])).
% 0.21/0.57  fof(f175,plain,(
% 0.21/0.57    ( ! [X6,X4,X5] : (~r2_hidden(X5,X6) | ~v1_xboole_0(X4) | ~r1_tarski(X6,X4)) )),
% 0.21/0.57    inference(resolution,[],[f87,f72])).
% 0.21/0.57  fof(f599,plain,(
% 0.21/0.57    ~v1_funct_2(sK7,k1_xboole_0,sK6) | (~spl9_2 | spl9_16)),
% 0.21/0.57    inference(backward_demodulation,[],[f309,f107])).
% 0.21/0.57  fof(f830,plain,(
% 0.21/0.57    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f829,f97])).
% 0.21/0.57  fof(f97,plain,(
% 0.21/0.57    ( ! [X1] : (~sP1(k1_xboole_0,X1)) )),
% 0.21/0.57    inference(equality_resolution,[],[f84])).
% 0.21/0.57  fof(f84,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~sP1(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f50])).
% 0.21/0.57  fof(f829,plain,(
% 0.21/0.57    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | sP1(k1_xboole_0,X0)) )),
% 0.21/0.57    inference(equality_resolution,[],[f825])).
% 0.21/0.57  fof(f825,plain,(
% 0.21/0.57    ( ! [X2,X1] : (k1_xboole_0 != X1 | v1_funct_2(k1_xboole_0,X1,X2) | sP1(X1,X2)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f821,f259])).
% 0.21/0.57  fof(f259,plain,(
% 0.21/0.57    ( ! [X2,X3] : (sP2(X2,k1_xboole_0,X3)) )),
% 0.21/0.57    inference(resolution,[],[f250,f199])).
% 0.21/0.57  fof(f250,plain,(
% 0.21/0.57    ( ! [X2,X3,X1] : (~r1_tarski(X2,k2_zfmisc_1(X1,X3)) | sP2(X1,X2,X3)) )),
% 0.21/0.57    inference(resolution,[],[f85,f72])).
% 0.21/0.57  fof(f821,plain,(
% 0.21/0.57    ( ! [X2,X1] : (k1_xboole_0 != X1 | v1_funct_2(k1_xboole_0,X1,X2) | sP1(X1,X2) | ~sP2(X1,k1_xboole_0,X2)) )),
% 0.21/0.57    inference(superposition,[],[f82,f376])).
% 0.21/0.57  fof(f607,plain,(
% 0.21/0.57    ~spl9_2 | ~spl9_20),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f606])).
% 0.21/0.57  fof(f606,plain,(
% 0.21/0.57    $false | (~spl9_2 | ~spl9_20)),
% 0.21/0.57    inference(subsumption_resolution,[],[f605,f97])).
% 0.21/0.57  fof(f605,plain,(
% 0.21/0.57    sP1(k1_xboole_0,k1_xboole_0) | (~spl9_2 | ~spl9_20)),
% 0.21/0.57    inference(backward_demodulation,[],[f590,f107])).
% 0.21/0.57  fof(f590,plain,(
% 0.21/0.57    sP1(sK4,k1_xboole_0) | ~spl9_20),
% 0.21/0.57    inference(backward_demodulation,[],[f572,f578])).
% 0.21/0.57  fof(f578,plain,(
% 0.21/0.57    k1_xboole_0 = sK5 | ~spl9_20),
% 0.21/0.57    inference(resolution,[],[f572,f83])).
% 0.21/0.57  fof(f572,plain,(
% 0.21/0.57    sP1(sK4,sK5) | ~spl9_20),
% 0.21/0.57    inference(avatar_component_clause,[],[f570])).
% 0.21/0.57  fof(f570,plain,(
% 0.21/0.57    spl9_20 <=> sP1(sK4,sK5)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 0.21/0.57  fof(f580,plain,(
% 0.21/0.57    spl9_1 | ~spl9_20),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f579])).
% 0.21/0.57  fof(f579,plain,(
% 0.21/0.57    $false | (spl9_1 | ~spl9_20)),
% 0.21/0.57    inference(subsumption_resolution,[],[f578,f103])).
% 0.21/0.57  fof(f103,plain,(
% 0.21/0.57    k1_xboole_0 != sK5 | spl9_1),
% 0.21/0.57    inference(avatar_component_clause,[],[f101])).
% 0.21/0.57  fof(f101,plain,(
% 0.21/0.57    spl9_1 <=> k1_xboole_0 = sK5),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.57  fof(f577,plain,(
% 0.21/0.57    spl9_20 | spl9_21),
% 0.21/0.57    inference(avatar_split_clause,[],[f568,f574,f570])).
% 0.21/0.57  fof(f568,plain,(
% 0.21/0.57    sK4 = k1_relat_1(sK7) | sP1(sK4,sK5)),
% 0.21/0.57    inference(forward_demodulation,[],[f567,f340])).
% 0.21/0.57  fof(f340,plain,(
% 0.21/0.57    k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7)),
% 0.21/0.57    inference(resolution,[],[f77,f53])).
% 0.21/0.57  fof(f567,plain,(
% 0.21/0.57    sP1(sK4,sK5) | sK4 = k1_relset_1(sK4,sK5,sK7)),
% 0.21/0.57    inference(subsumption_resolution,[],[f561,f52])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    v1_funct_2(sK7,sK4,sK5)),
% 0.21/0.57    inference(cnf_transformation,[],[f36])).
% 0.21/0.57  fof(f561,plain,(
% 0.21/0.57    ~v1_funct_2(sK7,sK4,sK5) | sP1(sK4,sK5) | sK4 = k1_relset_1(sK4,sK5,sK7)),
% 0.21/0.57    inference(resolution,[],[f81,f248])).
% 0.21/0.57  fof(f248,plain,(
% 0.21/0.57    sP2(sK4,sK7,sK5)),
% 0.21/0.57    inference(resolution,[],[f85,f53])).
% 0.21/0.57  fof(f81,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | sP1(X0,X2) | k1_relset_1(X0,X2,X1) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f49])).
% 0.21/0.57  fof(f316,plain,(
% 0.21/0.57    spl9_15),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f315])).
% 0.21/0.57  fof(f315,plain,(
% 0.21/0.57    $false | spl9_15),
% 0.21/0.57    inference(subsumption_resolution,[],[f305,f51])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    v1_funct_1(sK7)),
% 0.21/0.57    inference(cnf_transformation,[],[f36])).
% 0.21/0.57  fof(f305,plain,(
% 0.21/0.57    ~v1_funct_1(sK7) | spl9_15),
% 0.21/0.57    inference(avatar_component_clause,[],[f303])).
% 0.21/0.57  fof(f303,plain,(
% 0.21/0.57    spl9_15 <=> v1_funct_1(sK7)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.21/0.57  fof(f314,plain,(
% 0.21/0.57    ~spl9_15 | ~spl9_16 | ~spl9_17),
% 0.21/0.57    inference(avatar_split_clause,[],[f56,f311,f307,f303])).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) | ~v1_funct_2(sK7,sK4,sK6) | ~v1_funct_1(sK7)),
% 0.21/0.57    inference(cnf_transformation,[],[f36])).
% 0.21/0.57  fof(f108,plain,(
% 0.21/0.57    ~spl9_1 | spl9_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f55,f105,f101])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    k1_xboole_0 = sK4 | k1_xboole_0 != sK5),
% 0.21/0.57    inference(cnf_transformation,[],[f36])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (10779)------------------------------
% 0.21/0.57  % (10779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (10779)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (10779)Memory used [KB]: 11129
% 0.21/0.57  % (10779)Time elapsed: 0.137 s
% 0.21/0.57  % (10779)------------------------------
% 0.21/0.57  % (10779)------------------------------
% 0.21/0.57  % (10750)Success in time 0.208 s
%------------------------------------------------------------------------------
