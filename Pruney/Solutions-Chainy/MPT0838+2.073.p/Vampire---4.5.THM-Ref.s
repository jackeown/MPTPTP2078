%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 208 expanded)
%              Number of leaves         :   34 (  86 expanded)
%              Depth                    :   10
%              Number of atoms          :  355 ( 599 expanded)
%              Number of equality atoms :   74 ( 118 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f317,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f91,f104,f127,f144,f156,f179,f185,f194,f208,f260,f283,f301,f316])).

fof(f316,plain,
    ( ~ spl4_5
    | spl4_13
    | ~ spl4_20
    | ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f315])).

fof(f315,plain,
    ( $false
    | ~ spl4_5
    | spl4_13
    | ~ spl4_20
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f314,f184])).

fof(f184,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl4_13
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f314,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_5
    | ~ spl4_20
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f313,f49])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f313,plain,
    ( k1_relat_1(sK2) = k5_xboole_0(k1_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl4_5
    | ~ spl4_20
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f312,f259])).

fof(f259,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl4_20
  <=> sK2 = k7_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f312,plain,
    ( k1_relat_1(sK2) = k5_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK0)))
    | ~ spl4_5
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f306,f129])).

fof(f129,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK2,X0)) = k3_xboole_0(k1_relat_1(sK2),X0)
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f103,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f103,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl4_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f306,plain,
    ( k1_relat_1(sK2) = k5_xboole_0(k1_relat_1(sK2),k3_xboole_0(k1_relat_1(sK2),sK0))
    | ~ spl4_22 ),
    inference(resolution,[],[f300,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f61,f53])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f300,plain,
    ( r1_xboole_0(k1_relat_1(sK2),sK0)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl4_22
  <=> r1_xboole_0(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f301,plain,
    ( spl4_22
    | ~ spl4_5
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f285,f280,f101,f298])).

fof(f280,plain,
    ( spl4_21
  <=> k1_xboole_0 = k9_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f285,plain,
    ( r1_xboole_0(k1_relat_1(sK2),sK0)
    | ~ spl4_5
    | ~ spl4_21 ),
    inference(unit_resulting_resolution,[],[f103,f282,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f282,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,sK0)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f280])).

fof(f283,plain,
    ( spl4_21
    | ~ spl4_5
    | ~ spl4_15
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f271,f257,f191,f101,f280])).

fof(f191,plain,
    ( spl4_15
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f271,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,sK0)
    | ~ spl4_5
    | ~ spl4_15
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f270,f193])).

fof(f193,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f191])).

fof(f270,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK0)
    | ~ spl4_5
    | ~ spl4_20 ),
    inference(superposition,[],[f114,f259])).

fof(f114,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f103,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f260,plain,
    ( spl4_20
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f150,f124,f101,f257])).

fof(f124,plain,
    ( spl4_6
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f150,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f103,f126,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f126,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f124])).

fof(f208,plain,
    ( ~ spl4_8
    | spl4_14
    | spl4_15 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | ~ spl4_8
    | spl4_14
    | spl4_15 ),
    inference(subsumption_resolution,[],[f204,f195])).

fof(f195,plain,
    ( r2_hidden(sK3(k2_relat_1(sK2)),k2_relat_1(sK2))
    | spl4_15 ),
    inference(unit_resulting_resolution,[],[f192,f51])).

fof(f51,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f192,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f191])).

fof(f204,plain,
    ( ~ r2_hidden(sK3(k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl4_8
    | spl4_14 ),
    inference(unit_resulting_resolution,[],[f189,f155,f122])).

fof(f122,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(X3,X2)
      | ~ r2_hidden(X1,X3)
      | m1_subset_1(X1,X2) ) ),
    inference(resolution,[],[f69,f64])).

fof(f64,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f155,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl4_8
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f189,plain,
    ( ~ m1_subset_1(sK3(k2_relat_1(sK2)),sK1)
    | spl4_14 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl4_14
  <=> m1_subset_1(sK3(k2_relat_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f194,plain,
    ( ~ spl4_14
    | spl4_15
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f139,f83,f191,f187])).

fof(f83,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f139,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK3(k2_relat_1(sK2)),sK1)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f137,f134])).

fof(f134,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f85,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f85,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f137,plain,
    ( ~ m1_subset_1(sK3(k2_relat_1(sK2)),sK1)
    | k1_xboole_0 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f93,f134])).

fof(f93,plain,
    ( k1_xboole_0 = k2_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK3(k2_relset_1(sK0,sK1,sK2)),sK1) ),
    inference(resolution,[],[f51,f48])).

fof(f48,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
        | ~ m1_subset_1(X3,sK1) )
    & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f36,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                    | ~ m1_subset_1(X3,X1) )
                & k1_xboole_0 != k1_relset_1(X0,X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(sK0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(sK0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( ~ r2_hidden(X3,k2_relset_1(sK0,X1,X2))
                | ~ m1_subset_1(X3,X1) )
            & k1_xboole_0 != k1_relset_1(sK0,X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,X2))
              | ~ m1_subset_1(X3,sK1) )
          & k1_xboole_0 != k1_relset_1(sK0,sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,X2))
            | ~ m1_subset_1(X3,sK1) )
        & k1_xboole_0 != k1_relset_1(sK0,sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
   => ( ! [X3] :
          ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
          | ~ m1_subset_1(X3,sK1) )
      & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                    & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                  & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

fof(f185,plain,
    ( ~ spl4_13
    | spl4_4
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f180,f176,f88,f182])).

fof(f88,plain,
    ( spl4_4
  <=> k1_xboole_0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f176,plain,
    ( spl4_12
  <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f180,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl4_4
    | ~ spl4_12 ),
    inference(superposition,[],[f90,f178])).

fof(f178,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f176])).

fof(f90,plain,
    ( k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f179,plain,
    ( spl4_12
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f146,f83,f176])).

fof(f146,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f85,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f156,plain,
    ( spl4_8
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f151,f141,f101,f153])).

fof(f141,plain,
    ( spl4_7
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f151,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f103,f143,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f143,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f141])).

fof(f144,plain,
    ( spl4_7
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f109,f83,f141])).

fof(f109,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f85,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f127,plain,
    ( spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f106,f83,f124])).

fof(f106,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f85,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f104,plain,
    ( spl4_5
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f97,f83,f101])).

fof(f97,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f52,f85,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f52,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f91,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f47,f88])).

fof(f47,plain,(
    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f86,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f46,f83])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.41  % (1856)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.42  % (1856)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f317,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(avatar_sat_refutation,[],[f86,f91,f104,f127,f144,f156,f179,f185,f194,f208,f260,f283,f301,f316])).
% 0.22/0.42  fof(f316,plain,(
% 0.22/0.42    ~spl4_5 | spl4_13 | ~spl4_20 | ~spl4_22),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f315])).
% 0.22/0.42  fof(f315,plain,(
% 0.22/0.42    $false | (~spl4_5 | spl4_13 | ~spl4_20 | ~spl4_22)),
% 0.22/0.42    inference(subsumption_resolution,[],[f314,f184])).
% 0.22/0.42  fof(f184,plain,(
% 0.22/0.42    k1_xboole_0 != k1_relat_1(sK2) | spl4_13),
% 0.22/0.42    inference(avatar_component_clause,[],[f182])).
% 0.22/0.42  fof(f182,plain,(
% 0.22/0.42    spl4_13 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.42  fof(f314,plain,(
% 0.22/0.42    k1_xboole_0 = k1_relat_1(sK2) | (~spl4_5 | ~spl4_20 | ~spl4_22)),
% 0.22/0.42    inference(forward_demodulation,[],[f313,f49])).
% 0.22/0.42  fof(f49,plain,(
% 0.22/0.42    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f4])).
% 0.22/0.42  fof(f4,axiom,(
% 0.22/0.42    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.42  fof(f313,plain,(
% 0.22/0.42    k1_relat_1(sK2) = k5_xboole_0(k1_relat_1(sK2),k1_relat_1(sK2)) | (~spl4_5 | ~spl4_20 | ~spl4_22)),
% 0.22/0.42    inference(forward_demodulation,[],[f312,f259])).
% 0.22/0.42  fof(f259,plain,(
% 0.22/0.42    sK2 = k7_relat_1(sK2,sK0) | ~spl4_20),
% 0.22/0.42    inference(avatar_component_clause,[],[f257])).
% 0.22/0.42  fof(f257,plain,(
% 0.22/0.42    spl4_20 <=> sK2 = k7_relat_1(sK2,sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.22/0.42  fof(f312,plain,(
% 0.22/0.42    k1_relat_1(sK2) = k5_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK0))) | (~spl4_5 | ~spl4_22)),
% 0.22/0.42    inference(forward_demodulation,[],[f306,f129])).
% 0.22/0.42  fof(f129,plain,(
% 0.22/0.42    ( ! [X0] : (k1_relat_1(k7_relat_1(sK2,X0)) = k3_xboole_0(k1_relat_1(sK2),X0)) ) | ~spl4_5),
% 0.22/0.42    inference(unit_resulting_resolution,[],[f103,f55])).
% 0.22/0.42  fof(f55,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f24])).
% 0.22/0.42  fof(f24,plain,(
% 0.22/0.42    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f13])).
% 0.22/0.42  fof(f13,axiom,(
% 0.22/0.42    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.22/0.42  fof(f103,plain,(
% 0.22/0.42    v1_relat_1(sK2) | ~spl4_5),
% 0.22/0.42    inference(avatar_component_clause,[],[f101])).
% 0.22/0.42  fof(f101,plain,(
% 0.22/0.42    spl4_5 <=> v1_relat_1(sK2)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.42  fof(f306,plain,(
% 0.22/0.42    k1_relat_1(sK2) = k5_xboole_0(k1_relat_1(sK2),k3_xboole_0(k1_relat_1(sK2),sK0)) | ~spl4_22),
% 0.22/0.42    inference(resolution,[],[f300,f71])).
% 0.22/0.42  fof(f71,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.22/0.42    inference(definition_unfolding,[],[f61,f53])).
% 0.22/0.42  fof(f53,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.42  fof(f61,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f42])).
% 0.22/0.42  fof(f42,plain,(
% 0.22/0.42    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.42    inference(nnf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.42  fof(f300,plain,(
% 0.22/0.42    r1_xboole_0(k1_relat_1(sK2),sK0) | ~spl4_22),
% 0.22/0.42    inference(avatar_component_clause,[],[f298])).
% 0.22/0.42  fof(f298,plain,(
% 0.22/0.42    spl4_22 <=> r1_xboole_0(k1_relat_1(sK2),sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.22/0.42  fof(f301,plain,(
% 0.22/0.42    spl4_22 | ~spl4_5 | ~spl4_21),
% 0.22/0.42    inference(avatar_split_clause,[],[f285,f280,f101,f298])).
% 0.22/0.42  fof(f280,plain,(
% 0.22/0.42    spl4_21 <=> k1_xboole_0 = k9_relat_1(sK2,sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.22/0.42  fof(f285,plain,(
% 0.22/0.42    r1_xboole_0(k1_relat_1(sK2),sK0) | (~spl4_5 | ~spl4_21)),
% 0.22/0.42    inference(unit_resulting_resolution,[],[f103,f282,f58])).
% 0.22/0.42  fof(f58,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f41])).
% 0.22/0.42  fof(f41,plain,(
% 0.22/0.42    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.42    inference(nnf_transformation,[],[f26])).
% 0.22/0.42  fof(f26,plain,(
% 0.22/0.42    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f11])).
% 0.22/0.42  fof(f11,axiom,(
% 0.22/0.42    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 0.22/0.42  fof(f282,plain,(
% 0.22/0.42    k1_xboole_0 = k9_relat_1(sK2,sK0) | ~spl4_21),
% 0.22/0.42    inference(avatar_component_clause,[],[f280])).
% 0.22/0.42  fof(f283,plain,(
% 0.22/0.42    spl4_21 | ~spl4_5 | ~spl4_15 | ~spl4_20),
% 0.22/0.42    inference(avatar_split_clause,[],[f271,f257,f191,f101,f280])).
% 0.22/0.42  fof(f191,plain,(
% 0.22/0.42    spl4_15 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.42  fof(f271,plain,(
% 0.22/0.42    k1_xboole_0 = k9_relat_1(sK2,sK0) | (~spl4_5 | ~spl4_15 | ~spl4_20)),
% 0.22/0.42    inference(forward_demodulation,[],[f270,f193])).
% 0.22/0.42  fof(f193,plain,(
% 0.22/0.42    k1_xboole_0 = k2_relat_1(sK2) | ~spl4_15),
% 0.22/0.42    inference(avatar_component_clause,[],[f191])).
% 0.22/0.42  fof(f270,plain,(
% 0.22/0.42    k2_relat_1(sK2) = k9_relat_1(sK2,sK0) | (~spl4_5 | ~spl4_20)),
% 0.22/0.42    inference(superposition,[],[f114,f259])).
% 0.22/0.42  fof(f114,plain,(
% 0.22/0.42    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) ) | ~spl4_5),
% 0.22/0.42    inference(unit_resulting_resolution,[],[f103,f54])).
% 0.22/0.42  fof(f54,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f23])).
% 0.22/0.42  fof(f23,plain,(
% 0.22/0.42    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f10])).
% 0.22/0.42  fof(f10,axiom,(
% 0.22/0.42    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.42  fof(f260,plain,(
% 0.22/0.42    spl4_20 | ~spl4_5 | ~spl4_6),
% 0.22/0.42    inference(avatar_split_clause,[],[f150,f124,f101,f257])).
% 0.22/0.42  fof(f124,plain,(
% 0.22/0.42    spl4_6 <=> v4_relat_1(sK2,sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.42  fof(f150,plain,(
% 0.22/0.42    sK2 = k7_relat_1(sK2,sK0) | (~spl4_5 | ~spl4_6)),
% 0.22/0.42    inference(unit_resulting_resolution,[],[f103,f126,f60])).
% 0.22/0.42  fof(f60,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.22/0.42    inference(cnf_transformation,[],[f28])).
% 0.22/0.42  fof(f28,plain,(
% 0.22/0.42    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.42    inference(flattening,[],[f27])).
% 0.22/0.42  fof(f27,plain,(
% 0.22/0.42    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.42    inference(ennf_transformation,[],[f12])).
% 0.22/0.42  fof(f12,axiom,(
% 0.22/0.42    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.42  fof(f126,plain,(
% 0.22/0.42    v4_relat_1(sK2,sK0) | ~spl4_6),
% 0.22/0.42    inference(avatar_component_clause,[],[f124])).
% 0.22/0.42  fof(f208,plain,(
% 0.22/0.42    ~spl4_8 | spl4_14 | spl4_15),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f207])).
% 0.22/0.42  fof(f207,plain,(
% 0.22/0.42    $false | (~spl4_8 | spl4_14 | spl4_15)),
% 0.22/0.42    inference(subsumption_resolution,[],[f204,f195])).
% 0.22/0.42  fof(f195,plain,(
% 0.22/0.42    r2_hidden(sK3(k2_relat_1(sK2)),k2_relat_1(sK2)) | spl4_15),
% 0.22/0.42    inference(unit_resulting_resolution,[],[f192,f51])).
% 0.22/0.42  fof(f51,plain,(
% 0.22/0.42    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.42    inference(cnf_transformation,[],[f39])).
% 0.22/0.42  fof(f39,plain,(
% 0.22/0.42    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f38])).
% 0.22/0.42  fof(f38,plain,(
% 0.22/0.42    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f22,plain,(
% 0.22/0.42    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.42    inference(ennf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.42  fof(f192,plain,(
% 0.22/0.42    k1_xboole_0 != k2_relat_1(sK2) | spl4_15),
% 0.22/0.42    inference(avatar_component_clause,[],[f191])).
% 0.22/0.42  fof(f204,plain,(
% 0.22/0.42    ~r2_hidden(sK3(k2_relat_1(sK2)),k2_relat_1(sK2)) | (~spl4_8 | spl4_14)),
% 0.22/0.42    inference(unit_resulting_resolution,[],[f189,f155,f122])).
% 0.22/0.42  fof(f122,plain,(
% 0.22/0.42    ( ! [X2,X3,X1] : (~r1_tarski(X3,X2) | ~r2_hidden(X1,X3) | m1_subset_1(X1,X2)) )),
% 0.22/0.42    inference(resolution,[],[f69,f64])).
% 0.22/0.42  fof(f64,plain,(
% 0.22/0.42    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f43])).
% 0.22/0.42  fof(f43,plain,(
% 0.22/0.42    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.42    inference(nnf_transformation,[],[f5])).
% 0.22/0.42  fof(f5,axiom,(
% 0.22/0.42    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.42  fof(f69,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f33])).
% 0.22/0.42  fof(f33,plain,(
% 0.22/0.42    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.42    inference(flattening,[],[f32])).
% 0.22/0.42  fof(f32,plain,(
% 0.22/0.42    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.42    inference(ennf_transformation,[],[f6])).
% 0.22/0.42  fof(f6,axiom,(
% 0.22/0.42    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.42  fof(f155,plain,(
% 0.22/0.42    r1_tarski(k2_relat_1(sK2),sK1) | ~spl4_8),
% 0.22/0.42    inference(avatar_component_clause,[],[f153])).
% 0.22/0.42  fof(f153,plain,(
% 0.22/0.42    spl4_8 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.42  fof(f189,plain,(
% 0.22/0.42    ~m1_subset_1(sK3(k2_relat_1(sK2)),sK1) | spl4_14),
% 0.22/0.42    inference(avatar_component_clause,[],[f187])).
% 0.22/0.42  fof(f187,plain,(
% 0.22/0.42    spl4_14 <=> m1_subset_1(sK3(k2_relat_1(sK2)),sK1)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.42  fof(f194,plain,(
% 0.22/0.42    ~spl4_14 | spl4_15 | ~spl4_3),
% 0.22/0.42    inference(avatar_split_clause,[],[f139,f83,f191,f187])).
% 0.22/0.42  fof(f83,plain,(
% 0.22/0.42    spl4_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.42  fof(f139,plain,(
% 0.22/0.42    k1_xboole_0 = k2_relat_1(sK2) | ~m1_subset_1(sK3(k2_relat_1(sK2)),sK1) | ~spl4_3),
% 0.22/0.42    inference(forward_demodulation,[],[f137,f134])).
% 0.22/0.42  fof(f134,plain,(
% 0.22/0.42    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl4_3),
% 0.22/0.42    inference(unit_resulting_resolution,[],[f85,f65])).
% 0.22/0.42  fof(f65,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f29])).
% 0.22/0.42  fof(f29,plain,(
% 0.22/0.42    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.42    inference(ennf_transformation,[],[f16])).
% 0.22/0.42  fof(f16,axiom,(
% 0.22/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.42  fof(f85,plain,(
% 0.22/0.42    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_3),
% 0.22/0.42    inference(avatar_component_clause,[],[f83])).
% 0.22/0.42  fof(f137,plain,(
% 0.22/0.42    ~m1_subset_1(sK3(k2_relat_1(sK2)),sK1) | k1_xboole_0 = k2_relset_1(sK0,sK1,sK2) | ~spl4_3),
% 0.22/0.42    inference(backward_demodulation,[],[f93,f134])).
% 0.22/0.42  fof(f93,plain,(
% 0.22/0.42    k1_xboole_0 = k2_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK3(k2_relset_1(sK0,sK1,sK2)),sK1)),
% 0.22/0.42    inference(resolution,[],[f51,f48])).
% 0.22/0.42  fof(f48,plain,(
% 0.22/0.42    ( ! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f37])).
% 0.22/0.42  fof(f37,plain,(
% 0.22/0.42    ((! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f36,f35,f34])).
% 0.22/0.42  fof(f34,plain,(
% 0.22/0.42    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(sK0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f35,plain,(
% 0.22/0.42    ? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(sK0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) & ~v1_xboole_0(X1)) => (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,X2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) & ~v1_xboole_0(sK1))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f36,plain,(
% 0.22/0.42    ? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,X2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) => (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.42    inference(flattening,[],[f19])).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f18])).
% 0.22/0.42  fof(f18,negated_conjecture,(
% 0.22/0.42    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.22/0.42    inference(negated_conjecture,[],[f17])).
% 0.22/0.42  fof(f17,conjecture,(
% 0.22/0.42    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).
% 0.22/0.42  fof(f185,plain,(
% 0.22/0.42    ~spl4_13 | spl4_4 | ~spl4_12),
% 0.22/0.42    inference(avatar_split_clause,[],[f180,f176,f88,f182])).
% 0.22/0.42  fof(f88,plain,(
% 0.22/0.42    spl4_4 <=> k1_xboole_0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.42  fof(f176,plain,(
% 0.22/0.42    spl4_12 <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.42  fof(f180,plain,(
% 0.22/0.42    k1_xboole_0 != k1_relat_1(sK2) | (spl4_4 | ~spl4_12)),
% 0.22/0.42    inference(superposition,[],[f90,f178])).
% 0.22/0.42  fof(f178,plain,(
% 0.22/0.42    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl4_12),
% 0.22/0.42    inference(avatar_component_clause,[],[f176])).
% 0.22/0.42  fof(f90,plain,(
% 0.22/0.42    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) | spl4_4),
% 0.22/0.42    inference(avatar_component_clause,[],[f88])).
% 0.22/0.42  fof(f179,plain,(
% 0.22/0.42    spl4_12 | ~spl4_3),
% 0.22/0.42    inference(avatar_split_clause,[],[f146,f83,f176])).
% 0.22/0.42  fof(f146,plain,(
% 0.22/0.42    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl4_3),
% 0.22/0.42    inference(unit_resulting_resolution,[],[f85,f66])).
% 0.22/0.42  fof(f66,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f30])).
% 0.22/0.42  fof(f30,plain,(
% 0.22/0.42    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.42    inference(ennf_transformation,[],[f15])).
% 0.22/0.42  fof(f15,axiom,(
% 0.22/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.42  fof(f156,plain,(
% 0.22/0.42    spl4_8 | ~spl4_5 | ~spl4_7),
% 0.22/0.42    inference(avatar_split_clause,[],[f151,f141,f101,f153])).
% 0.22/0.42  fof(f141,plain,(
% 0.22/0.42    spl4_7 <=> v5_relat_1(sK2,sK1)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.42  fof(f151,plain,(
% 0.22/0.42    r1_tarski(k2_relat_1(sK2),sK1) | (~spl4_5 | ~spl4_7)),
% 0.22/0.42    inference(unit_resulting_resolution,[],[f103,f143,f56])).
% 0.22/0.42  fof(f56,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f40])).
% 0.22/0.42  fof(f40,plain,(
% 0.22/0.42    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.42    inference(nnf_transformation,[],[f25])).
% 0.22/0.42  fof(f25,plain,(
% 0.22/0.42    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f8])).
% 0.22/0.42  fof(f8,axiom,(
% 0.22/0.42    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.42  fof(f143,plain,(
% 0.22/0.42    v5_relat_1(sK2,sK1) | ~spl4_7),
% 0.22/0.42    inference(avatar_component_clause,[],[f141])).
% 0.22/0.42  fof(f144,plain,(
% 0.22/0.42    spl4_7 | ~spl4_3),
% 0.22/0.42    inference(avatar_split_clause,[],[f109,f83,f141])).
% 0.22/0.42  fof(f109,plain,(
% 0.22/0.42    v5_relat_1(sK2,sK1) | ~spl4_3),
% 0.22/0.42    inference(unit_resulting_resolution,[],[f85,f68])).
% 0.22/0.42  fof(f68,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f31])).
% 0.22/0.42  fof(f31,plain,(
% 0.22/0.42    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.42    inference(ennf_transformation,[],[f14])).
% 0.22/0.42  fof(f14,axiom,(
% 0.22/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.42  fof(f127,plain,(
% 0.22/0.42    spl4_6 | ~spl4_3),
% 0.22/0.42    inference(avatar_split_clause,[],[f106,f83,f124])).
% 0.22/0.42  fof(f106,plain,(
% 0.22/0.42    v4_relat_1(sK2,sK0) | ~spl4_3),
% 0.22/0.42    inference(unit_resulting_resolution,[],[f85,f67])).
% 0.22/0.42  fof(f67,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f31])).
% 0.22/0.42  fof(f104,plain,(
% 0.22/0.42    spl4_5 | ~spl4_3),
% 0.22/0.42    inference(avatar_split_clause,[],[f97,f83,f101])).
% 0.22/0.42  fof(f97,plain,(
% 0.22/0.42    v1_relat_1(sK2) | ~spl4_3),
% 0.22/0.42    inference(unit_resulting_resolution,[],[f52,f85,f50])).
% 0.22/0.42  fof(f50,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f21])).
% 0.22/0.42  fof(f21,plain,(
% 0.22/0.42    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f7])).
% 0.22/0.42  fof(f7,axiom,(
% 0.22/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.42  fof(f52,plain,(
% 0.22/0.42    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f9])).
% 0.22/0.42  fof(f9,axiom,(
% 0.22/0.42    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.42  fof(f91,plain,(
% 0.22/0.42    ~spl4_4),
% 0.22/0.42    inference(avatar_split_clause,[],[f47,f88])).
% 0.22/0.42  fof(f47,plain,(
% 0.22/0.42    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.42    inference(cnf_transformation,[],[f37])).
% 0.22/0.42  fof(f86,plain,(
% 0.22/0.42    spl4_3),
% 0.22/0.42    inference(avatar_split_clause,[],[f46,f83])).
% 0.22/0.42  fof(f46,plain,(
% 0.22/0.42    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.42    inference(cnf_transformation,[],[f37])).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (1856)------------------------------
% 0.22/0.42  % (1856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (1856)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (1856)Memory used [KB]: 10874
% 0.22/0.42  % (1856)Time elapsed: 0.013 s
% 0.22/0.42  % (1856)------------------------------
% 0.22/0.42  % (1856)------------------------------
% 0.22/0.42  % (1839)Success in time 0.067 s
%------------------------------------------------------------------------------
