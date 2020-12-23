%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 303 expanded)
%              Number of leaves         :   33 ( 103 expanded)
%              Depth                    :   10
%              Number of atoms          :  326 ( 645 expanded)
%              Number of equality atoms :   77 ( 213 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (16955)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
fof(f664,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f152,f156,f226,f336,f338,f352,f427,f445,f496,f511,f516,f520,f546,f661])).

fof(f661,plain,
    ( spl5_14
    | ~ spl5_25 ),
    inference(avatar_contradiction_clause,[],[f654])).

fof(f654,plain,
    ( $false
    | spl5_14
    | ~ spl5_25 ),
    inference(unit_resulting_resolution,[],[f48,f548])).

fof(f548,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)))
    | spl5_14
    | ~ spl5_25 ),
    inference(forward_demodulation,[],[f547,f47])).

fof(f47,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f547,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)))
    | spl5_14
    | ~ spl5_25 ),
    inference(forward_demodulation,[],[f351,f510])).

fof(f510,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f508])).

fof(f508,plain,
    ( spl5_25
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f351,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f349])).

fof(f349,plain,
    ( spl5_14
  <=> r1_tarski(k2_relat_1(sK3),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f546,plain,
    ( spl5_13
    | ~ spl5_25 ),
    inference(avatar_contradiction_clause,[],[f540])).

fof(f540,plain,
    ( $false
    | spl5_13
    | ~ spl5_25 ),
    inference(unit_resulting_resolution,[],[f49,f531,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f531,plain,
    ( ~ v4_relat_1(k1_xboole_0,sK2)
    | spl5_13
    | ~ spl5_25 ),
    inference(superposition,[],[f347,f510])).

fof(f347,plain,
    ( ~ v4_relat_1(sK3,sK2)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f345])).

fof(f345,plain,
    ( spl5_13
  <=> v4_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f520,plain,
    ( ~ spl5_4
    | spl5_19 ),
    inference(avatar_contradiction_clause,[],[f517])).

fof(f517,plain,
    ( $false
    | ~ spl5_4
    | spl5_19 ),
    inference(unit_resulting_resolution,[],[f147,f420,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(f420,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | spl5_19 ),
    inference(avatar_component_clause,[],[f418])).

fof(f418,plain,
    ( spl5_19
  <=> r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f147,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl5_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f516,plain,
    ( ~ spl5_11
    | ~ spl5_19
    | spl5_20 ),
    inference(avatar_split_clause,[],[f514,f424,f418,f329])).

fof(f329,plain,
    ( spl5_11
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f424,plain,
    ( spl5_20
  <=> r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f514,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | spl5_20 ),
    inference(superposition,[],[f426,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f426,plain,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_relat_1(sK3))
    | spl5_20 ),
    inference(avatar_component_clause,[],[f424])).

fof(f511,plain,
    ( spl5_25
    | ~ spl5_4
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f502,f389,f145,f508])).

fof(f389,plain,
    ( spl5_16
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f502,plain,
    ( ~ v1_relat_1(sK3)
    | k1_xboole_0 = sK3
    | ~ spl5_16 ),
    inference(trivial_inequality_removal,[],[f501])).

fof(f501,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK3)
    | k1_xboole_0 = sK3
    | ~ spl5_16 ),
    inference(superposition,[],[f51,f391])).

fof(f391,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f389])).

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f496,plain,(
    spl5_18 ),
    inference(avatar_contradiction_clause,[],[f495])).

fof(f495,plain,
    ( $false
    | spl5_18 ),
    inference(subsumption_resolution,[],[f41,f416])).

fof(f416,plain,
    ( ~ v1_funct_1(sK3)
    | spl5_18 ),
    inference(avatar_component_clause,[],[f414])).

fof(f414,plain,
    ( spl5_18
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f41,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

fof(f445,plain,
    ( spl5_17
    | ~ spl5_4
    | spl5_16 ),
    inference(avatar_split_clause,[],[f442,f389,f145,f410])).

fof(f410,plain,
    ( spl5_17
  <=> r2_hidden(sK0,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f442,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | r2_hidden(sK0,k1_relat_1(sK3)) ),
    inference(resolution,[],[f356,f142])).

fof(f142,plain,(
    v4_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f83,f70])).

fof(f83,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f43,f81])).

fof(f81,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f80])).

fof(f80,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f356,plain,(
    ! [X4,X3] :
      ( ~ v4_relat_1(X4,k2_enumset1(X3,X3,X3,X3))
      | k1_xboole_0 = k1_relat_1(X4)
      | ~ v1_relat_1(X4)
      | r2_hidden(X3,k1_relat_1(X4)) ) ),
    inference(superposition,[],[f103,f229])).

fof(f229,plain,(
    ! [X2,X3] :
      ( k2_enumset1(X2,X2,X2,X2) = k1_relat_1(X3)
      | k1_xboole_0 = k1_relat_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v4_relat_1(X3,k2_enumset1(X2,X2,X2,X2)) ) ),
    inference(resolution,[],[f89,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f63,f81,f81])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f103,plain,(
    ! [X3,X1] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X1)) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k2_enumset1(X3,X3,X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f77,f80])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f427,plain,
    ( ~ spl5_4
    | ~ spl5_17
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f422,f223,f424,f414,f410,f145])).

fof(f223,plain,
    ( spl5_8
  <=> k2_relat_1(sK3) = k11_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f422,plain,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ r2_hidden(sK0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f395,f225])).

fof(f225,plain,
    ( k2_relat_1(sK3) = k11_relat_1(sK3,sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f223])).

fof(f395,plain,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k11_relat_1(sK3,sK0))
    | ~ v1_funct_1(sK3)
    | ~ r2_hidden(sK0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f82,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f61,f81])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

fof(f82,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f45,f81,f81])).

fof(f45,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f352,plain,
    ( ~ spl5_13
    | ~ spl5_4
    | ~ spl5_14
    | spl5_12 ),
    inference(avatar_split_clause,[],[f343,f333,f349,f145,f345])).

fof(f333,plain,
    ( spl5_12
  <=> r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f343,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ v1_relat_1(sK3)
    | ~ v4_relat_1(sK3,sK2)
    | spl5_12 ),
    inference(superposition,[],[f335,f160])).

fof(f160,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f58,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f335,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f333])).

fof(f338,plain,(
    spl5_11 ),
    inference(avatar_contradiction_clause,[],[f337])).

fof(f337,plain,
    ( $false
    | spl5_11 ),
    inference(subsumption_resolution,[],[f83,f331])).

fof(f331,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f329])).

fof(f336,plain,
    ( ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f327,f333,f329])).

fof(f327,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(superposition,[],[f82,f79])).

fof(f226,plain,
    ( spl5_8
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f216,f145,f223])).

fof(f216,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) = k11_relat_1(sK3,sK0) ),
    inference(resolution,[],[f176,f142])).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k2_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f160,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f53,f81])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f156,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f55,f151])).

fof(f151,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl5_5
  <=> v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f152,plain,
    ( spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f143,f149,f145])).

fof(f143,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f83,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:49:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.49  % (16946)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.51  % (16960)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.51  % (16936)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (16952)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.51  % (16940)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % (16960)Refutation not found, incomplete strategy% (16960)------------------------------
% 0.20/0.51  % (16960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (16960)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (16960)Memory used [KB]: 6268
% 0.20/0.51  % (16960)Time elapsed: 0.101 s
% 0.20/0.51  % (16960)------------------------------
% 0.20/0.51  % (16960)------------------------------
% 0.20/0.51  % (16938)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (16946)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  % (16955)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  fof(f664,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f152,f156,f226,f336,f338,f352,f427,f445,f496,f511,f516,f520,f546,f661])).
% 0.20/0.51  fof(f661,plain,(
% 0.20/0.51    spl5_14 | ~spl5_25),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f654])).
% 0.20/0.51  fof(f654,plain,(
% 0.20/0.51    $false | (spl5_14 | ~spl5_25)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f48,f548])).
% 0.20/0.51  fof(f548,plain,(
% 0.20/0.51    ~r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) | (spl5_14 | ~spl5_25)),
% 0.20/0.51    inference(forward_demodulation,[],[f547,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,axiom,(
% 0.20/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.51  fof(f547,plain,(
% 0.20/0.51    ~r1_tarski(k2_relat_1(k1_xboole_0),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) | (spl5_14 | ~spl5_25)),
% 0.20/0.51    inference(forward_demodulation,[],[f351,f510])).
% 0.20/0.51  fof(f510,plain,(
% 0.20/0.51    k1_xboole_0 = sK3 | ~spl5_25),
% 0.20/0.51    inference(avatar_component_clause,[],[f508])).
% 0.20/0.51  fof(f508,plain,(
% 0.20/0.51    spl5_25 <=> k1_xboole_0 = sK3),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.20/0.51  fof(f351,plain,(
% 0.20/0.51    ~r1_tarski(k2_relat_1(sK3),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) | spl5_14),
% 0.20/0.51    inference(avatar_component_clause,[],[f349])).
% 0.20/0.51  fof(f349,plain,(
% 0.20/0.51    spl5_14 <=> r1_tarski(k2_relat_1(sK3),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.51  fof(f546,plain,(
% 0.20/0.51    spl5_13 | ~spl5_25),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f540])).
% 0.20/0.51  fof(f540,plain,(
% 0.20/0.51    $false | (spl5_13 | ~spl5_25)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f49,f531,f70])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.51  fof(f531,plain,(
% 0.20/0.51    ~v4_relat_1(k1_xboole_0,sK2) | (spl5_13 | ~spl5_25)),
% 0.20/0.51    inference(superposition,[],[f347,f510])).
% 0.20/0.51  fof(f347,plain,(
% 0.20/0.51    ~v4_relat_1(sK3,sK2) | spl5_13),
% 0.20/0.51    inference(avatar_component_clause,[],[f345])).
% 0.20/0.51  fof(f345,plain,(
% 0.20/0.51    spl5_13 <=> v4_relat_1(sK3,sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.51  fof(f520,plain,(
% 0.20/0.51    ~spl5_4 | spl5_19),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f517])).
% 0.20/0.51  fof(f517,plain,(
% 0.20/0.51    $false | (~spl5_4 | spl5_19)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f147,f420,f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).
% 0.20/0.52  fof(f420,plain,(
% 0.20/0.52    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | spl5_19),
% 0.20/0.52    inference(avatar_component_clause,[],[f418])).
% 0.20/0.52  fof(f418,plain,(
% 0.20/0.52    spl5_19 <=> r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.20/0.52  fof(f147,plain,(
% 0.20/0.52    v1_relat_1(sK3) | ~spl5_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f145])).
% 0.20/0.52  fof(f145,plain,(
% 0.20/0.52    spl5_4 <=> v1_relat_1(sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.52  fof(f516,plain,(
% 0.20/0.52    ~spl5_11 | ~spl5_19 | spl5_20),
% 0.20/0.52    inference(avatar_split_clause,[],[f514,f424,f418,f329])).
% 0.20/0.52  fof(f329,plain,(
% 0.20/0.52    spl5_11 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.52  fof(f424,plain,(
% 0.20/0.52    spl5_20 <=> r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_relat_1(sK3))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.20/0.52  fof(f514,plain,(
% 0.20/0.52    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | spl5_20),
% 0.20/0.52    inference(superposition,[],[f426,f79])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.52  fof(f426,plain,(
% 0.20/0.52    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_relat_1(sK3)) | spl5_20),
% 0.20/0.52    inference(avatar_component_clause,[],[f424])).
% 0.20/0.52  fof(f511,plain,(
% 0.20/0.52    spl5_25 | ~spl5_4 | ~spl5_16),
% 0.20/0.52    inference(avatar_split_clause,[],[f502,f389,f145,f508])).
% 0.20/0.52  fof(f389,plain,(
% 0.20/0.52    spl5_16 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.52  fof(f502,plain,(
% 0.20/0.52    ~v1_relat_1(sK3) | k1_xboole_0 = sK3 | ~spl5_16),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f501])).
% 0.20/0.52  fof(f501,plain,(
% 0.20/0.52    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK3) | k1_xboole_0 = sK3 | ~spl5_16),
% 0.20/0.52    inference(superposition,[],[f51,f391])).
% 0.20/0.52  fof(f391,plain,(
% 0.20/0.52    k1_xboole_0 = k1_relat_1(sK3) | ~spl5_16),
% 0.20/0.52    inference(avatar_component_clause,[],[f389])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.20/0.52  fof(f496,plain,(
% 0.20/0.52    spl5_18),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f495])).
% 0.20/0.52  fof(f495,plain,(
% 0.20/0.52    $false | spl5_18),
% 0.20/0.52    inference(subsumption_resolution,[],[f41,f416])).
% 0.20/0.52  fof(f416,plain,(
% 0.20/0.52    ~v1_funct_1(sK3) | spl5_18),
% 0.20/0.52    inference(avatar_component_clause,[],[f414])).
% 0.20/0.52  fof(f414,plain,(
% 0.20/0.52    spl5_18 <=> v1_funct_1(sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    v1_funct_1(sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 0.20/0.52    inference(flattening,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 0.20/0.52    inference(ennf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.20/0.52    inference(negated_conjecture,[],[f22])).
% 0.20/0.52  fof(f22,conjecture,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).
% 0.20/0.52  fof(f445,plain,(
% 0.20/0.52    spl5_17 | ~spl5_4 | spl5_16),
% 0.20/0.52    inference(avatar_split_clause,[],[f442,f389,f145,f410])).
% 0.20/0.52  fof(f410,plain,(
% 0.20/0.52    spl5_17 <=> r2_hidden(sK0,k1_relat_1(sK3))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.20/0.52  fof(f442,plain,(
% 0.20/0.52    k1_xboole_0 = k1_relat_1(sK3) | ~v1_relat_1(sK3) | r2_hidden(sK0,k1_relat_1(sK3))),
% 0.20/0.52    inference(resolution,[],[f356,f142])).
% 0.20/0.52  fof(f142,plain,(
% 0.20/0.52    v4_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.20/0.52    inference(resolution,[],[f83,f70])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.20/0.52    inference(definition_unfolding,[],[f43,f81])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f50,f80])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f56,f69])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f356,plain,(
% 0.20/0.52    ( ! [X4,X3] : (~v4_relat_1(X4,k2_enumset1(X3,X3,X3,X3)) | k1_xboole_0 = k1_relat_1(X4) | ~v1_relat_1(X4) | r2_hidden(X3,k1_relat_1(X4))) )),
% 0.20/0.52    inference(superposition,[],[f103,f229])).
% 0.20/0.52  fof(f229,plain,(
% 0.20/0.52    ( ! [X2,X3] : (k2_enumset1(X2,X2,X2,X2) = k1_relat_1(X3) | k1_xboole_0 = k1_relat_1(X3) | ~v1_relat_1(X3) | ~v4_relat_1(X3,k2_enumset1(X2,X2,X2,X2))) )),
% 0.20/0.52    inference(resolution,[],[f89,f60])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(definition_unfolding,[],[f63,f81,f81])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    ( ! [X3,X1] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X1))) )),
% 0.20/0.52    inference(equality_resolution,[],[f102])).
% 0.20/0.52  fof(f102,plain,(
% 0.20/0.52    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k2_enumset1(X3,X3,X3,X1) != X2) )),
% 0.20/0.52    inference(equality_resolution,[],[f91])).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.20/0.52    inference(definition_unfolding,[],[f77,f80])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.20/0.52  fof(f427,plain,(
% 0.20/0.52    ~spl5_4 | ~spl5_17 | ~spl5_18 | ~spl5_20 | ~spl5_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f422,f223,f424,f414,f410,f145])).
% 0.20/0.52  fof(f223,plain,(
% 0.20/0.52    spl5_8 <=> k2_relat_1(sK3) = k11_relat_1(sK3,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.52  fof(f422,plain,(
% 0.20/0.52    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~r2_hidden(sK0,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl5_8),
% 0.20/0.52    inference(forward_demodulation,[],[f395,f225])).
% 0.20/0.52  fof(f225,plain,(
% 0.20/0.52    k2_relat_1(sK3) = k11_relat_1(sK3,sK0) | ~spl5_8),
% 0.20/0.52    inference(avatar_component_clause,[],[f223])).
% 0.20/0.52  fof(f395,plain,(
% 0.20/0.52    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k11_relat_1(sK3,sK0)) | ~v1_funct_1(sK3) | ~r2_hidden(sK0,k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 0.20/0.52    inference(superposition,[],[f82,f86])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k11_relat_1(X1,X0) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f61,f81])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ! [X0,X1] : ((k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,axiom,(
% 0.20/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 0.20/0.52    inference(definition_unfolding,[],[f45,f81,f81])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f352,plain,(
% 0.20/0.52    ~spl5_13 | ~spl5_4 | ~spl5_14 | spl5_12),
% 0.20/0.52    inference(avatar_split_clause,[],[f343,f333,f349,f145,f345])).
% 0.20/0.52  fof(f333,plain,(
% 0.20/0.52    spl5_12 <=> r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.52  fof(f343,plain,(
% 0.20/0.52    ~r1_tarski(k2_relat_1(sK3),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) | ~v1_relat_1(sK3) | ~v4_relat_1(sK3,sK2) | spl5_12),
% 0.20/0.52    inference(superposition,[],[f335,f160])).
% 0.20/0.52  fof(f160,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f159])).
% 0.20/0.52  fof(f159,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(superposition,[],[f58,f62])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,axiom,(
% 0.20/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.52  fof(f335,plain,(
% 0.20/0.52    ~r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) | spl5_12),
% 0.20/0.52    inference(avatar_component_clause,[],[f333])).
% 0.20/0.52  fof(f338,plain,(
% 0.20/0.52    spl5_11),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f337])).
% 0.20/0.52  fof(f337,plain,(
% 0.20/0.52    $false | spl5_11),
% 0.20/0.52    inference(subsumption_resolution,[],[f83,f331])).
% 0.20/0.52  fof(f331,plain,(
% 0.20/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | spl5_11),
% 0.20/0.52    inference(avatar_component_clause,[],[f329])).
% 0.20/0.52  fof(f336,plain,(
% 0.20/0.52    ~spl5_11 | ~spl5_12),
% 0.20/0.52    inference(avatar_split_clause,[],[f327,f333,f329])).
% 0.20/0.52  fof(f327,plain,(
% 0.20/0.52    ~r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.20/0.52    inference(superposition,[],[f82,f79])).
% 0.20/0.52  fof(f226,plain,(
% 0.20/0.52    spl5_8 | ~spl5_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f216,f145,f223])).
% 0.20/0.52  fof(f216,plain,(
% 0.20/0.52    ~v1_relat_1(sK3) | k2_relat_1(sK3) = k11_relat_1(sK3,sK0)),
% 0.20/0.52    inference(resolution,[],[f176,f142])).
% 0.20/0.52  fof(f176,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v4_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0) | k11_relat_1(X0,X1) = k2_relat_1(X0)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f172])).
% 0.20/0.52  fof(f172,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k2_relat_1(X0) | ~v1_relat_1(X0) | ~v4_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(superposition,[],[f160,f85])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f53,f81])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.20/0.52  fof(f156,plain,(
% 0.20/0.52    spl5_5),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f153])).
% 0.20/0.52  fof(f153,plain,(
% 0.20/0.52    $false | spl5_5),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f55,f151])).
% 0.20/0.52  fof(f151,plain,(
% 0.20/0.52    ~v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | spl5_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f149])).
% 0.20/0.52  fof(f149,plain,(
% 0.20/0.52    spl5_5 <=> v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,axiom,(
% 0.20/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.52  fof(f152,plain,(
% 0.20/0.52    spl5_4 | ~spl5_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f143,f149,f145])).
% 0.20/0.52  fof(f143,plain,(
% 0.20/0.52    ~v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | v1_relat_1(sK3)),
% 0.20/0.52    inference(resolution,[],[f83,f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (16946)------------------------------
% 0.20/0.52  % (16946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (16946)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (16946)Memory used [KB]: 6652
% 0.20/0.52  % (16946)Time elapsed: 0.098 s
% 0.20/0.52  % (16946)------------------------------
% 0.20/0.52  % (16946)------------------------------
% 0.20/0.52  % (16932)Success in time 0.164 s
%------------------------------------------------------------------------------
