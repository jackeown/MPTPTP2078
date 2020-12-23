%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 253 expanded)
%              Number of leaves         :   27 (  85 expanded)
%              Depth                    :   10
%              Number of atoms          :  290 ( 566 expanded)
%              Number of equality atoms :   72 ( 189 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f293,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f86,f147,f157,f160,f176,f188,f233,f264,f266,f268,f282,f285,f292])).

fof(f292,plain,
    ( ~ spl5_1
    | spl5_22 ),
    inference(avatar_contradiction_clause,[],[f287])).

fof(f287,plain,
    ( $false
    | ~ spl5_1
    | spl5_22 ),
    inference(unit_resulting_resolution,[],[f77,f281,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f39,f34])).

fof(f34,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_relat_1)).

fof(f281,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | spl5_22 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl5_22
  <=> r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f77,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl5_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f285,plain,
    ( ~ spl5_12
    | spl5_21 ),
    inference(avatar_contradiction_clause,[],[f283])).

fof(f283,plain,
    ( $false
    | ~ spl5_12
    | spl5_21 ),
    inference(subsumption_resolution,[],[f204,f277])).

fof(f277,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))
    | spl5_21 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl5_21
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f204,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f57,f174])).

fof(f174,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl5_12
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f30,f55])).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f282,plain,
    ( ~ spl5_21
    | ~ spl5_22
    | spl5_20 ),
    inference(avatar_split_clause,[],[f273,f261,f279,f275])).

fof(f261,plain,
    ( spl5_20
  <=> r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f273,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))
    | spl5_20 ),
    inference(superposition,[],[f263,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f263,plain,
    ( ~ r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_relat_1(sK3))
    | spl5_20 ),
    inference(avatar_component_clause,[],[f261])).

fof(f268,plain,(
    spl5_19 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | spl5_19 ),
    inference(subsumption_resolution,[],[f28,f259])).

fof(f259,plain,
    ( ~ v1_funct_1(sK3)
    | spl5_19 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl5_19
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f28,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f266,plain,
    ( ~ spl5_12
    | spl5_18 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | ~ spl5_12
    | spl5_18 ),
    inference(subsumption_resolution,[],[f196,f255])).

fof(f255,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK3))
    | spl5_18 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl5_18
  <=> r2_hidden(sK0,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f196,plain,
    ( r2_hidden(sK0,k1_relat_1(sK3))
    | ~ spl5_12 ),
    inference(superposition,[],[f67,f174])).

fof(f67,plain,(
    ! [X2] : r2_hidden(X2,k2_enumset1(X2,X2,X2,X2)) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k2_enumset1(X2,X2,X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f41,f55])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f264,plain,
    ( ~ spl5_1
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_20
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f251,f221,f172,f261,f257,f253,f75])).

fof(f221,plain,
    ( spl5_14
  <=> k2_relat_1(sK3) = k11_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f251,plain,
    ( ~ r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ r2_hidden(sK0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f250,f174])).

fof(f250,plain,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ r2_hidden(sK0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f245,f223])).

fof(f223,plain,
    ( k2_relat_1(sK3) = k11_relat_1(sK3,sK0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f221])).

fof(f245,plain,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k11_relat_1(sK3,sK0))
    | ~ v1_funct_1(sK3)
    | ~ r2_hidden(sK0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f56,f60])).

% (17573)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
fof(f60,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f40,f55])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

fof(f56,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f32,f55,f55])).

fof(f32,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f233,plain,
    ( ~ spl5_1
    | spl5_14
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f216,f172,f221,f75])).

fof(f216,plain,
    ( k2_relat_1(sK3) = k11_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl5_12 ),
    inference(duplicate_literal_removal,[],[f211])).

fof(f211,plain,
    ( k2_relat_1(sK3) = k11_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl5_12 ),
    inference(superposition,[],[f34,f194])).

fof(f194,plain,
    ( ! [X1] :
        ( k11_relat_1(X1,sK0) = k9_relat_1(X1,k1_relat_1(sK3))
        | ~ v1_relat_1(X1) )
    | ~ spl5_12 ),
    inference(superposition,[],[f59,f174])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f35,f55])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f188,plain,(
    spl5_11 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | spl5_11 ),
    inference(subsumption_resolution,[],[f57,f170])).

fof(f170,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl5_11
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f176,plain,
    ( ~ spl5_11
    | spl5_12
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f165,f140,f172,f168])).

fof(f140,plain,
    ( spl5_8
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f165,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ spl5_8 ),
    inference(superposition,[],[f46,f142])).

fof(f142,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f140])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f160,plain,(
    spl5_7 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | spl5_7 ),
    inference(subsumption_resolution,[],[f58,f138])).

fof(f138,plain,
    ( ~ v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl5_7
  <=> v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f58,plain,(
    v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f29,f55])).

fof(f29,plain,(
    v1_funct_2(sK3,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f157,plain,(
    ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f31,f146])).

fof(f146,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl5_9
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f31,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f17])).

fof(f147,plain,
    ( ~ spl5_7
    | spl5_8
    | spl5_9 ),
    inference(avatar_split_clause,[],[f133,f144,f140,f136])).

fof(f133,plain,
    ( k1_xboole_0 = sK1
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3)
    | ~ v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f52,f57])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f86,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f37,f81])).

fof(f81,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl5_2
  <=> v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f37,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f82,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f73,f79,f75])).

fof(f73,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f57,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:19:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (17576)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (17601)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (17579)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (17584)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (17601)Refutation not found, incomplete strategy% (17601)------------------------------
% 0.21/0.52  % (17601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (17580)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (17601)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (17601)Memory used [KB]: 1663
% 0.21/0.52  % (17601)Time elapsed: 0.107 s
% 0.21/0.52  % (17581)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (17601)------------------------------
% 0.21/0.52  % (17601)------------------------------
% 0.21/0.53  % (17584)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (17574)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f293,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f82,f86,f147,f157,f160,f176,f188,f233,f264,f266,f268,f282,f285,f292])).
% 0.21/0.53  fof(f292,plain,(
% 0.21/0.53    ~spl5_1 | spl5_22),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f287])).
% 0.21/0.53  fof(f287,plain,(
% 0.21/0.53    $false | (~spl5_1 | spl5_22)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f77,f281,f89])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f88])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(superposition,[],[f39,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_relat_1)).
% 0.21/0.53  fof(f281,plain,(
% 0.21/0.53    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | spl5_22),
% 0.21/0.53    inference(avatar_component_clause,[],[f279])).
% 0.21/0.53  fof(f279,plain,(
% 0.21/0.53    spl5_22 <=> r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    v1_relat_1(sK3) | ~spl5_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f75])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    spl5_1 <=> v1_relat_1(sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.53  fof(f285,plain,(
% 0.21/0.53    ~spl5_12 | spl5_21),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f283])).
% 0.21/0.53  fof(f283,plain,(
% 0.21/0.53    $false | (~spl5_12 | spl5_21)),
% 0.21/0.53    inference(subsumption_resolution,[],[f204,f277])).
% 0.21/0.53  fof(f277,plain,(
% 0.21/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) | spl5_21),
% 0.21/0.53    inference(avatar_component_clause,[],[f275])).
% 0.21/0.53  fof(f275,plain,(
% 0.21/0.53    spl5_21 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.53  fof(f204,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) | ~spl5_12),
% 0.21/0.53    inference(forward_demodulation,[],[f57,f174])).
% 0.21/0.53  fof(f174,plain,(
% 0.21/0.53    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | ~spl5_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f172])).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    spl5_12 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.21/0.53    inference(definition_unfolding,[],[f30,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f33,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f38,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 0.21/0.53    inference(flattening,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.21/0.53    inference(negated_conjecture,[],[f14])).
% 0.21/0.53  fof(f14,conjecture,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 0.21/0.53  fof(f282,plain,(
% 0.21/0.53    ~spl5_21 | ~spl5_22 | spl5_20),
% 0.21/0.53    inference(avatar_split_clause,[],[f273,f261,f279,f275])).
% 0.21/0.53  fof(f261,plain,(
% 0.21/0.53    spl5_20 <=> r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_relat_1(sK3))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.53  fof(f273,plain,(
% 0.21/0.53    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) | spl5_20),
% 0.21/0.53    inference(superposition,[],[f263,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.53  fof(f263,plain,(
% 0.21/0.53    ~r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_relat_1(sK3)) | spl5_20),
% 0.21/0.53    inference(avatar_component_clause,[],[f261])).
% 0.21/0.53  fof(f268,plain,(
% 0.21/0.53    spl5_19),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f267])).
% 0.21/0.53  fof(f267,plain,(
% 0.21/0.53    $false | spl5_19),
% 0.21/0.53    inference(subsumption_resolution,[],[f28,f259])).
% 0.21/0.53  fof(f259,plain,(
% 0.21/0.53    ~v1_funct_1(sK3) | spl5_19),
% 0.21/0.53    inference(avatar_component_clause,[],[f257])).
% 0.21/0.53  fof(f257,plain,(
% 0.21/0.53    spl5_19 <=> v1_funct_1(sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    v1_funct_1(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f266,plain,(
% 0.21/0.53    ~spl5_12 | spl5_18),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f265])).
% 0.21/0.53  fof(f265,plain,(
% 0.21/0.53    $false | (~spl5_12 | spl5_18)),
% 0.21/0.53    inference(subsumption_resolution,[],[f196,f255])).
% 0.21/0.53  fof(f255,plain,(
% 0.21/0.53    ~r2_hidden(sK0,k1_relat_1(sK3)) | spl5_18),
% 0.21/0.53    inference(avatar_component_clause,[],[f253])).
% 0.21/0.53  fof(f253,plain,(
% 0.21/0.53    spl5_18 <=> r2_hidden(sK0,k1_relat_1(sK3))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.53  fof(f196,plain,(
% 0.21/0.53    r2_hidden(sK0,k1_relat_1(sK3)) | ~spl5_12),
% 0.21/0.53    inference(superposition,[],[f67,f174])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X2] : (r2_hidden(X2,k2_enumset1(X2,X2,X2,X2))) )),
% 0.21/0.53    inference(equality_resolution,[],[f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X2,X1] : (r2_hidden(X2,X1) | k2_enumset1(X2,X2,X2,X2) != X1) )),
% 0.21/0.53    inference(equality_resolution,[],[f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.21/0.53    inference(definition_unfolding,[],[f41,f55])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.53  fof(f264,plain,(
% 0.21/0.53    ~spl5_1 | ~spl5_18 | ~spl5_19 | ~spl5_20 | ~spl5_12 | ~spl5_14),
% 0.21/0.53    inference(avatar_split_clause,[],[f251,f221,f172,f261,f257,f253,f75])).
% 0.21/0.53  fof(f221,plain,(
% 0.21/0.53    spl5_14 <=> k2_relat_1(sK3) = k11_relat_1(sK3,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.53  fof(f251,plain,(
% 0.21/0.53    ~r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~r2_hidden(sK0,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl5_12 | ~spl5_14)),
% 0.21/0.53    inference(forward_demodulation,[],[f250,f174])).
% 0.21/0.53  fof(f250,plain,(
% 0.21/0.53    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~r2_hidden(sK0,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl5_14),
% 0.21/0.53    inference(forward_demodulation,[],[f245,f223])).
% 0.21/0.53  fof(f223,plain,(
% 0.21/0.53    k2_relat_1(sK3) = k11_relat_1(sK3,sK0) | ~spl5_14),
% 0.21/0.53    inference(avatar_component_clause,[],[f221])).
% 0.21/0.53  fof(f245,plain,(
% 0.21/0.53    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k11_relat_1(sK3,sK0)) | ~v1_funct_1(sK3) | ~r2_hidden(sK0,k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 0.21/0.53    inference(superposition,[],[f56,f60])).
% 1.25/0.53  % (17573)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.25/0.53  fof(f60,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k11_relat_1(X1,X0) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.25/0.53    inference(definition_unfolding,[],[f40,f55])).
% 1.25/0.53  fof(f40,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f23])).
% 1.25/0.53  fof(f23,plain,(
% 1.25/0.53    ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.25/0.53    inference(flattening,[],[f22])).
% 1.25/0.53  fof(f22,plain,(
% 1.25/0.53    ! [X0,X1] : ((k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.25/0.53    inference(ennf_transformation,[],[f10])).
% 1.25/0.53  fof(f10,axiom,(
% 1.25/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).
% 1.25/0.53  fof(f56,plain,(
% 1.25/0.53    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.25/0.53    inference(definition_unfolding,[],[f32,f55,f55])).
% 1.25/0.53  fof(f32,plain,(
% 1.25/0.53    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.25/0.53    inference(cnf_transformation,[],[f17])).
% 1.25/0.53  fof(f233,plain,(
% 1.25/0.53    ~spl5_1 | spl5_14 | ~spl5_12),
% 1.25/0.53    inference(avatar_split_clause,[],[f216,f172,f221,f75])).
% 1.25/0.53  fof(f216,plain,(
% 1.25/0.53    k2_relat_1(sK3) = k11_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | ~spl5_12),
% 1.25/0.53    inference(duplicate_literal_removal,[],[f211])).
% 1.25/0.53  fof(f211,plain,(
% 1.25/0.53    k2_relat_1(sK3) = k11_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | ~v1_relat_1(sK3) | ~spl5_12),
% 1.25/0.53    inference(superposition,[],[f34,f194])).
% 1.25/0.53  fof(f194,plain,(
% 1.25/0.53    ( ! [X1] : (k11_relat_1(X1,sK0) = k9_relat_1(X1,k1_relat_1(sK3)) | ~v1_relat_1(X1)) ) | ~spl5_12),
% 1.25/0.53    inference(superposition,[],[f59,f174])).
% 1.25/0.53  fof(f59,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 1.25/0.53    inference(definition_unfolding,[],[f35,f55])).
% 1.25/0.53  fof(f35,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f19])).
% 1.25/0.53  fof(f19,plain,(
% 1.25/0.53    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.25/0.53    inference(ennf_transformation,[],[f6])).
% 1.25/0.53  fof(f6,axiom,(
% 1.25/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 1.25/0.53  fof(f188,plain,(
% 1.25/0.53    spl5_11),
% 1.25/0.53    inference(avatar_contradiction_clause,[],[f185])).
% 1.25/0.53  fof(f185,plain,(
% 1.25/0.53    $false | spl5_11),
% 1.25/0.53    inference(subsumption_resolution,[],[f57,f170])).
% 1.25/0.53  fof(f170,plain,(
% 1.25/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | spl5_11),
% 1.25/0.53    inference(avatar_component_clause,[],[f168])).
% 1.25/0.53  fof(f168,plain,(
% 1.25/0.53    spl5_11 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.25/0.53  fof(f176,plain,(
% 1.25/0.53    ~spl5_11 | spl5_12 | ~spl5_8),
% 1.25/0.53    inference(avatar_split_clause,[],[f165,f140,f172,f168])).
% 1.25/0.53  fof(f140,plain,(
% 1.25/0.53    spl5_8 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3)),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.25/0.53  fof(f165,plain,(
% 1.25/0.53    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~spl5_8),
% 1.25/0.53    inference(superposition,[],[f46,f142])).
% 1.25/0.53  fof(f142,plain,(
% 1.25/0.53    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) | ~spl5_8),
% 1.25/0.53    inference(avatar_component_clause,[],[f140])).
% 1.25/0.53  fof(f46,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f24])).
% 1.25/0.53  fof(f24,plain,(
% 1.25/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/0.53    inference(ennf_transformation,[],[f11])).
% 1.25/0.53  fof(f11,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.25/0.53  fof(f160,plain,(
% 1.25/0.53    spl5_7),
% 1.25/0.53    inference(avatar_contradiction_clause,[],[f158])).
% 1.25/0.53  fof(f158,plain,(
% 1.25/0.53    $false | spl5_7),
% 1.25/0.53    inference(subsumption_resolution,[],[f58,f138])).
% 1.25/0.53  fof(f138,plain,(
% 1.25/0.53    ~v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | spl5_7),
% 1.25/0.53    inference(avatar_component_clause,[],[f136])).
% 1.25/0.53  fof(f136,plain,(
% 1.25/0.53    spl5_7 <=> v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.25/0.53  fof(f58,plain,(
% 1.25/0.53    v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.25/0.53    inference(definition_unfolding,[],[f29,f55])).
% 1.25/0.53  fof(f29,plain,(
% 1.25/0.53    v1_funct_2(sK3,k1_tarski(sK0),sK1)),
% 1.25/0.53    inference(cnf_transformation,[],[f17])).
% 1.25/0.53  fof(f157,plain,(
% 1.25/0.53    ~spl5_9),
% 1.25/0.53    inference(avatar_contradiction_clause,[],[f152])).
% 1.25/0.53  fof(f152,plain,(
% 1.25/0.53    $false | ~spl5_9),
% 1.25/0.53    inference(subsumption_resolution,[],[f31,f146])).
% 1.25/0.53  fof(f146,plain,(
% 1.25/0.53    k1_xboole_0 = sK1 | ~spl5_9),
% 1.25/0.53    inference(avatar_component_clause,[],[f144])).
% 1.25/0.53  fof(f144,plain,(
% 1.25/0.53    spl5_9 <=> k1_xboole_0 = sK1),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.25/0.53  fof(f31,plain,(
% 1.25/0.53    k1_xboole_0 != sK1),
% 1.25/0.53    inference(cnf_transformation,[],[f17])).
% 1.25/0.53  fof(f147,plain,(
% 1.25/0.53    ~spl5_7 | spl5_8 | spl5_9),
% 1.25/0.53    inference(avatar_split_clause,[],[f133,f144,f140,f136])).
% 1.25/0.53  fof(f133,plain,(
% 1.25/0.53    k1_xboole_0 = sK1 | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) | ~v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.25/0.53    inference(resolution,[],[f52,f57])).
% 1.25/0.53  fof(f52,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f26])).
% 1.25/0.53  fof(f26,plain,(
% 1.25/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/0.53    inference(flattening,[],[f25])).
% 1.25/0.53  fof(f25,plain,(
% 1.25/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/0.53    inference(ennf_transformation,[],[f13])).
% 1.25/0.53  fof(f13,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.25/0.53  fof(f86,plain,(
% 1.25/0.53    spl5_2),
% 1.25/0.53    inference(avatar_contradiction_clause,[],[f83])).
% 1.25/0.53  fof(f83,plain,(
% 1.25/0.53    $false | spl5_2),
% 1.25/0.53    inference(unit_resulting_resolution,[],[f37,f81])).
% 1.25/0.53  fof(f81,plain,(
% 1.25/0.53    ~v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | spl5_2),
% 1.25/0.53    inference(avatar_component_clause,[],[f79])).
% 1.25/0.53  fof(f79,plain,(
% 1.25/0.53    spl5_2 <=> v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.25/0.53  fof(f37,plain,(
% 1.25/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f7])).
% 1.25/0.53  fof(f7,axiom,(
% 1.25/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.25/0.53  fof(f82,plain,(
% 1.25/0.53    spl5_1 | ~spl5_2),
% 1.25/0.53    inference(avatar_split_clause,[],[f73,f79,f75])).
% 1.25/0.53  fof(f73,plain,(
% 1.25/0.53    ~v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | v1_relat_1(sK3)),
% 1.25/0.53    inference(resolution,[],[f57,f36])).
% 1.25/0.53  fof(f36,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f20])).
% 1.25/0.54  fof(f20,plain,(
% 1.25/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.25/0.54    inference(ennf_transformation,[],[f5])).
% 1.25/0.54  fof(f5,axiom,(
% 1.25/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.25/0.54  % SZS output end Proof for theBenchmark
% 1.25/0.54  % (17584)------------------------------
% 1.25/0.54  % (17584)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (17584)Termination reason: Refutation
% 1.25/0.54  
% 1.25/0.54  % (17584)Memory used [KB]: 6396
% 1.25/0.54  % (17584)Time elapsed: 0.115 s
% 1.25/0.54  % (17584)------------------------------
% 1.25/0.54  % (17584)------------------------------
% 1.25/0.54  % (17570)Success in time 0.173 s
%------------------------------------------------------------------------------
