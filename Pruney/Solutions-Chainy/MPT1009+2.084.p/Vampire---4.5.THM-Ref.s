%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 285 expanded)
%              Number of leaves         :   29 (  94 expanded)
%              Depth                    :   10
%              Number of atoms          :  333 ( 646 expanded)
%              Number of equality atoms :   97 ( 227 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f512,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f196,f198,f201,f215,f217,f255,f277,f300,f339,f405,f407,f409,f503,f511])).

fof(f511,plain,(
    spl5_26 ),
    inference(avatar_contradiction_clause,[],[f505])).

fof(f505,plain,
    ( $false
    | spl5_26 ),
    inference(unit_resulting_resolution,[],[f115,f502,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(f502,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | spl5_26 ),
    inference(avatar_component_clause,[],[f500])).

fof(f500,plain,
    ( spl5_26
  <=> r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f115,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f76,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f76,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f36,f74])).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

% (29472)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

fof(f503,plain,
    ( ~ spl5_17
    | ~ spl5_26
    | spl5_23 ),
    inference(avatar_split_clause,[],[f498,f402,f500,f330])).

fof(f330,plain,
    ( spl5_17
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f402,plain,
    ( spl5_23
  <=> r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f498,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))
    | spl5_23 ),
    inference(superposition,[],[f404,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f404,plain,
    ( ~ r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_relat_1(sK3))
    | spl5_23 ),
    inference(avatar_component_clause,[],[f402])).

fof(f409,plain,(
    spl5_22 ),
    inference(avatar_contradiction_clause,[],[f408])).

fof(f408,plain,
    ( $false
    | spl5_22 ),
    inference(subsumption_resolution,[],[f34,f400])).

fof(f400,plain,
    ( ~ v1_funct_1(sK3)
    | spl5_22 ),
    inference(avatar_component_clause,[],[f398])).

fof(f398,plain,
    ( spl5_22
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f34,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f407,plain,
    ( ~ spl5_5
    | spl5_21 ),
    inference(avatar_contradiction_clause,[],[f406])).

fof(f406,plain,
    ( $false
    | ~ spl5_5
    | spl5_21 ),
    inference(subsumption_resolution,[],[f224,f396])).

fof(f396,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK3))
    | spl5_21 ),
    inference(avatar_component_clause,[],[f394])).

fof(f394,plain,
    ( spl5_21
  <=> r2_hidden(sK0,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f224,plain,
    ( r2_hidden(sK0,k1_relat_1(sK3))
    | ~ spl5_5 ),
    inference(superposition,[],[f103,f213])).

fof(f213,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl5_5
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f103,plain,(
    ! [X3,X1] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X1)) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k2_enumset1(X3,X3,X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f61,f73])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f405,plain,
    ( ~ spl5_7
    | ~ spl5_21
    | ~ spl5_22
    | ~ spl5_23
    | ~ spl5_5
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f392,f297,f211,f402,f398,f394,f249])).

fof(f249,plain,
    ( spl5_7
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f297,plain,
    ( spl5_14
  <=> k2_relat_1(sK3) = k11_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f392,plain,
    ( ~ r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ r2_hidden(sK0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl5_5
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f368,f299])).

fof(f299,plain,
    ( k2_relat_1(sK3) = k11_relat_1(sK3,sK0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f297])).

fof(f368,plain,
    ( ~ r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k11_relat_1(sK3,sK0))
    | ~ v1_funct_1(sK3)
    | ~ r2_hidden(sK0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl5_5 ),
    inference(superposition,[],[f309,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f46,f74])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

fof(f309,plain,
    ( ~ r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f75,f213])).

fof(f75,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f38,f74,f74])).

fof(f38,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f339,plain,
    ( ~ spl5_5
    | spl5_17 ),
    inference(avatar_contradiction_clause,[],[f338])).

fof(f338,plain,
    ( $false
    | ~ spl5_5
    | spl5_17 ),
    inference(subsumption_resolution,[],[f253,f332])).

fof(f332,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f330])).

fof(f253,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f76,f213])).

fof(f300,plain,
    ( spl5_14
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f281,f275,f249,f297])).

fof(f275,plain,
    ( spl5_10
  <=> ! [X0] : v4_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f281,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) = k11_relat_1(sK3,sK0)
    | ~ spl5_10 ),
    inference(resolution,[],[f276,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k2_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f118,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f40,f74])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f118,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X0,X1) = k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X0,X1) = k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f43,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f276,plain,
    ( ! [X0] : v4_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,X0))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f275])).

fof(f277,plain,
    ( spl5_10
    | ~ spl5_7
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f272,f211,f249,f275])).

fof(f272,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK3)
        | v4_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,X0)) )
    | ~ spl5_5 ),
    inference(resolution,[],[f221,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f221,plain,
    ( ! [X1] : r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,X1))
    | ~ spl5_5 ),
    inference(superposition,[],[f108,f213])).

fof(f108,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_enumset1(X0,X0,X0,X1) != X3
      | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(definition_unfolding,[],[f69,f73,f48])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tarski(X0,X1) != X3
      | r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ~ ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

fof(f255,plain,(
    spl5_7 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | spl5_7 ),
    inference(subsumption_resolution,[],[f115,f251])).

fof(f251,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f249])).

fof(f217,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | spl5_4 ),
    inference(subsumption_resolution,[],[f76,f209])).

fof(f209,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl5_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f215,plain,
    ( ~ spl5_4
    | spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f204,f189,f211,f207])).

fof(f189,plain,
    ( spl5_2
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f204,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ spl5_2 ),
    inference(superposition,[],[f50,f191])).

fof(f191,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f189])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f201,plain,(
    ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f37,f195])).

fof(f195,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl5_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f37,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f198,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f77,f187])).

fof(f187,plain,
    ( ~ v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl5_1
  <=> v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f77,plain,(
    v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f35,f74])).

fof(f35,plain,(
    v1_funct_2(sK3,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f196,plain,
    ( ~ spl5_1
    | spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f183,f193,f189,f185])).

fof(f183,plain,
    ( k1_xboole_0 = sK1
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3)
    | ~ v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f56,f76])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

% (29464)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:52:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (29474)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.51  % (29474)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (29465)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (29482)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.51  % (29483)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.25/0.52  % (29475)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.25/0.52  % SZS output start Proof for theBenchmark
% 1.25/0.52  fof(f512,plain,(
% 1.25/0.52    $false),
% 1.25/0.52    inference(avatar_sat_refutation,[],[f196,f198,f201,f215,f217,f255,f277,f300,f339,f405,f407,f409,f503,f511])).
% 1.25/0.52  fof(f511,plain,(
% 1.25/0.52    spl5_26),
% 1.25/0.52    inference(avatar_contradiction_clause,[],[f505])).
% 1.25/0.52  fof(f505,plain,(
% 1.25/0.52    $false | spl5_26),
% 1.25/0.52    inference(unit_resulting_resolution,[],[f115,f502,f42])).
% 1.25/0.52  fof(f42,plain,(
% 1.25/0.52    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f21])).
% 1.25/0.52  fof(f21,plain,(
% 1.25/0.52    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.25/0.52    inference(ennf_transformation,[],[f8])).
% 1.25/0.52  fof(f8,axiom,(
% 1.25/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).
% 1.25/0.52  fof(f502,plain,(
% 1.25/0.52    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | spl5_26),
% 1.25/0.52    inference(avatar_component_clause,[],[f500])).
% 1.25/0.52  fof(f500,plain,(
% 1.25/0.52    spl5_26 <=> r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 1.25/0.52  fof(f115,plain,(
% 1.25/0.52    v1_relat_1(sK3)),
% 1.25/0.52    inference(resolution,[],[f76,f49])).
% 1.25/0.52  fof(f49,plain,(
% 1.25/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f28])).
% 1.25/0.52  fof(f28,plain,(
% 1.25/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/0.52    inference(ennf_transformation,[],[f12])).
% 1.25/0.52  fof(f12,axiom,(
% 1.25/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.25/0.52  fof(f76,plain,(
% 1.25/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.25/0.52    inference(definition_unfolding,[],[f36,f74])).
% 1.25/0.52  fof(f74,plain,(
% 1.25/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.25/0.52    inference(definition_unfolding,[],[f39,f73])).
% 1.25/0.52  fof(f73,plain,(
% 1.25/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.25/0.52    inference(definition_unfolding,[],[f41,f48])).
% 1.25/0.52  fof(f48,plain,(
% 1.25/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f4])).
% 1.25/0.52  fof(f4,axiom,(
% 1.25/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.25/0.52  fof(f41,plain,(
% 1.25/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f3])).
% 1.25/0.52  fof(f3,axiom,(
% 1.25/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.25/0.52  fof(f39,plain,(
% 1.25/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f2])).
% 1.25/0.52  fof(f2,axiom,(
% 1.25/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.25/0.52  fof(f36,plain,(
% 1.25/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.25/0.52    inference(cnf_transformation,[],[f19])).
% 1.25/0.52  fof(f19,plain,(
% 1.25/0.52    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 1.25/0.52    inference(flattening,[],[f18])).
% 1.25/0.52  fof(f18,plain,(
% 1.25/0.52    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 1.25/0.52    inference(ennf_transformation,[],[f17])).
% 1.25/0.52  % (29472)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.25/0.52  fof(f17,negated_conjecture,(
% 1.25/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.25/0.52    inference(negated_conjecture,[],[f16])).
% 1.25/0.52  fof(f16,conjecture,(
% 1.25/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).
% 1.25/0.52  fof(f503,plain,(
% 1.25/0.52    ~spl5_17 | ~spl5_26 | spl5_23),
% 1.25/0.52    inference(avatar_split_clause,[],[f498,f402,f500,f330])).
% 1.25/0.52  fof(f330,plain,(
% 1.25/0.52    spl5_17 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.25/0.52  fof(f402,plain,(
% 1.25/0.52    spl5_23 <=> r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_relat_1(sK3))),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 1.25/0.52  fof(f498,plain,(
% 1.25/0.52    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) | spl5_23),
% 1.25/0.52    inference(superposition,[],[f404,f63])).
% 1.25/0.52  fof(f63,plain,(
% 1.25/0.52    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.25/0.52    inference(cnf_transformation,[],[f32])).
% 1.25/0.52  fof(f32,plain,(
% 1.25/0.52    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/0.52    inference(ennf_transformation,[],[f14])).
% 1.25/0.52  fof(f14,axiom,(
% 1.25/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.25/0.52  fof(f404,plain,(
% 1.25/0.52    ~r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_relat_1(sK3)) | spl5_23),
% 1.25/0.52    inference(avatar_component_clause,[],[f402])).
% 1.25/0.52  fof(f409,plain,(
% 1.25/0.52    spl5_22),
% 1.25/0.52    inference(avatar_contradiction_clause,[],[f408])).
% 1.25/0.52  fof(f408,plain,(
% 1.25/0.52    $false | spl5_22),
% 1.25/0.52    inference(subsumption_resolution,[],[f34,f400])).
% 1.25/0.52  fof(f400,plain,(
% 1.25/0.52    ~v1_funct_1(sK3) | spl5_22),
% 1.25/0.52    inference(avatar_component_clause,[],[f398])).
% 1.25/0.52  fof(f398,plain,(
% 1.25/0.52    spl5_22 <=> v1_funct_1(sK3)),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 1.25/0.52  fof(f34,plain,(
% 1.25/0.52    v1_funct_1(sK3)),
% 1.25/0.52    inference(cnf_transformation,[],[f19])).
% 1.25/0.52  fof(f407,plain,(
% 1.25/0.52    ~spl5_5 | spl5_21),
% 1.25/0.52    inference(avatar_contradiction_clause,[],[f406])).
% 1.25/0.52  fof(f406,plain,(
% 1.25/0.52    $false | (~spl5_5 | spl5_21)),
% 1.25/0.52    inference(subsumption_resolution,[],[f224,f396])).
% 1.25/0.52  fof(f396,plain,(
% 1.25/0.52    ~r2_hidden(sK0,k1_relat_1(sK3)) | spl5_21),
% 1.25/0.52    inference(avatar_component_clause,[],[f394])).
% 1.25/0.52  fof(f394,plain,(
% 1.25/0.52    spl5_21 <=> r2_hidden(sK0,k1_relat_1(sK3))),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 1.25/0.52  fof(f224,plain,(
% 1.25/0.52    r2_hidden(sK0,k1_relat_1(sK3)) | ~spl5_5),
% 1.25/0.52    inference(superposition,[],[f103,f213])).
% 1.25/0.52  fof(f213,plain,(
% 1.25/0.52    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | ~spl5_5),
% 1.25/0.52    inference(avatar_component_clause,[],[f211])).
% 1.25/0.52  fof(f211,plain,(
% 1.25/0.52    spl5_5 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.25/0.52  fof(f103,plain,(
% 1.25/0.52    ( ! [X3,X1] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X1))) )),
% 1.25/0.52    inference(equality_resolution,[],[f102])).
% 1.25/0.52  fof(f102,plain,(
% 1.25/0.52    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k2_enumset1(X3,X3,X3,X1) != X2) )),
% 1.25/0.52    inference(equality_resolution,[],[f81])).
% 1.25/0.52  fof(f81,plain,(
% 1.25/0.52    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 1.25/0.52    inference(definition_unfolding,[],[f61,f73])).
% 1.25/0.52  fof(f61,plain,(
% 1.25/0.52    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.25/0.52    inference(cnf_transformation,[],[f1])).
% 1.25/0.52  fof(f1,axiom,(
% 1.25/0.52    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.25/0.52  fof(f405,plain,(
% 1.25/0.52    ~spl5_7 | ~spl5_21 | ~spl5_22 | ~spl5_23 | ~spl5_5 | ~spl5_14),
% 1.25/0.52    inference(avatar_split_clause,[],[f392,f297,f211,f402,f398,f394,f249])).
% 1.25/0.52  fof(f249,plain,(
% 1.25/0.52    spl5_7 <=> v1_relat_1(sK3)),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.25/0.52  fof(f297,plain,(
% 1.25/0.52    spl5_14 <=> k2_relat_1(sK3) = k11_relat_1(sK3,sK0)),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.25/0.52  fof(f392,plain,(
% 1.25/0.52    ~r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~r2_hidden(sK0,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl5_5 | ~spl5_14)),
% 1.25/0.52    inference(forward_demodulation,[],[f368,f299])).
% 1.25/0.52  fof(f299,plain,(
% 1.25/0.52    k2_relat_1(sK3) = k11_relat_1(sK3,sK0) | ~spl5_14),
% 1.25/0.52    inference(avatar_component_clause,[],[f297])).
% 1.25/0.52  fof(f368,plain,(
% 1.25/0.52    ~r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k11_relat_1(sK3,sK0)) | ~v1_funct_1(sK3) | ~r2_hidden(sK0,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl5_5),
% 1.25/0.52    inference(superposition,[],[f309,f79])).
% 1.25/0.52  fof(f79,plain,(
% 1.25/0.52    ( ! [X0,X1] : (k11_relat_1(X1,X0) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.25/0.52    inference(definition_unfolding,[],[f46,f74])).
% 1.25/0.52  fof(f46,plain,(
% 1.25/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))) )),
% 1.25/0.52    inference(cnf_transformation,[],[f25])).
% 1.25/0.52  fof(f25,plain,(
% 1.25/0.52    ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.25/0.52    inference(flattening,[],[f24])).
% 1.25/0.52  fof(f24,plain,(
% 1.25/0.52    ! [X0,X1] : ((k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.25/0.52    inference(ennf_transformation,[],[f11])).
% 1.25/0.52  fof(f11,axiom,(
% 1.25/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).
% 1.25/0.52  fof(f309,plain,(
% 1.25/0.52    ~r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) | ~spl5_5),
% 1.25/0.52    inference(forward_demodulation,[],[f75,f213])).
% 1.25/0.52  fof(f75,plain,(
% 1.25/0.52    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.25/0.52    inference(definition_unfolding,[],[f38,f74,f74])).
% 1.25/0.52  fof(f38,plain,(
% 1.25/0.52    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.25/0.52    inference(cnf_transformation,[],[f19])).
% 1.25/0.52  fof(f339,plain,(
% 1.25/0.52    ~spl5_5 | spl5_17),
% 1.25/0.52    inference(avatar_contradiction_clause,[],[f338])).
% 1.25/0.52  fof(f338,plain,(
% 1.25/0.52    $false | (~spl5_5 | spl5_17)),
% 1.25/0.52    inference(subsumption_resolution,[],[f253,f332])).
% 1.25/0.52  fof(f332,plain,(
% 1.25/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) | spl5_17),
% 1.25/0.52    inference(avatar_component_clause,[],[f330])).
% 1.25/0.52  fof(f253,plain,(
% 1.25/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) | ~spl5_5),
% 1.25/0.52    inference(forward_demodulation,[],[f76,f213])).
% 1.25/0.52  fof(f300,plain,(
% 1.25/0.52    spl5_14 | ~spl5_7 | ~spl5_10),
% 1.25/0.52    inference(avatar_split_clause,[],[f281,f275,f249,f297])).
% 1.25/0.52  fof(f275,plain,(
% 1.25/0.52    spl5_10 <=> ! [X0] : v4_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,X0))),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.25/0.52  fof(f281,plain,(
% 1.25/0.52    ~v1_relat_1(sK3) | k2_relat_1(sK3) = k11_relat_1(sK3,sK0) | ~spl5_10),
% 1.25/0.52    inference(resolution,[],[f276,f126])).
% 1.25/0.52  fof(f126,plain,(
% 1.25/0.52    ( ! [X0,X1] : (~v4_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0) | k11_relat_1(X0,X1) = k2_relat_1(X0)) )),
% 1.25/0.52    inference(duplicate_literal_removal,[],[f123])).
% 1.25/0.52  fof(f123,plain,(
% 1.25/0.52    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k2_relat_1(X0) | ~v1_relat_1(X0) | ~v4_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 1.25/0.52    inference(superposition,[],[f118,f78])).
% 1.25/0.52  fof(f78,plain,(
% 1.25/0.52    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 1.25/0.52    inference(definition_unfolding,[],[f40,f74])).
% 1.25/0.52  fof(f40,plain,(
% 1.25/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 1.25/0.52    inference(cnf_transformation,[],[f20])).
% 1.25/0.52  fof(f20,plain,(
% 1.25/0.52    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.25/0.52    inference(ennf_transformation,[],[f6])).
% 1.25/0.52  fof(f6,axiom,(
% 1.25/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 1.25/0.52  fof(f118,plain,(
% 1.25/0.52    ( ! [X0,X1] : (k9_relat_1(X0,X1) = k2_relat_1(X0) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 1.25/0.52    inference(duplicate_literal_removal,[],[f117])).
% 1.25/0.52  fof(f117,plain,(
% 1.25/0.52    ( ! [X0,X1] : (k9_relat_1(X0,X1) = k2_relat_1(X0) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 1.25/0.52    inference(superposition,[],[f43,f47])).
% 1.25/0.52  fof(f47,plain,(
% 1.25/0.52    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f27])).
% 1.25/0.52  fof(f27,plain,(
% 1.25/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.25/0.52    inference(flattening,[],[f26])).
% 1.25/0.52  fof(f26,plain,(
% 1.25/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.25/0.52    inference(ennf_transformation,[],[f10])).
% 1.25/0.52  fof(f10,axiom,(
% 1.25/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.25/0.52  fof(f43,plain,(
% 1.25/0.52    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f22])).
% 1.25/0.52  fof(f22,plain,(
% 1.25/0.52    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.25/0.52    inference(ennf_transformation,[],[f9])).
% 1.25/0.52  fof(f9,axiom,(
% 1.25/0.52    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.25/0.52  fof(f276,plain,(
% 1.25/0.52    ( ! [X0] : (v4_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,X0))) ) | ~spl5_10),
% 1.25/0.52    inference(avatar_component_clause,[],[f275])).
% 1.25/0.52  fof(f277,plain,(
% 1.25/0.52    spl5_10 | ~spl5_7 | ~spl5_5),
% 1.25/0.52    inference(avatar_split_clause,[],[f272,f211,f249,f275])).
% 1.25/0.52  fof(f272,plain,(
% 1.25/0.52    ( ! [X0] : (~v1_relat_1(sK3) | v4_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,X0))) ) | ~spl5_5),
% 1.25/0.52    inference(resolution,[],[f221,f44])).
% 1.25/0.52  fof(f44,plain,(
% 1.25/0.52    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | v4_relat_1(X1,X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f23])).
% 1.25/0.52  fof(f23,plain,(
% 1.25/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.25/0.52    inference(ennf_transformation,[],[f7])).
% 1.25/0.52  fof(f7,axiom,(
% 1.25/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.25/0.52  fof(f221,plain,(
% 1.25/0.52    ( ! [X1] : (r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,X1))) ) | ~spl5_5),
% 1.25/0.52    inference(superposition,[],[f108,f213])).
% 1.25/0.52  fof(f108,plain,(
% 1.25/0.52    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X1,X2))) )),
% 1.25/0.52    inference(equality_resolution,[],[f89])).
% 1.25/0.52  fof(f89,plain,(
% 1.25/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X0,X1) != X3 | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))) )),
% 1.25/0.52    inference(definition_unfolding,[],[f69,f73,f48])).
% 1.25/0.52  fof(f69,plain,(
% 1.25/0.52    ( ! [X2,X0,X3,X1] : (k2_tarski(X0,X1) != X3 | r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 1.25/0.52    inference(cnf_transformation,[],[f33])).
% 1.25/0.52  fof(f33,plain,(
% 1.25/0.52    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 1.25/0.52    inference(ennf_transformation,[],[f5])).
% 1.25/0.52  fof(f5,axiom,(
% 1.25/0.52    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).
% 1.25/0.52  fof(f255,plain,(
% 1.25/0.52    spl5_7),
% 1.25/0.52    inference(avatar_contradiction_clause,[],[f254])).
% 1.25/0.52  fof(f254,plain,(
% 1.25/0.52    $false | spl5_7),
% 1.25/0.52    inference(subsumption_resolution,[],[f115,f251])).
% 1.25/0.52  fof(f251,plain,(
% 1.25/0.52    ~v1_relat_1(sK3) | spl5_7),
% 1.25/0.52    inference(avatar_component_clause,[],[f249])).
% 1.25/0.52  fof(f217,plain,(
% 1.25/0.52    spl5_4),
% 1.25/0.52    inference(avatar_contradiction_clause,[],[f216])).
% 1.25/0.52  fof(f216,plain,(
% 1.25/0.52    $false | spl5_4),
% 1.25/0.52    inference(subsumption_resolution,[],[f76,f209])).
% 1.25/0.52  fof(f209,plain,(
% 1.25/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | spl5_4),
% 1.25/0.52    inference(avatar_component_clause,[],[f207])).
% 1.25/0.52  fof(f207,plain,(
% 1.25/0.52    spl5_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.25/0.52  fof(f215,plain,(
% 1.25/0.52    ~spl5_4 | spl5_5 | ~spl5_2),
% 1.25/0.52    inference(avatar_split_clause,[],[f204,f189,f211,f207])).
% 1.25/0.52  fof(f189,plain,(
% 1.25/0.52    spl5_2 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3)),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.25/0.52  fof(f204,plain,(
% 1.25/0.52    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~spl5_2),
% 1.25/0.52    inference(superposition,[],[f50,f191])).
% 1.25/0.52  fof(f191,plain,(
% 1.25/0.52    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) | ~spl5_2),
% 1.25/0.52    inference(avatar_component_clause,[],[f189])).
% 1.25/0.52  fof(f50,plain,(
% 1.25/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.25/0.52    inference(cnf_transformation,[],[f29])).
% 1.25/0.52  fof(f29,plain,(
% 1.25/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/0.52    inference(ennf_transformation,[],[f13])).
% 1.25/0.52  fof(f13,axiom,(
% 1.25/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.25/0.52  fof(f201,plain,(
% 1.25/0.52    ~spl5_3),
% 1.25/0.52    inference(avatar_contradiction_clause,[],[f199])).
% 1.25/0.52  fof(f199,plain,(
% 1.25/0.52    $false | ~spl5_3),
% 1.25/0.52    inference(subsumption_resolution,[],[f37,f195])).
% 1.25/0.52  fof(f195,plain,(
% 1.25/0.52    k1_xboole_0 = sK1 | ~spl5_3),
% 1.25/0.52    inference(avatar_component_clause,[],[f193])).
% 1.25/0.52  fof(f193,plain,(
% 1.25/0.52    spl5_3 <=> k1_xboole_0 = sK1),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.25/0.52  fof(f37,plain,(
% 1.25/0.52    k1_xboole_0 != sK1),
% 1.25/0.52    inference(cnf_transformation,[],[f19])).
% 1.25/0.52  fof(f198,plain,(
% 1.25/0.52    spl5_1),
% 1.25/0.52    inference(avatar_contradiction_clause,[],[f197])).
% 1.25/0.52  fof(f197,plain,(
% 1.25/0.52    $false | spl5_1),
% 1.25/0.52    inference(subsumption_resolution,[],[f77,f187])).
% 1.25/0.52  fof(f187,plain,(
% 1.25/0.52    ~v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | spl5_1),
% 1.25/0.52    inference(avatar_component_clause,[],[f185])).
% 1.25/0.52  fof(f185,plain,(
% 1.25/0.52    spl5_1 <=> v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.25/0.52  fof(f77,plain,(
% 1.25/0.52    v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.25/0.52    inference(definition_unfolding,[],[f35,f74])).
% 1.25/0.52  fof(f35,plain,(
% 1.25/0.52    v1_funct_2(sK3,k1_tarski(sK0),sK1)),
% 1.25/0.52    inference(cnf_transformation,[],[f19])).
% 1.25/0.52  fof(f196,plain,(
% 1.25/0.52    ~spl5_1 | spl5_2 | spl5_3),
% 1.25/0.52    inference(avatar_split_clause,[],[f183,f193,f189,f185])).
% 1.25/0.52  fof(f183,plain,(
% 1.25/0.52    k1_xboole_0 = sK1 | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) | ~v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.25/0.52    inference(resolution,[],[f56,f76])).
% 1.25/0.52  fof(f56,plain,(
% 1.25/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f31])).
% 1.25/0.52  fof(f31,plain,(
% 1.25/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/0.52    inference(flattening,[],[f30])).
% 1.25/0.52  fof(f30,plain,(
% 1.25/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/0.52    inference(ennf_transformation,[],[f15])).
% 1.25/0.52  fof(f15,axiom,(
% 1.25/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.25/0.52  % (29464)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.25/0.52  % SZS output end Proof for theBenchmark
% 1.25/0.52  % (29474)------------------------------
% 1.25/0.52  % (29474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (29474)Termination reason: Refutation
% 1.25/0.52  
% 1.25/0.52  % (29474)Memory used [KB]: 6524
% 1.25/0.52  % (29474)Time elapsed: 0.107 s
% 1.25/0.52  % (29474)------------------------------
% 1.25/0.52  % (29474)------------------------------
% 1.25/0.53  % (29467)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.25/0.53  % (29460)Success in time 0.166 s
%------------------------------------------------------------------------------
