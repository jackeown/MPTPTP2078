%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 247 expanded)
%              Number of leaves         :   26 (  82 expanded)
%              Depth                    :   10
%              Number of atoms          :  285 ( 557 expanded)
%              Number of equality atoms :   74 ( 217 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f374,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f105,f119,f277,f284,f291,f303,f342,f348,f352,f356,f373])).

fof(f373,plain,
    ( ~ spl4_4
    | spl4_14
    | ~ spl4_21 ),
    inference(avatar_contradiction_clause,[],[f364])).

fof(f364,plain,
    ( $false
    | ~ spl4_4
    | spl4_14
    | ~ spl4_21 ),
    inference(unit_resulting_resolution,[],[f304,f72,f341])).

fof(f341,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | r2_hidden(k1_funct_1(sK2,X0),k1_xboole_0) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f340])).

fof(f340,plain,
    ( spl4_21
  <=> ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,X0),k1_xboole_0)
        | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f72,plain,(
    ! [X3,X1] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X1)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k2_enumset1(X3,X3,X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f52,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
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

fof(f304,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_xboole_0)
    | ~ spl4_4
    | spl4_14 ),
    inference(forward_demodulation,[],[f269,f116])).

fof(f116,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl4_4
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f269,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl4_14
  <=> r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f356,plain,(
    ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f353])).

fof(f353,plain,
    ( $false
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f33,f330])).

fof(f330,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f328])).

fof(f328,plain,
    ( spl4_18
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f33,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

fof(f352,plain,(
    spl4_20 ),
    inference(avatar_contradiction_clause,[],[f349])).

fof(f349,plain,
    ( $false
    | spl4_20 ),
    inference(subsumption_resolution,[],[f60,f338])).

fof(f338,plain,
    ( ~ v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | spl4_20 ),
    inference(avatar_component_clause,[],[f336])).

fof(f336,plain,
    ( spl4_20
  <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f60,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f31,f57])).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f36,f56])).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f31,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f348,plain,(
    spl4_19 ),
    inference(avatar_contradiction_clause,[],[f344])).

fof(f344,plain,
    ( $false
    | spl4_19 ),
    inference(subsumption_resolution,[],[f59,f334])).

fof(f334,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | spl4_19 ),
    inference(avatar_component_clause,[],[f332])).

fof(f332,plain,
    ( spl4_19
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f32,f57])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f342,plain,
    ( ~ spl4_10
    | spl4_18
    | ~ spl4_19
    | ~ spl4_20
    | spl4_21
    | ~ spl4_4
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f322,f274,f114,f340,f336,f332,f328,f251])).

fof(f251,plain,
    ( spl4_10
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f274,plain,
    ( spl4_15
  <=> k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f322,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,X0),k1_xboole_0)
        | ~ v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
        | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | k1_xboole_0 = sK1
        | ~ v1_funct_1(sK2) )
    | ~ spl4_4
    | ~ spl4_15 ),
    inference(superposition,[],[f55,f305])).

fof(f305,plain,
    ( k1_xboole_0 = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | ~ spl4_4
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f275,f116])).

fof(f275,plain,
    ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f274])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

fof(f303,plain,
    ( ~ spl4_4
    | ~ spl4_14 ),
    inference(avatar_contradiction_clause,[],[f301])).

fof(f301,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(unit_resulting_resolution,[],[f35,f300,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f300,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f270,f116])).

fof(f270,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f268])).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f291,plain,(
    spl4_15 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | spl4_15 ),
    inference(unit_resulting_resolution,[],[f59,f276,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
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

fof(f276,plain,
    ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_relat_1(sK2)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f274])).

fof(f284,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f283])).

fof(f283,plain,
    ( $false
    | spl4_10 ),
    inference(subsumption_resolution,[],[f30,f253])).

fof(f253,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f251])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f277,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | ~ spl4_10
    | ~ spl4_15
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f272,f97,f274,f251,f110,f93])).

fof(f93,plain,
    ( spl4_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f110,plain,
    ( spl4_3
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f97,plain,
    ( spl4_2
  <=> k2_relat_1(sK2) = k11_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f272,plain,
    ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f120,f99])).

fof(f99,plain,
    ( k2_relat_1(sK2) = k11_relat_1(sK2,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f120,plain,
    ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k11_relat_1(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f58,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f41,f57])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

fof(f58,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    inference(definition_unfolding,[],[f34,f57,f57])).

fof(f34,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f119,plain,
    ( spl4_3
    | ~ spl4_1
    | spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f108,f97,f114,f93,f110])).

fof(f108,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl4_2 ),
    inference(superposition,[],[f39,f99])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | r2_hidden(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f105,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f76,f95])).

fof(f95,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f76,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f59,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f101,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f91,f97,f93])).

fof(f91,plain,
    ( k2_relat_1(sK2) = k11_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f61,f89])).

fof(f89,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f87,f59])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(X2) = k9_relat_1(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k9_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f45,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k9_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k9_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f54,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f54,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f37,f57])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:32:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (26410)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.49  % (26426)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (26410)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (26426)Refutation not found, incomplete strategy% (26426)------------------------------
% 0.21/0.50  % (26426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (26426)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (26426)Memory used [KB]: 1663
% 0.21/0.50  % (26426)Time elapsed: 0.004 s
% 0.21/0.50  % (26426)------------------------------
% 0.21/0.50  % (26426)------------------------------
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f374,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f101,f105,f119,f277,f284,f291,f303,f342,f348,f352,f356,f373])).
% 0.21/0.50  fof(f373,plain,(
% 0.21/0.50    ~spl4_4 | spl4_14 | ~spl4_21),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f364])).
% 0.21/0.50  fof(f364,plain,(
% 0.21/0.50    $false | (~spl4_4 | spl4_14 | ~spl4_21)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f304,f72,f341])).
% 0.21/0.50  fof(f341,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(k1_funct_1(sK2,X0),k1_xboole_0)) ) | ~spl4_21),
% 0.21/0.50    inference(avatar_component_clause,[],[f340])).
% 0.21/0.50  fof(f340,plain,(
% 0.21/0.50    spl4_21 <=> ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k1_xboole_0) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X3,X1] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X1))) )),
% 0.21/0.50    inference(equality_resolution,[],[f71])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k2_enumset1(X3,X3,X3,X1) != X2) )),
% 0.21/0.50    inference(equality_resolution,[],[f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.21/0.50    inference(definition_unfolding,[],[f52,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f38,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.50  fof(f304,plain,(
% 0.21/0.50    ~r2_hidden(k1_funct_1(sK2,sK0),k1_xboole_0) | (~spl4_4 | spl4_14)),
% 0.21/0.50    inference(forward_demodulation,[],[f269,f116])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(sK2) | ~spl4_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f114])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    spl4_4 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.50  fof(f269,plain,(
% 0.21/0.50    ~r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2)) | spl4_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f268])).
% 0.21/0.50  fof(f268,plain,(
% 0.21/0.50    spl4_14 <=> r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.50  fof(f356,plain,(
% 0.21/0.50    ~spl4_18),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f353])).
% 0.21/0.50  fof(f353,plain,(
% 0.21/0.50    $false | ~spl4_18),
% 0.21/0.50    inference(subsumption_resolution,[],[f33,f330])).
% 0.21/0.50  fof(f330,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | ~spl4_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f328])).
% 0.21/0.50  fof(f328,plain,(
% 0.21/0.50    spl4_18 <=> k1_xboole_0 = sK1),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    k1_xboole_0 != sK1),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.21/0.50    inference(negated_conjecture,[],[f15])).
% 0.21/0.50  fof(f15,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).
% 0.21/0.50  fof(f352,plain,(
% 0.21/0.50    spl4_20),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f349])).
% 0.21/0.50  fof(f349,plain,(
% 0.21/0.50    $false | spl4_20),
% 0.21/0.50    inference(subsumption_resolution,[],[f60,f338])).
% 0.21/0.50  fof(f338,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | spl4_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f336])).
% 0.21/0.50  fof(f336,plain,(
% 0.21/0.50    spl4_20 <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.50    inference(definition_unfolding,[],[f31,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f36,f56])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f348,plain,(
% 0.21/0.50    spl4_19),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f344])).
% 0.21/0.50  fof(f344,plain,(
% 0.21/0.50    $false | spl4_19),
% 0.21/0.50    inference(subsumption_resolution,[],[f59,f334])).
% 0.21/0.50  fof(f334,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | spl4_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f332])).
% 0.21/0.50  fof(f332,plain,(
% 0.21/0.50    spl4_19 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.21/0.50    inference(definition_unfolding,[],[f32,f57])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f342,plain,(
% 0.21/0.50    ~spl4_10 | spl4_18 | ~spl4_19 | ~spl4_20 | spl4_21 | ~spl4_4 | ~spl4_15),
% 0.21/0.50    inference(avatar_split_clause,[],[f322,f274,f114,f340,f336,f332,f328,f251])).
% 0.21/0.50  fof(f251,plain,(
% 0.21/0.50    spl4_10 <=> v1_funct_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.50  fof(f274,plain,(
% 0.21/0.50    spl4_15 <=> k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.50  fof(f322,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k1_xboole_0) | ~v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | k1_xboole_0 = sK1 | ~v1_funct_1(sK2)) ) | (~spl4_4 | ~spl4_15)),
% 0.21/0.50    inference(superposition,[],[f55,f305])).
% 0.21/0.50  fof(f305,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | (~spl4_4 | ~spl4_15)),
% 0.21/0.50    inference(forward_demodulation,[],[f275,f116])).
% 0.21/0.50  fof(f275,plain,(
% 0.21/0.50    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) | ~spl4_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f274])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | ~v1_funct_1(X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.50    inference(flattening,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).
% 0.21/0.50  fof(f303,plain,(
% 0.21/0.50    ~spl4_4 | ~spl4_14),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f301])).
% 0.21/0.50  fof(f301,plain,(
% 0.21/0.50    $false | (~spl4_4 | ~spl4_14)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f35,f300,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.50  fof(f300,plain,(
% 0.21/0.50    r2_hidden(k1_funct_1(sK2,sK0),k1_xboole_0) | (~spl4_4 | ~spl4_14)),
% 0.21/0.50    inference(forward_demodulation,[],[f270,f116])).
% 0.21/0.50  fof(f270,plain,(
% 0.21/0.50    r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2)) | ~spl4_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f268])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.50  fof(f291,plain,(
% 0.21/0.50    spl4_15),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f285])).
% 0.21/0.50  fof(f285,plain,(
% 0.21/0.50    $false | spl4_15),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f59,f276,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.50  fof(f276,plain,(
% 0.21/0.50    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_relat_1(sK2) | spl4_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f274])).
% 0.21/0.50  fof(f284,plain,(
% 0.21/0.50    spl4_10),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f283])).
% 0.21/0.50  fof(f283,plain,(
% 0.21/0.50    $false | spl4_10),
% 0.21/0.50    inference(subsumption_resolution,[],[f30,f253])).
% 0.21/0.50  fof(f253,plain,(
% 0.21/0.50    ~v1_funct_1(sK2) | spl4_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f251])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    v1_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f277,plain,(
% 0.21/0.50    ~spl4_1 | ~spl4_3 | ~spl4_10 | ~spl4_15 | ~spl4_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f272,f97,f274,f251,f110,f93])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    spl4_1 <=> v1_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    spl4_3 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    spl4_2 <=> k2_relat_1(sK2) = k11_relat_1(sK2,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.50  fof(f272,plain,(
% 0.21/0.50    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_relat_1(sK2) | ~v1_funct_1(sK2) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl4_2),
% 0.21/0.50    inference(forward_demodulation,[],[f120,f99])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    k2_relat_1(sK2) = k11_relat_1(sK2,sK0) | ~spl4_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f97])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k11_relat_1(sK2,sK0) | ~v1_funct_1(sK2) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.21/0.50    inference(superposition,[],[f58,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k11_relat_1(X1,X0) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f41,f57])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : ((k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 0.21/0.50    inference(definition_unfolding,[],[f34,f57,f57])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    spl4_3 | ~spl4_1 | spl4_4 | ~spl4_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f108,f97,f114,f93,f110])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(sK2) | ~v1_relat_1(sK2) | r2_hidden(sK0,k1_relat_1(sK2)) | ~spl4_2),
% 0.21/0.50    inference(superposition,[],[f39,f99])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 = k11_relat_1(X1,X0) | ~v1_relat_1(X1) | r2_hidden(X0,k1_relat_1(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    spl4_1),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f102])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    $false | spl4_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f76,f95])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | spl4_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f93])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    v1_relat_1(sK2)),
% 0.21/0.50    inference(resolution,[],[f59,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    ~spl4_1 | spl4_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f91,f97,f93])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    k2_relat_1(sK2) = k11_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 0.21/0.50    inference(superposition,[],[f61,f89])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    k2_relat_1(sK2) = k9_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.50    inference(resolution,[],[f87,f59])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relat_1(X2) = k9_relat_1(X2,X0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f86])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k9_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(superposition,[],[f45,f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k9_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f82])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k9_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(superposition,[],[f54,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f37,f57])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (26410)------------------------------
% 0.21/0.50  % (26410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (26410)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (26410)Memory used [KB]: 6396
% 0.21/0.50  % (26410)Time elapsed: 0.077 s
% 0.21/0.50  % (26410)------------------------------
% 0.21/0.50  % (26410)------------------------------
% 0.21/0.50  % (26396)Success in time 0.141 s
%------------------------------------------------------------------------------
