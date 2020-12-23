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
% DateTime   : Thu Dec  3 13:04:32 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 252 expanded)
%              Number of leaves         :   19 (  76 expanded)
%              Depth                    :   13
%              Number of atoms          :  210 ( 501 expanded)
%              Number of equality atoms :   64 ( 206 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f186,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f125,f128,f158,f185])).

fof(f185,plain,
    ( ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f181,f72])).

fof(f72,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f42,f63])).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f59,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f181,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f80,f180])).

fof(f180,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(sK3,X0)
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f178,f47])).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f178,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k9_relat_1(sK3,X0))
        | k1_xboole_0 = k9_relat_1(sK3,X0) )
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(resolution,[],[f176,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f176,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK3,X0),k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f173,f119])).

fof(f119,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl4_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f173,plain,
    ( ! [X0] :
        ( r1_tarski(k9_relat_1(sK3,X0),k1_xboole_0)
        | ~ v1_relat_1(sK3) )
    | ~ spl4_6 ),
    inference(superposition,[],[f58,f124])).

fof(f124,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl4_6
  <=> k1_xboole_0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f80,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f64,f78])).

fof(f78,plain,(
    ! [X0] : k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f65,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f65,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f35,f63])).

% (19681)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f64,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f37,f63,f63])).

fof(f37,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f158,plain,
    ( ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f156,f119])).

fof(f156,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(resolution,[],[f155,f58])).

fof(f155,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f80,f154])).

fof(f154,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f153,f119])).

fof(f153,plain,
    ( ~ v1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f152,f33])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f152,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl4_4 ),
    inference(equality_resolution,[],[f145])).

fof(f145,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != k1_relat_1(sK3)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_relat_1(X0) = k2_enumset1(k1_funct_1(X0,sK0),k1_funct_1(X0,sK0),k1_funct_1(X0,sK0),k1_funct_1(X0,sK0)) )
    | ~ spl4_4 ),
    inference(superposition,[],[f70,f105])).

fof(f105,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl4_4
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) ) ),
    inference(definition_unfolding,[],[f48,f63,f63])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f128,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f65,f126])).

fof(f126,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_5 ),
    inference(resolution,[],[f120,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f120,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f125,plain,
    ( ~ spl4_5
    | spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f116,f99,f122,f118])).

fof(f99,plain,
    ( spl4_3
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f116,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_3 ),
    inference(trivial_inequality_removal,[],[f115])).

fof(f115,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_3 ),
    inference(superposition,[],[f54,f101])).

fof(f101,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f106,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f95,f103,f99])).

fof(f95,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(resolution,[],[f85,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f41,f63,f63])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f85,plain,(
    r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f84,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f84,plain,(
    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(subsumption_resolution,[],[f83,f65])).

fof(f83,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(superposition,[],[f60,f77])).

fof(f77,plain,(
    k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f65,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:08:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.23/0.51  % (19694)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.23/0.51  % (19686)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.23/0.52  % (19673)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.23/0.52  % (19677)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.53  % (19679)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.23/0.53  % (19678)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.23/0.54  % (19675)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.23/0.54  % (19674)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.23/0.54  % (19680)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.23/0.54  % (19671)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.23/0.54  % (19672)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.23/0.54  % (19672)Refutation not found, incomplete strategy% (19672)------------------------------
% 0.23/0.54  % (19672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (19672)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (19672)Memory used [KB]: 1663
% 0.23/0.54  % (19672)Time elapsed: 0.126 s
% 0.23/0.54  % (19672)------------------------------
% 0.23/0.54  % (19672)------------------------------
% 0.23/0.55  % (19682)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.23/0.55  % (19701)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.23/0.55  % (19701)Refutation not found, incomplete strategy% (19701)------------------------------
% 0.23/0.55  % (19701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (19700)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.23/0.55  % (19701)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (19701)Memory used [KB]: 1663
% 0.23/0.55  % (19701)Time elapsed: 0.129 s
% 0.23/0.55  % (19701)------------------------------
% 0.23/0.55  % (19701)------------------------------
% 0.23/0.55  % (19698)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.23/0.55  % (19695)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.23/0.55  % (19692)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.23/0.55  % (19695)Refutation not found, incomplete strategy% (19695)------------------------------
% 0.23/0.55  % (19695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (19695)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (19695)Memory used [KB]: 10746
% 0.23/0.55  % (19695)Time elapsed: 0.140 s
% 0.23/0.55  % (19695)------------------------------
% 0.23/0.55  % (19695)------------------------------
% 0.23/0.55  % (19700)Refutation not found, incomplete strategy% (19700)------------------------------
% 0.23/0.55  % (19700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (19700)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (19700)Memory used [KB]: 10746
% 0.23/0.55  % (19700)Time elapsed: 0.140 s
% 0.23/0.55  % (19700)------------------------------
% 0.23/0.55  % (19700)------------------------------
% 0.23/0.55  % (19699)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.23/0.55  % (19690)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.23/0.56  % (19697)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.23/0.56  % (19699)Refutation found. Thanks to Tanya!
% 0.23/0.56  % SZS status Theorem for theBenchmark
% 0.23/0.56  % SZS output start Proof for theBenchmark
% 0.23/0.56  fof(f186,plain,(
% 0.23/0.56    $false),
% 0.23/0.56    inference(avatar_sat_refutation,[],[f106,f125,f128,f158,f185])).
% 0.23/0.56  fof(f185,plain,(
% 0.23/0.56    ~spl4_5 | ~spl4_6),
% 0.23/0.56    inference(avatar_contradiction_clause,[],[f184])).
% 0.23/0.56  fof(f184,plain,(
% 0.23/0.56    $false | (~spl4_5 | ~spl4_6)),
% 0.23/0.56    inference(subsumption_resolution,[],[f181,f72])).
% 0.23/0.56  fof(f72,plain,(
% 0.23/0.56    ( ! [X1] : (r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1))) )),
% 0.23/0.56    inference(equality_resolution,[],[f68])).
% 0.23/0.56  fof(f68,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 0.23/0.56    inference(definition_unfolding,[],[f42,f63])).
% 0.23/0.56  fof(f63,plain,(
% 0.23/0.56    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.23/0.56    inference(definition_unfolding,[],[f56,f62])).
% 0.23/0.56  fof(f62,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.23/0.56    inference(definition_unfolding,[],[f59,f61])).
% 0.23/0.56  fof(f61,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f5])).
% 0.23/0.56  fof(f5,axiom,(
% 0.23/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.23/0.56  fof(f59,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f4])).
% 0.23/0.56  fof(f4,axiom,(
% 0.23/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.23/0.56  fof(f56,plain,(
% 0.23/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f3])).
% 0.23/0.56  fof(f3,axiom,(
% 0.23/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.23/0.56  fof(f42,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 0.23/0.56    inference(cnf_transformation,[],[f6])).
% 0.23/0.56  fof(f6,axiom,(
% 0.23/0.56    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.23/0.56  fof(f181,plain,(
% 0.23/0.56    ~r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) | (~spl4_5 | ~spl4_6)),
% 0.23/0.56    inference(backward_demodulation,[],[f80,f180])).
% 0.23/0.56  fof(f180,plain,(
% 0.23/0.56    ( ! [X0] : (k1_xboole_0 = k9_relat_1(sK3,X0)) ) | (~spl4_5 | ~spl4_6)),
% 0.23/0.56    inference(subsumption_resolution,[],[f178,f47])).
% 0.23/0.56  fof(f47,plain,(
% 0.23/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f2])).
% 0.23/0.56  fof(f2,axiom,(
% 0.23/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.23/0.56  fof(f178,plain,(
% 0.23/0.56    ( ! [X0] : (~r1_tarski(k1_xboole_0,k9_relat_1(sK3,X0)) | k1_xboole_0 = k9_relat_1(sK3,X0)) ) | (~spl4_5 | ~spl4_6)),
% 0.23/0.56    inference(resolution,[],[f176,f46])).
% 0.23/0.56  fof(f46,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.23/0.56    inference(cnf_transformation,[],[f1])).
% 0.23/0.56  fof(f1,axiom,(
% 0.23/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.23/0.56  fof(f176,plain,(
% 0.23/0.56    ( ! [X0] : (r1_tarski(k9_relat_1(sK3,X0),k1_xboole_0)) ) | (~spl4_5 | ~spl4_6)),
% 0.23/0.56    inference(subsumption_resolution,[],[f173,f119])).
% 0.23/0.56  fof(f119,plain,(
% 0.23/0.56    v1_relat_1(sK3) | ~spl4_5),
% 0.23/0.56    inference(avatar_component_clause,[],[f118])).
% 0.23/0.56  fof(f118,plain,(
% 0.23/0.56    spl4_5 <=> v1_relat_1(sK3)),
% 0.23/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.23/0.56  fof(f173,plain,(
% 0.23/0.56    ( ! [X0] : (r1_tarski(k9_relat_1(sK3,X0),k1_xboole_0) | ~v1_relat_1(sK3)) ) | ~spl4_6),
% 0.23/0.56    inference(superposition,[],[f58,f124])).
% 0.23/0.56  fof(f124,plain,(
% 0.23/0.56    k1_xboole_0 = k2_relat_1(sK3) | ~spl4_6),
% 0.23/0.56    inference(avatar_component_clause,[],[f122])).
% 0.23/0.56  fof(f122,plain,(
% 0.23/0.56    spl4_6 <=> k1_xboole_0 = k2_relat_1(sK3)),
% 0.23/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.23/0.56  fof(f58,plain,(
% 0.23/0.56    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f31])).
% 0.23/0.56  fof(f31,plain,(
% 0.23/0.56    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.23/0.56    inference(ennf_transformation,[],[f10])).
% 0.23/0.56  fof(f10,axiom,(
% 0.23/0.56    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 0.23/0.56  fof(f80,plain,(
% 0.23/0.56    ~r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 0.23/0.56    inference(backward_demodulation,[],[f64,f78])).
% 0.23/0.56  fof(f78,plain,(
% 0.23/0.56    ( ! [X0] : (k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 0.23/0.56    inference(resolution,[],[f65,f49])).
% 0.23/0.56  fof(f49,plain,(
% 0.23/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f27])).
% 0.23/0.56  fof(f27,plain,(
% 0.23/0.56    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.56    inference(ennf_transformation,[],[f17])).
% 0.23/0.56  fof(f17,axiom,(
% 0.23/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.23/0.56  fof(f65,plain,(
% 0.23/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.23/0.56    inference(definition_unfolding,[],[f35,f63])).
% 0.23/0.56  % (19681)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.23/0.56  fof(f35,plain,(
% 0.23/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.23/0.56    inference(cnf_transformation,[],[f22])).
% 0.23/0.56  fof(f22,plain,(
% 0.23/0.56    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 0.23/0.56    inference(flattening,[],[f21])).
% 0.23/0.56  fof(f21,plain,(
% 0.23/0.56    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 0.23/0.56    inference(ennf_transformation,[],[f20])).
% 0.23/0.56  fof(f20,negated_conjecture,(
% 0.23/0.56    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.23/0.56    inference(negated_conjecture,[],[f19])).
% 0.23/0.56  fof(f19,conjecture,(
% 0.23/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 0.23/0.56  fof(f64,plain,(
% 0.23/0.56    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 0.23/0.56    inference(definition_unfolding,[],[f37,f63,f63])).
% 0.23/0.56  fof(f37,plain,(
% 0.23/0.56    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 0.23/0.56    inference(cnf_transformation,[],[f22])).
% 0.23/0.56  fof(f158,plain,(
% 0.23/0.56    ~spl4_4 | ~spl4_5),
% 0.23/0.56    inference(avatar_contradiction_clause,[],[f157])).
% 0.23/0.56  fof(f157,plain,(
% 0.23/0.56    $false | (~spl4_4 | ~spl4_5)),
% 0.23/0.56    inference(subsumption_resolution,[],[f156,f119])).
% 0.23/0.56  fof(f156,plain,(
% 0.23/0.56    ~v1_relat_1(sK3) | (~spl4_4 | ~spl4_5)),
% 0.23/0.56    inference(resolution,[],[f155,f58])).
% 0.23/0.56  fof(f155,plain,(
% 0.23/0.56    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | (~spl4_4 | ~spl4_5)),
% 0.23/0.56    inference(backward_demodulation,[],[f80,f154])).
% 0.23/0.56  fof(f154,plain,(
% 0.23/0.56    k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | (~spl4_4 | ~spl4_5)),
% 0.23/0.56    inference(subsumption_resolution,[],[f153,f119])).
% 0.23/0.56  fof(f153,plain,(
% 0.23/0.56    ~v1_relat_1(sK3) | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~spl4_4),
% 0.23/0.56    inference(subsumption_resolution,[],[f152,f33])).
% 0.23/0.56  fof(f33,plain,(
% 0.23/0.56    v1_funct_1(sK3)),
% 0.23/0.56    inference(cnf_transformation,[],[f22])).
% 0.23/0.56  fof(f152,plain,(
% 0.23/0.56    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~spl4_4),
% 0.23/0.56    inference(equality_resolution,[],[f145])).
% 0.23/0.56  fof(f145,plain,(
% 0.23/0.56    ( ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK3) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k2_enumset1(k1_funct_1(X0,sK0),k1_funct_1(X0,sK0),k1_funct_1(X0,sK0),k1_funct_1(X0,sK0))) ) | ~spl4_4),
% 0.23/0.56    inference(superposition,[],[f70,f105])).
% 0.23/0.56  fof(f105,plain,(
% 0.23/0.56    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | ~spl4_4),
% 0.23/0.56    inference(avatar_component_clause,[],[f103])).
% 0.23/0.56  fof(f103,plain,(
% 0.23/0.56    spl4_4 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)),
% 0.23/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.23/0.56  fof(f70,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))) )),
% 0.23/0.56    inference(definition_unfolding,[],[f48,f63,f63])).
% 0.23/0.56  fof(f48,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))) )),
% 0.23/0.56    inference(cnf_transformation,[],[f26])).
% 0.23/0.56  fof(f26,plain,(
% 0.23/0.56    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.23/0.56    inference(flattening,[],[f25])).
% 0.23/0.56  fof(f25,plain,(
% 0.23/0.56    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.23/0.56    inference(ennf_transformation,[],[f12])).
% 0.23/0.56  fof(f12,axiom,(
% 0.23/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 0.23/0.56  fof(f128,plain,(
% 0.23/0.56    spl4_5),
% 0.23/0.56    inference(avatar_contradiction_clause,[],[f127])).
% 0.23/0.56  fof(f127,plain,(
% 0.23/0.56    $false | spl4_5),
% 0.23/0.56    inference(subsumption_resolution,[],[f65,f126])).
% 0.23/0.56  fof(f126,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_5),
% 0.23/0.56    inference(resolution,[],[f120,f55])).
% 0.23/0.56  fof(f55,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.56    inference(cnf_transformation,[],[f29])).
% 0.23/0.56  fof(f29,plain,(
% 0.23/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.56    inference(ennf_transformation,[],[f13])).
% 0.23/0.56  fof(f13,axiom,(
% 0.23/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.23/0.56  fof(f120,plain,(
% 0.23/0.56    ~v1_relat_1(sK3) | spl4_5),
% 0.23/0.56    inference(avatar_component_clause,[],[f118])).
% 0.23/0.56  fof(f125,plain,(
% 0.23/0.56    ~spl4_5 | spl4_6 | ~spl4_3),
% 0.23/0.56    inference(avatar_split_clause,[],[f116,f99,f122,f118])).
% 0.23/0.56  fof(f99,plain,(
% 0.23/0.56    spl4_3 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 0.23/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.23/0.56  fof(f116,plain,(
% 0.23/0.56    k1_xboole_0 = k2_relat_1(sK3) | ~v1_relat_1(sK3) | ~spl4_3),
% 0.23/0.56    inference(trivial_inequality_removal,[],[f115])).
% 0.23/0.56  fof(f115,plain,(
% 0.23/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_relat_1(sK3) | ~v1_relat_1(sK3) | ~spl4_3),
% 0.23/0.56    inference(superposition,[],[f54,f101])).
% 0.23/0.56  fof(f101,plain,(
% 0.23/0.56    k1_xboole_0 = k1_relat_1(sK3) | ~spl4_3),
% 0.23/0.56    inference(avatar_component_clause,[],[f99])).
% 0.23/0.56  fof(f54,plain,(
% 0.23/0.56    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f28])).
% 0.23/0.56  fof(f28,plain,(
% 0.23/0.56    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.23/0.56    inference(ennf_transformation,[],[f11])).
% 0.23/0.56  fof(f11,axiom,(
% 0.23/0.56    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.23/0.56  fof(f106,plain,(
% 0.23/0.56    spl4_3 | spl4_4),
% 0.23/0.56    inference(avatar_split_clause,[],[f95,f103,f99])).
% 0.23/0.56  fof(f95,plain,(
% 0.23/0.56    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3)),
% 0.23/0.56    inference(resolution,[],[f85,f69])).
% 0.23/0.56  fof(f69,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 0.23/0.56    inference(definition_unfolding,[],[f41,f63,f63])).
% 0.23/0.56  fof(f41,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.23/0.56    inference(cnf_transformation,[],[f6])).
% 0.23/0.56  fof(f85,plain,(
% 0.23/0.56    r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.23/0.56    inference(resolution,[],[f84,f40])).
% 0.23/0.56  fof(f40,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f8])).
% 0.23/0.56  fof(f8,axiom,(
% 0.23/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.23/0.56  fof(f84,plain,(
% 0.23/0.56    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.23/0.56    inference(subsumption_resolution,[],[f83,f65])).
% 0.23/0.56  fof(f83,plain,(
% 0.23/0.56    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.23/0.56    inference(superposition,[],[f60,f77])).
% 0.23/0.56  fof(f77,plain,(
% 0.23/0.56    k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) = k1_relat_1(sK3)),
% 0.23/0.56    inference(resolution,[],[f65,f57])).
% 0.23/0.56  fof(f57,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f30])).
% 0.23/0.56  fof(f30,plain,(
% 0.23/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.56    inference(ennf_transformation,[],[f16])).
% 0.23/0.56  fof(f16,axiom,(
% 0.23/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.23/0.56  fof(f60,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.56    inference(cnf_transformation,[],[f32])).
% 0.23/0.56  fof(f32,plain,(
% 0.23/0.56    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.56    inference(ennf_transformation,[],[f15])).
% 0.23/0.56  fof(f15,axiom,(
% 0.23/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.23/0.56  % SZS output end Proof for theBenchmark
% 0.23/0.56  % (19699)------------------------------
% 0.23/0.56  % (19699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (19699)Termination reason: Refutation
% 0.23/0.56  
% 0.23/0.56  % (19699)Memory used [KB]: 6268
% 0.23/0.56  % (19699)Time elapsed: 0.140 s
% 0.23/0.56  % (19699)------------------------------
% 0.23/0.56  % (19699)------------------------------
% 0.23/0.56  % (19684)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.23/0.56  % (19681)Refutation not found, incomplete strategy% (19681)------------------------------
% 0.23/0.56  % (19681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (19681)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (19681)Memory used [KB]: 10746
% 0.23/0.56  % (19681)Time elapsed: 0.140 s
% 0.23/0.56  % (19681)------------------------------
% 0.23/0.56  % (19681)------------------------------
% 0.23/0.56  % (19683)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.23/0.56  % (19688)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.23/0.56  % (19691)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.23/0.57  % (19670)Success in time 0.195 s
%------------------------------------------------------------------------------
