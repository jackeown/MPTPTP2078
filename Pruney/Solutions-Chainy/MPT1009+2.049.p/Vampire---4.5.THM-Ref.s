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
% DateTime   : Thu Dec  3 13:04:33 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 314 expanded)
%              Number of leaves         :   29 (  98 expanded)
%              Depth                    :   15
%              Number of atoms          :  331 ( 773 expanded)
%              Number of equality atoms :   89 ( 231 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f252,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f119,f121,f136,f145,f148,f178,f187,f193,f227,f251])).

fof(f251,plain,
    ( ~ spl4_2
    | spl4_4
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | ~ spl4_2
    | spl4_4
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(resolution,[],[f233,f51])).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f233,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ spl4_2
    | spl4_4
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(backward_demodulation,[],[f118,f228])).

fof(f228,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(sK3,X0)
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(resolution,[],[f196,f226])).

fof(f226,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl4_12
  <=> ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f196,plain,
    ( ! [X3] :
        ( ~ r1_xboole_0(k1_xboole_0,X3)
        | k1_xboole_0 = k9_relat_1(sK3,X3) )
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f154,f103])).

fof(f103,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl4_2
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f154,plain,
    ( ! [X3] :
        ( ~ r1_xboole_0(k1_relat_1(sK3),X3)
        | k1_xboole_0 = k9_relat_1(sK3,X3) )
    | ~ spl4_7 ),
    inference(resolution,[],[f140,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

% (11038)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(f140,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl4_7
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f118,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl4_4
  <=> r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f227,plain,
    ( spl4_5
    | spl4_12 ),
    inference(avatar_split_clause,[],[f223,f225,f129])).

fof(f129,plain,
    ( spl4_5
  <=> ! [X1,X2] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f223,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k1_xboole_0,X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(trivial_inequality_removal,[],[f222])).

fof(f222,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k1_xboole_0,X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(forward_demodulation,[],[f220,f53])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(f220,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(superposition,[],[f85,f49])).

fof(f49,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k1_relat_1(X0),X1)
      | k1_xboole_0 != k9_relat_1(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f63,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 != k9_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f193,plain,
    ( spl4_2
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f150,f139,f97,f101])).

fof(f97,plain,
    ( spl4_1
  <=> k1_xboole_0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f150,plain,
    ( k1_xboole_0 != k2_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f140,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f187,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | spl4_9 ),
    inference(resolution,[],[f177,f87])).

fof(f87,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3)) ),
    inference(resolution,[],[f80,f76])).

fof(f76,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f46,f74])).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f54,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f54,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK3,k1_tarski(sK0),sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f39])).

fof(f39,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK3,k1_tarski(sK0),sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r1_tarski(k9_relat_1(X0,X3),k2_relat_1(X0)) ) ),
    inference(resolution,[],[f68,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f177,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl4_9
  <=> r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f178,plain,
    ( ~ spl4_9
    | spl4_1
    | spl4_4
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f173,f143,f139,f116,f97,f175])).

fof(f143,plain,
    ( spl4_8
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | k11_relat_1(sK3,X0) = k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f173,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | spl4_4
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f172,f163])).

fof(f163,plain,
    ( k2_relat_1(sK3) = k11_relat_1(sK3,sK0)
    | ~ spl4_7 ),
    inference(superposition,[],[f156,f122])).

fof(f122,plain,(
    k2_relat_1(sK3) = k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f109,f76])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k2_relat_1(X0) = k9_relat_1(X0,X1) ) ),
    inference(condensation,[],[f108])).

% (11034)Termination reason: Refutation not found, incomplete strategy
fof(f108,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(resolution,[],[f107,f68])).

% (11034)Memory used [KB]: 6268
% (11034)Time elapsed: 0.137 s
% (11034)------------------------------
% (11034)------------------------------
fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(superposition,[],[f60,f106])).

% (11052)Refutation not found, incomplete strategy% (11052)------------------------------
% (11052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(condensation,[],[f105])).

fof(f105,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k7_relat_1(X0,X1) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ),
    inference(resolution,[],[f83,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_relat_1(X0,X1)
      | k7_relat_1(X0,X1) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f66,f68])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

% (11049)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f156,plain,
    ( ! [X5] : k11_relat_1(sK3,X5) = k9_relat_1(sK3,k2_enumset1(X5,X5,X5,X5))
    | ~ spl4_7 ),
    inference(resolution,[],[f140,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f57,f74])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f172,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k1_xboole_0 = k11_relat_1(sK3,sK0)
    | spl4_4
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f169,f163])).

fof(f169,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k11_relat_1(sK3,sK0))
    | k1_xboole_0 = k11_relat_1(sK3,sK0)
    | spl4_4
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(superposition,[],[f118,f161])).

fof(f161,plain,
    ( ! [X0] :
        ( k11_relat_1(sK3,X0) = k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0))
        | k1_xboole_0 = k11_relat_1(sK3,X0) )
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(resolution,[],[f144,f152])).

fof(f152,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k1_relat_1(sK3))
        | k1_xboole_0 = k11_relat_1(sK3,X1) )
    | ~ spl4_7 ),
    inference(resolution,[],[f140,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 = k11_relat_1(X1,X0)
      | r2_hidden(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(f144,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | k11_relat_1(sK3,X0) = k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f143])).

% (11048)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (11054)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (11050)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f148,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | spl4_7 ),
    inference(resolution,[],[f146,f76])).

fof(f146,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_7 ),
    inference(resolution,[],[f141,f68])).

fof(f141,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f139])).

fof(f145,plain,
    ( ~ spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f137,f143,f139])).

fof(f137,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | k11_relat_1(sK3,X0) = k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f79,f44])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k11_relat_1(X1,X0) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f65,f74])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

fof(f136,plain,(
    ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | ~ spl4_5 ),
    inference(resolution,[],[f130,f52])).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f130,plain,
    ( ! [X2,X1] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f129])).

fof(f121,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | spl4_3 ),
    inference(resolution,[],[f114,f76])).

fof(f114,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f119,plain,
    ( ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f110,f116,f112])).

fof(f110,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(superposition,[],[f75,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f75,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f48,f74,f74])).

fof(f48,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:51:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (11055)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (11047)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (11039)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (11035)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (11031)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (11036)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (11047)Refutation not found, incomplete strategy% (11047)------------------------------
% 0.21/0.53  % (11047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11053)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (11030)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (11045)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (11059)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (11034)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (11042)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (11037)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (11033)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (11045)Refutation not found, incomplete strategy% (11045)------------------------------
% 0.21/0.54  % (11045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (11045)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (11045)Memory used [KB]: 6140
% 0.21/0.54  % (11045)Time elapsed: 0.004 s
% 0.21/0.54  % (11045)------------------------------
% 0.21/0.54  % (11045)------------------------------
% 0.21/0.54  % (11041)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (11035)Refutation not found, incomplete strategy% (11035)------------------------------
% 0.21/0.54  % (11035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (11041)Refutation not found, incomplete strategy% (11041)------------------------------
% 0.21/0.54  % (11041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (11041)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (11041)Memory used [KB]: 10618
% 0.21/0.54  % (11041)Time elapsed: 0.135 s
% 0.21/0.54  % (11041)------------------------------
% 0.21/0.54  % (11041)------------------------------
% 1.40/0.55  % (11047)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  % (11051)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.40/0.55  
% 1.40/0.55  % (11047)Memory used [KB]: 10618
% 1.40/0.55  % (11047)Time elapsed: 0.116 s
% 1.40/0.55  % (11047)------------------------------
% 1.40/0.55  % (11047)------------------------------
% 1.40/0.55  % (11052)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.40/0.55  % (11042)Refutation found. Thanks to Tanya!
% 1.40/0.55  % SZS status Theorem for theBenchmark
% 1.40/0.55  % (11055)Refutation not found, incomplete strategy% (11055)------------------------------
% 1.40/0.55  % (11055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (11055)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (11055)Memory used [KB]: 6268
% 1.40/0.55  % (11055)Time elapsed: 0.119 s
% 1.40/0.55  % (11055)------------------------------
% 1.40/0.55  % (11055)------------------------------
% 1.40/0.55  % (11046)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.40/0.55  % (11034)Refutation not found, incomplete strategy% (11034)------------------------------
% 1.40/0.55  % (11034)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (11044)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.40/0.55  % (11051)Refutation not found, incomplete strategy% (11051)------------------------------
% 1.40/0.55  % (11051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (11035)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (11035)Memory used [KB]: 6268
% 1.40/0.55  % (11035)Time elapsed: 0.121 s
% 1.40/0.55  % (11035)------------------------------
% 1.40/0.55  % (11035)------------------------------
% 1.40/0.55  % (11057)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.40/0.55  % (11043)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.40/0.55  % (11058)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.40/0.55  % SZS output start Proof for theBenchmark
% 1.40/0.55  fof(f252,plain,(
% 1.40/0.55    $false),
% 1.40/0.55    inference(avatar_sat_refutation,[],[f119,f121,f136,f145,f148,f178,f187,f193,f227,f251])).
% 1.40/0.55  fof(f251,plain,(
% 1.40/0.55    ~spl4_2 | spl4_4 | ~spl4_7 | ~spl4_12),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f250])).
% 1.40/0.55  fof(f250,plain,(
% 1.40/0.55    $false | (~spl4_2 | spl4_4 | ~spl4_7 | ~spl4_12)),
% 1.40/0.55    inference(resolution,[],[f233,f51])).
% 1.40/0.55  fof(f51,plain,(
% 1.40/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f1])).
% 1.40/0.55  fof(f1,axiom,(
% 1.40/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.40/0.55  fof(f233,plain,(
% 1.40/0.55    ~r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) | (~spl4_2 | spl4_4 | ~spl4_7 | ~spl4_12)),
% 1.40/0.55    inference(backward_demodulation,[],[f118,f228])).
% 1.40/0.55  fof(f228,plain,(
% 1.40/0.55    ( ! [X0] : (k1_xboole_0 = k9_relat_1(sK3,X0)) ) | (~spl4_2 | ~spl4_7 | ~spl4_12)),
% 1.40/0.55    inference(resolution,[],[f196,f226])).
% 1.40/0.55  fof(f226,plain,(
% 1.40/0.55    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) ) | ~spl4_12),
% 1.40/0.55    inference(avatar_component_clause,[],[f225])).
% 1.40/0.55  fof(f225,plain,(
% 1.40/0.55    spl4_12 <=> ! [X0] : r1_xboole_0(k1_xboole_0,X0)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.40/0.55  fof(f196,plain,(
% 1.40/0.55    ( ! [X3] : (~r1_xboole_0(k1_xboole_0,X3) | k1_xboole_0 = k9_relat_1(sK3,X3)) ) | (~spl4_2 | ~spl4_7)),
% 1.40/0.55    inference(backward_demodulation,[],[f154,f103])).
% 1.40/0.55  fof(f103,plain,(
% 1.40/0.55    k1_xboole_0 = k1_relat_1(sK3) | ~spl4_2),
% 1.40/0.55    inference(avatar_component_clause,[],[f101])).
% 1.40/0.55  fof(f101,plain,(
% 1.40/0.55    spl4_2 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.40/0.55  fof(f154,plain,(
% 1.40/0.55    ( ! [X3] : (~r1_xboole_0(k1_relat_1(sK3),X3) | k1_xboole_0 = k9_relat_1(sK3,X3)) ) | ~spl4_7),
% 1.40/0.55    inference(resolution,[],[f140,f64])).
% 1.40/0.55  fof(f64,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f43])).
% 1.40/0.55  % (11038)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.40/0.55  fof(f43,plain,(
% 1.40/0.55    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.40/0.55    inference(nnf_transformation,[],[f29])).
% 1.40/0.55  fof(f29,plain,(
% 1.40/0.55    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.40/0.55    inference(ennf_transformation,[],[f11])).
% 1.40/0.55  fof(f11,axiom,(
% 1.40/0.55    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).
% 1.40/0.55  fof(f140,plain,(
% 1.40/0.55    v1_relat_1(sK3) | ~spl4_7),
% 1.40/0.55    inference(avatar_component_clause,[],[f139])).
% 1.40/0.55  fof(f139,plain,(
% 1.40/0.55    spl4_7 <=> v1_relat_1(sK3)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.40/0.55  fof(f118,plain,(
% 1.40/0.55    ~r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) | spl4_4),
% 1.40/0.55    inference(avatar_component_clause,[],[f116])).
% 1.40/0.55  fof(f116,plain,(
% 1.40/0.55    spl4_4 <=> r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.40/0.55  fof(f227,plain,(
% 1.40/0.55    spl4_5 | spl4_12),
% 1.40/0.55    inference(avatar_split_clause,[],[f223,f225,f129])).
% 1.40/0.55  fof(f129,plain,(
% 1.40/0.55    spl4_5 <=> ! [X1,X2] : ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.40/0.55  fof(f223,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (r1_xboole_0(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.40/0.55    inference(trivial_inequality_removal,[],[f222])).
% 1.40/0.55  fof(f222,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.40/0.55    inference(forward_demodulation,[],[f220,f53])).
% 1.40/0.55  fof(f53,plain,(
% 1.40/0.55    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f10])).
% 1.40/0.55  fof(f10,axiom,(
% 1.40/0.55    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 1.40/0.55  fof(f220,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (r1_xboole_0(k1_xboole_0,X0) | k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.40/0.55    inference(superposition,[],[f85,f49])).
% 1.40/0.55  fof(f49,plain,(
% 1.40/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.40/0.55    inference(cnf_transformation,[],[f14])).
% 1.40/0.55  fof(f14,axiom,(
% 1.40/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.40/0.55  fof(f85,plain,(
% 1.40/0.55    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k1_relat_1(X0),X1) | k1_xboole_0 != k9_relat_1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 1.40/0.55    inference(resolution,[],[f63,f68])).
% 1.40/0.55  fof(f68,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f34])).
% 1.40/0.55  fof(f34,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(ennf_transformation,[],[f17])).
% 1.40/0.55  fof(f17,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.40/0.55  fof(f63,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 != k9_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f43])).
% 1.40/0.55  fof(f193,plain,(
% 1.40/0.55    spl4_2 | ~spl4_1 | ~spl4_7),
% 1.40/0.55    inference(avatar_split_clause,[],[f150,f139,f97,f101])).
% 1.40/0.55  fof(f97,plain,(
% 1.40/0.55    spl4_1 <=> k1_xboole_0 = k2_relat_1(sK3)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.40/0.55  fof(f150,plain,(
% 1.40/0.55    k1_xboole_0 != k2_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3) | ~spl4_7),
% 1.40/0.55    inference(resolution,[],[f140,f56])).
% 1.40/0.55  fof(f56,plain,(
% 1.40/0.55    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f41])).
% 1.40/0.55  fof(f41,plain,(
% 1.40/0.55    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.40/0.55    inference(nnf_transformation,[],[f24])).
% 1.40/0.55  fof(f24,plain,(
% 1.40/0.55    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.40/0.55    inference(ennf_transformation,[],[f15])).
% 1.40/0.55  fof(f15,axiom,(
% 1.40/0.55    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 1.40/0.55  fof(f187,plain,(
% 1.40/0.55    spl4_9),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f186])).
% 1.40/0.55  fof(f186,plain,(
% 1.40/0.55    $false | spl4_9),
% 1.40/0.55    inference(resolution,[],[f177,f87])).
% 1.40/0.55  fof(f87,plain,(
% 1.40/0.55    ( ! [X0] : (r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))) )),
% 1.40/0.55    inference(resolution,[],[f80,f76])).
% 1.40/0.55  fof(f76,plain,(
% 1.40/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.40/0.55    inference(definition_unfolding,[],[f46,f74])).
% 1.40/0.55  fof(f74,plain,(
% 1.40/0.55    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.40/0.55    inference(definition_unfolding,[],[f54,f73])).
% 1.40/0.55  fof(f73,plain,(
% 1.40/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.40/0.55    inference(definition_unfolding,[],[f58,f67])).
% 1.40/0.55  fof(f67,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f4])).
% 1.40/0.55  fof(f4,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.40/0.55  fof(f58,plain,(
% 1.40/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f3])).
% 1.40/0.55  fof(f3,axiom,(
% 1.40/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.40/0.55  fof(f54,plain,(
% 1.40/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f2])).
% 1.40/0.55  fof(f2,axiom,(
% 1.40/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.40/0.55  fof(f46,plain,(
% 1.40/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.40/0.55    inference(cnf_transformation,[],[f40])).
% 1.40/0.55  fof(f40,plain,(
% 1.40/0.55    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3)),
% 1.40/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f39])).
% 1.40/0.55  fof(f39,plain,(
% 1.40/0.55    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f23,plain,(
% 1.40/0.55    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 1.40/0.55    inference(flattening,[],[f22])).
% 1.40/0.55  fof(f22,plain,(
% 1.40/0.55    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 1.40/0.55    inference(ennf_transformation,[],[f21])).
% 1.40/0.55  fof(f21,negated_conjecture,(
% 1.40/0.55    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.40/0.55    inference(negated_conjecture,[],[f20])).
% 1.40/0.55  fof(f20,conjecture,(
% 1.40/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 1.40/0.55  fof(f80,plain,(
% 1.40/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_tarski(k9_relat_1(X0,X3),k2_relat_1(X0))) )),
% 1.40/0.55    inference(resolution,[],[f68,f59])).
% 1.40/0.55  fof(f59,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f26])).
% 1.40/0.55  fof(f26,plain,(
% 1.40/0.55    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.40/0.55    inference(ennf_transformation,[],[f8])).
% 1.40/0.55  fof(f8,axiom,(
% 1.40/0.55    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 1.40/0.55  fof(f177,plain,(
% 1.40/0.55    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | spl4_9),
% 1.40/0.55    inference(avatar_component_clause,[],[f175])).
% 1.40/0.55  fof(f175,plain,(
% 1.40/0.55    spl4_9 <=> r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.40/0.55  fof(f178,plain,(
% 1.40/0.55    ~spl4_9 | spl4_1 | spl4_4 | ~spl4_7 | ~spl4_8),
% 1.40/0.55    inference(avatar_split_clause,[],[f173,f143,f139,f116,f97,f175])).
% 1.40/0.55  fof(f143,plain,(
% 1.40/0.55    spl4_8 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | k11_relat_1(sK3,X0) = k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)))),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.40/0.55  fof(f173,plain,(
% 1.40/0.55    k1_xboole_0 = k2_relat_1(sK3) | ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | (spl4_4 | ~spl4_7 | ~spl4_8)),
% 1.40/0.55    inference(forward_demodulation,[],[f172,f163])).
% 1.40/0.55  fof(f163,plain,(
% 1.40/0.55    k2_relat_1(sK3) = k11_relat_1(sK3,sK0) | ~spl4_7),
% 1.40/0.55    inference(superposition,[],[f156,f122])).
% 1.40/0.55  fof(f122,plain,(
% 1.40/0.55    k2_relat_1(sK3) = k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.40/0.55    inference(resolution,[],[f109,f76])).
% 1.40/0.55  fof(f109,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k2_relat_1(X0) = k9_relat_1(X0,X1)) )),
% 1.40/0.55    inference(condensation,[],[f108])).
% 1.40/0.55  % (11034)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  fof(f108,plain,(
% 1.40/0.55    ( ! [X4,X2,X0,X3,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 1.40/0.55    inference(resolution,[],[f107,f68])).
% 1.40/0.55  
% 1.40/0.55  % (11034)Memory used [KB]: 6268
% 1.40/0.55  % (11034)Time elapsed: 0.137 s
% 1.40/0.55  % (11034)------------------------------
% 1.40/0.55  % (11034)------------------------------
% 1.40/0.55  fof(f107,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k2_relat_1(X0) = k9_relat_1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.40/0.55    inference(superposition,[],[f60,f106])).
% 1.40/0.55  % (11052)Refutation not found, incomplete strategy% (11052)------------------------------
% 1.40/0.55  % (11052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  fof(f106,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (k7_relat_1(X0,X1) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.40/0.55    inference(condensation,[],[f105])).
% 1.40/0.55  fof(f105,plain,(
% 1.40/0.55    ( ! [X4,X2,X0,X3,X1] : (k7_relat_1(X0,X1) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X4)))) )),
% 1.40/0.55    inference(resolution,[],[f83,f69])).
% 1.40/0.55  fof(f69,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f35])).
% 1.40/0.55  fof(f35,plain,(
% 1.40/0.55    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(ennf_transformation,[],[f18])).
% 1.40/0.55  fof(f18,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.40/0.55  fof(f83,plain,(
% 1.40/0.55    ( ! [X2,X0,X3,X1] : (~v4_relat_1(X0,X1) | k7_relat_1(X0,X1) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 1.40/0.55    inference(resolution,[],[f66,f68])).
% 1.40/0.55  fof(f66,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 1.40/0.55    inference(cnf_transformation,[],[f33])).
% 1.40/0.55  fof(f33,plain,(
% 1.40/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.40/0.55    inference(flattening,[],[f32])).
% 1.40/0.55  fof(f32,plain,(
% 1.40/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.40/0.55    inference(ennf_transformation,[],[f13])).
% 1.40/0.55  fof(f13,axiom,(
% 1.40/0.55    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.40/0.55  fof(f60,plain,(
% 1.40/0.55    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f27])).
% 1.40/0.55  fof(f27,plain,(
% 1.40/0.55    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.40/0.55    inference(ennf_transformation,[],[f9])).
% 1.40/0.55  fof(f9,axiom,(
% 1.40/0.55    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.40/0.55  % (11049)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.40/0.55  fof(f156,plain,(
% 1.40/0.55    ( ! [X5] : (k11_relat_1(sK3,X5) = k9_relat_1(sK3,k2_enumset1(X5,X5,X5,X5))) ) | ~spl4_7),
% 1.40/0.55    inference(resolution,[],[f140,f78])).
% 1.40/0.55  fof(f78,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 1.40/0.55    inference(definition_unfolding,[],[f57,f74])).
% 1.40/0.55  fof(f57,plain,(
% 1.40/0.55    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f25])).
% 1.40/0.55  fof(f25,plain,(
% 1.40/0.55    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.40/0.55    inference(ennf_transformation,[],[f7])).
% 1.40/0.55  fof(f7,axiom,(
% 1.40/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 1.40/0.55  fof(f172,plain,(
% 1.40/0.55    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | k1_xboole_0 = k11_relat_1(sK3,sK0) | (spl4_4 | ~spl4_7 | ~spl4_8)),
% 1.40/0.55    inference(forward_demodulation,[],[f169,f163])).
% 1.40/0.55  fof(f169,plain,(
% 1.40/0.55    ~r1_tarski(k9_relat_1(sK3,sK2),k11_relat_1(sK3,sK0)) | k1_xboole_0 = k11_relat_1(sK3,sK0) | (spl4_4 | ~spl4_7 | ~spl4_8)),
% 1.40/0.55    inference(superposition,[],[f118,f161])).
% 1.40/0.55  fof(f161,plain,(
% 1.40/0.55    ( ! [X0] : (k11_relat_1(sK3,X0) = k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) | k1_xboole_0 = k11_relat_1(sK3,X0)) ) | (~spl4_7 | ~spl4_8)),
% 1.40/0.55    inference(resolution,[],[f144,f152])).
% 1.40/0.55  fof(f152,plain,(
% 1.40/0.55    ( ! [X1] : (r2_hidden(X1,k1_relat_1(sK3)) | k1_xboole_0 = k11_relat_1(sK3,X1)) ) | ~spl4_7),
% 1.40/0.55    inference(resolution,[],[f140,f62])).
% 1.40/0.55  fof(f62,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 = k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f42])).
% 1.40/0.55  fof(f42,plain,(
% 1.40/0.55    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 1.40/0.55    inference(nnf_transformation,[],[f28])).
% 1.40/0.55  fof(f28,plain,(
% 1.40/0.55    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.40/0.55    inference(ennf_transformation,[],[f12])).
% 1.40/0.55  fof(f12,axiom,(
% 1.40/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).
% 1.40/0.55  fof(f144,plain,(
% 1.40/0.55    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | k11_relat_1(sK3,X0) = k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0))) ) | ~spl4_8),
% 1.40/0.55    inference(avatar_component_clause,[],[f143])).
% 1.40/0.55  % (11048)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.40/0.55  % (11054)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.40/0.55  % (11050)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.40/0.55  fof(f148,plain,(
% 1.40/0.55    spl4_7),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f147])).
% 1.40/0.55  fof(f147,plain,(
% 1.40/0.55    $false | spl4_7),
% 1.40/0.55    inference(resolution,[],[f146,f76])).
% 1.40/0.55  fof(f146,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_7),
% 1.40/0.55    inference(resolution,[],[f141,f68])).
% 1.40/0.55  fof(f141,plain,(
% 1.40/0.55    ~v1_relat_1(sK3) | spl4_7),
% 1.40/0.55    inference(avatar_component_clause,[],[f139])).
% 1.40/0.55  fof(f145,plain,(
% 1.40/0.55    ~spl4_7 | spl4_8),
% 1.40/0.55    inference(avatar_split_clause,[],[f137,f143,f139])).
% 1.40/0.55  fof(f137,plain,(
% 1.40/0.55    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | k11_relat_1(sK3,X0) = k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) | ~v1_relat_1(sK3)) )),
% 1.40/0.55    inference(resolution,[],[f79,f44])).
% 1.40/0.55  fof(f44,plain,(
% 1.40/0.55    v1_funct_1(sK3)),
% 1.40/0.55    inference(cnf_transformation,[],[f40])).
% 1.40/0.55  fof(f79,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k11_relat_1(X1,X0) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 1.40/0.55    inference(definition_unfolding,[],[f65,f74])).
% 1.40/0.55  fof(f65,plain,(
% 1.40/0.55    ( ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f31])).
% 1.40/0.55  fof(f31,plain,(
% 1.40/0.55    ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.40/0.55    inference(flattening,[],[f30])).
% 1.40/0.55  fof(f30,plain,(
% 1.40/0.55    ! [X0,X1] : ((k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.40/0.55    inference(ennf_transformation,[],[f16])).
% 1.40/0.55  fof(f16,axiom,(
% 1.40/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).
% 1.40/0.55  fof(f136,plain,(
% 1.40/0.55    ~spl4_5),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f135])).
% 1.40/0.55  fof(f135,plain,(
% 1.40/0.55    $false | ~spl4_5),
% 1.40/0.55    inference(resolution,[],[f130,f52])).
% 1.40/0.55  fof(f52,plain,(
% 1.40/0.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f5])).
% 1.40/0.55  fof(f5,axiom,(
% 1.40/0.55    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.40/0.55  fof(f130,plain,(
% 1.40/0.55    ( ! [X2,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ) | ~spl4_5),
% 1.40/0.55    inference(avatar_component_clause,[],[f129])).
% 1.40/0.55  fof(f121,plain,(
% 1.40/0.55    spl4_3),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f120])).
% 1.40/0.55  fof(f120,plain,(
% 1.40/0.55    $false | spl4_3),
% 1.40/0.55    inference(resolution,[],[f114,f76])).
% 1.40/0.55  fof(f114,plain,(
% 1.40/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | spl4_3),
% 1.40/0.55    inference(avatar_component_clause,[],[f112])).
% 1.40/0.55  fof(f112,plain,(
% 1.40/0.55    spl4_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.40/0.55  fof(f119,plain,(
% 1.40/0.55    ~spl4_3 | ~spl4_4),
% 1.40/0.55    inference(avatar_split_clause,[],[f110,f116,f112])).
% 1.40/0.55  fof(f110,plain,(
% 1.40/0.55    ~r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.40/0.55    inference(superposition,[],[f75,f72])).
% 1.40/0.55  fof(f72,plain,(
% 1.40/0.55    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f38])).
% 1.40/0.55  fof(f38,plain,(
% 1.40/0.55    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(ennf_transformation,[],[f19])).
% 1.40/0.55  fof(f19,axiom,(
% 1.40/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.40/0.55  fof(f75,plain,(
% 1.40/0.55    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.40/0.55    inference(definition_unfolding,[],[f48,f74,f74])).
% 1.40/0.55  fof(f48,plain,(
% 1.40/0.55    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.40/0.55    inference(cnf_transformation,[],[f40])).
% 1.40/0.55  % SZS output end Proof for theBenchmark
% 1.40/0.55  % (11042)------------------------------
% 1.40/0.55  % (11042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (11042)Termination reason: Refutation
% 1.40/0.55  
% 1.40/0.55  % (11042)Memory used [KB]: 6268
% 1.40/0.55  % (11042)Time elapsed: 0.142 s
% 1.40/0.55  % (11042)------------------------------
% 1.40/0.55  % (11042)------------------------------
% 1.40/0.56  % (11029)Success in time 0.189 s
%------------------------------------------------------------------------------
