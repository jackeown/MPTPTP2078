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
% DateTime   : Thu Dec  3 13:04:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 287 expanded)
%              Number of leaves         :   26 (  98 expanded)
%              Depth                    :   11
%              Number of atoms          :  347 ( 814 expanded)
%              Number of equality atoms :  127 ( 353 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f173,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f86,f94,f107,f109,f126,f129,f143,f145,f156,f161,f167,f172])).

fof(f172,plain,
    ( ~ spl4_10
    | spl4_12 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | ~ spl4_10
    | spl4_12 ),
    inference(resolution,[],[f169,f151])).

fof(f151,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl4_10
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f169,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_12 ),
    inference(trivial_inequality_removal,[],[f168])).

fof(f168,plain,
    ( k2_relat_1(sK3) != k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl4_12 ),
    inference(superposition,[],[f166,f39])).

fof(f39,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f166,plain,
    ( k9_relat_1(sK3,k1_relat_1(sK3)) != k2_relat_1(sK3)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl4_12
  <=> k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f167,plain,
    ( ~ spl4_5
    | ~ spl4_12
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f162,f154,f139,f103,f164,f103])).

fof(f103,plain,
    ( spl4_5
  <=> k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f139,plain,
    ( spl4_9
  <=> k2_relset_1(k1_relat_1(sK3),sK2,sK3) = k9_relat_1(sK3,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f154,plain,
    ( spl4_11
  <=> ! [X0] :
        ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
        | k2_relat_1(sK3) = k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f162,plain,
    ( k9_relat_1(sK3,k1_relat_1(sK3)) != k2_relat_1(sK3)
    | k2_enumset1(sK1,sK1,sK1,sK1) != k1_relat_1(sK3)
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(superposition,[],[f147,f155])).

fof(f155,plain,
    ( ! [X0] :
        ( k2_relat_1(sK3) = k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0))
        | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f154])).

fof(f147,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k9_relat_1(sK3,k1_relat_1(sK3))
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f112,f141])).

fof(f141,plain,
    ( k2_relset_1(k1_relat_1(sK3),sK2,sK3) = k9_relat_1(sK3,k1_relat_1(sK3))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f139])).

fof(f112,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k1_relat_1(sK3),sK2,sK3)
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f58,f105])).

fof(f105,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f58,plain,(
    k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) != k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) ),
    inference(definition_unfolding,[],[f37,f57,f57])).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    k2_relset_1(k1_tarski(sK1),sK2,sK3) != k1_tarski(k1_funct_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( k2_relset_1(k1_tarski(sK1),sK2,sK3) != k1_tarski(k1_funct_1(sK3,sK1))
    & k1_xboole_0 != sK2
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK3,k1_tarski(sK1),sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(k1_tarski(sK1),sK2,sK3) != k1_tarski(k1_funct_1(sK3,sK1))
      & k1_xboole_0 != sK2
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
      & v1_funct_2(sK3,k1_tarski(sK1),sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

fof(f161,plain,
    ( ~ spl4_5
    | spl4_10 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | ~ spl4_5
    | spl4_10 ),
    inference(resolution,[],[f158,f41])).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f158,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))
    | ~ spl4_5
    | spl4_10 ),
    inference(resolution,[],[f157,f111])).

fof(f111,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f59,f105])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f35,f57])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f29])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl4_10 ),
    inference(resolution,[],[f152,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f152,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f150])).

fof(f156,plain,
    ( ~ spl4_10
    | spl4_11 ),
    inference(avatar_split_clause,[],[f148,f154,f150])).

fof(f148,plain,(
    ! [X0] :
      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
      | k2_relat_1(sK3) = k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f61,f33])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0)
      | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f43,f57,f57])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f145,plain,
    ( ~ spl4_5
    | spl4_8 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | ~ spl4_5
    | spl4_8 ),
    inference(resolution,[],[f137,f111])).

fof(f137,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl4_8
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f143,plain,
    ( ~ spl4_8
    | spl4_9
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f133,f119,f139,f135])).

fof(f119,plain,
    ( spl4_6
  <=> k2_relset_1(k1_relat_1(sK3),sK2,sK3) = k7_relset_1(k1_relat_1(sK3),sK2,sK3,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f133,plain,
    ( k2_relset_1(k1_relat_1(sK3),sK2,sK3) = k9_relat_1(sK3,k1_relat_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | ~ spl4_6 ),
    inference(superposition,[],[f55,f121])).

fof(f121,plain,
    ( k2_relset_1(k1_relat_1(sK3),sK2,sK3) = k7_relset_1(k1_relat_1(sK3),sK2,sK3,k1_relat_1(sK3))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f119])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f129,plain,
    ( ~ spl4_1
    | ~ spl4_5
    | spl4_7 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_5
    | spl4_7 ),
    inference(resolution,[],[f125,f113])).

fof(f113,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),sK2)
    | ~ spl4_1
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f73,f105])).

fof(f73,plain,
    ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl4_1
  <=> v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f125,plain,
    ( ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl4_7
  <=> v1_funct_2(sK3,k1_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f126,plain,
    ( spl4_6
    | ~ spl4_7
    | spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f117,f103,f80,f123,f119])).

fof(f80,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f117,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2)
    | k2_relset_1(k1_relat_1(sK3),sK2,sK3) = k7_relset_1(k1_relat_1(sK3),sK2,sK3,k1_relat_1(sK3))
    | ~ spl4_5 ),
    inference(resolution,[],[f116,f111])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_xboole_0 = X0
      | ~ v1_funct_2(sK3,X1,X0)
      | k7_relset_1(X1,X0,sK3,X1) = k2_relset_1(X1,X0,sK3) ) ),
    inference(resolution,[],[f53,f33])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_funct_2)).

fof(f109,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | spl4_4 ),
    inference(resolution,[],[f101,f59])).

fof(f101,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f107,plain,
    ( ~ spl4_4
    | spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f97,f76,f103,f99])).

fof(f76,plain,
    ( spl4_2
  <=> k2_enumset1(sK1,sK1,sK1,sK1) = k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f97,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | ~ spl4_2 ),
    inference(superposition,[],[f45,f78])).

fof(f78,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f94,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | ~ spl4_3 ),
    inference(trivial_inequality_removal,[],[f92])).

fof(f92,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl4_3 ),
    inference(superposition,[],[f36,f82])).

fof(f82,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f36,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f29])).

fof(f86,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | spl4_1 ),
    inference(resolution,[],[f74,f60])).

fof(f60,plain,(
    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f34,f57])).

fof(f34,plain,(
    v1_funct_2(sK3,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,
    ( ~ v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f83,plain,
    ( ~ spl4_1
    | spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f70,f80,f76,f72])).

fof(f70,plain,
    ( k1_xboole_0 = sK2
    | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)
    | ~ v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(resolution,[],[f69,f59])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = X2
      | k1_relset_1(X1,X2,X0) = X1
      | ~ v1_funct_2(X0,X1,X2) ) ),
    inference(resolution,[],[f46,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f22,f26])).

fof(f26,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:31:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (21158)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (21166)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (21158)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (21150)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f83,f86,f94,f107,f109,f126,f129,f143,f145,f156,f161,f167,f172])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    ~spl4_10 | spl4_12),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f170])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    $false | (~spl4_10 | spl4_12)),
% 0.21/0.51    inference(resolution,[],[f169,f151])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    v1_relat_1(sK3) | ~spl4_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f150])).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    spl4_10 <=> v1_relat_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    ~v1_relat_1(sK3) | spl4_12),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f168])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    k2_relat_1(sK3) != k2_relat_1(sK3) | ~v1_relat_1(sK3) | spl4_12),
% 0.21/0.51    inference(superposition,[],[f166,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    k9_relat_1(sK3,k1_relat_1(sK3)) != k2_relat_1(sK3) | spl4_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f164])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    spl4_12 <=> k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    ~spl4_5 | ~spl4_12 | ~spl4_5 | ~spl4_9 | ~spl4_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f162,f154,f139,f103,f164,f103])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    spl4_5 <=> k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    spl4_9 <=> k2_relset_1(k1_relat_1(sK3),sK2,sK3) = k9_relat_1(sK3,k1_relat_1(sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    spl4_11 <=> ! [X0] : (k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) | k2_relat_1(sK3) = k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    k9_relat_1(sK3,k1_relat_1(sK3)) != k2_relat_1(sK3) | k2_enumset1(sK1,sK1,sK1,sK1) != k1_relat_1(sK3) | (~spl4_5 | ~spl4_9 | ~spl4_11)),
% 0.21/0.51    inference(superposition,[],[f147,f155])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    ( ! [X0] : (k2_relat_1(sK3) = k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)) ) | ~spl4_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f154])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k9_relat_1(sK3,k1_relat_1(sK3)) | (~spl4_5 | ~spl4_9)),
% 0.21/0.51    inference(backward_demodulation,[],[f112,f141])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    k2_relset_1(k1_relat_1(sK3),sK2,sK3) = k9_relat_1(sK3,k1_relat_1(sK3)) | ~spl4_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f139])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k1_relat_1(sK3),sK2,sK3) | ~spl4_5),
% 0.21/0.51    inference(backward_demodulation,[],[f58,f105])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3) | ~spl4_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f103])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) != k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1))),
% 0.21/0.51    inference(definition_unfolding,[],[f37,f57,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f38,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f42,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    k2_relset_1(k1_tarski(sK1),sK2,sK3) != k1_tarski(k1_funct_1(sK3,sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    k2_relset_1(k1_tarski(sK1),sK2,sK3) != k1_tarski(k1_funct_1(sK3,sK1)) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k2_relset_1(k1_tarski(sK1),sK2,sK3) != k1_tarski(k1_funct_1(sK3,sK1)) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.21/0.51    inference(negated_conjecture,[],[f12])).
% 0.21/0.51  fof(f12,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    ~spl4_5 | spl4_10),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f159])).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    $false | (~spl4_5 | spl4_10)),
% 0.21/0.51    inference(resolution,[],[f158,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    ~v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) | (~spl4_5 | spl4_10)),
% 0.21/0.51    inference(resolution,[],[f157,f111])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) | ~spl4_5),
% 0.21/0.51    inference(backward_demodulation,[],[f59,f105])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 0.21/0.51    inference(definition_unfolding,[],[f35,f57])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl4_10),
% 0.21/0.51    inference(resolution,[],[f152,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    ~v1_relat_1(sK3) | spl4_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f150])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    ~spl4_10 | spl4_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f148,f154,f150])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) | k2_relat_1(sK3) = k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) | ~v1_relat_1(sK3)) )),
% 0.21/0.51    inference(resolution,[],[f61,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    v1_funct_1(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_funct_1(X1) | k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0) | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f43,f57,f57])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    ~spl4_5 | spl4_8),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f144])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    $false | (~spl4_5 | spl4_8)),
% 0.21/0.51    inference(resolution,[],[f137,f111])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) | spl4_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f135])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    spl4_8 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    ~spl4_8 | spl4_9 | ~spl4_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f133,f119,f139,f135])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    spl4_6 <=> k2_relset_1(k1_relat_1(sK3),sK2,sK3) = k7_relset_1(k1_relat_1(sK3),sK2,sK3,k1_relat_1(sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    k2_relset_1(k1_relat_1(sK3),sK2,sK3) = k9_relat_1(sK3,k1_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) | ~spl4_6),
% 0.21/0.51    inference(superposition,[],[f55,f121])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    k2_relset_1(k1_relat_1(sK3),sK2,sK3) = k7_relset_1(k1_relat_1(sK3),sK2,sK3,k1_relat_1(sK3)) | ~spl4_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f119])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    ~spl4_1 | ~spl4_5 | spl4_7),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f127])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    $false | (~spl4_1 | ~spl4_5 | spl4_7)),
% 0.21/0.51    inference(resolution,[],[f125,f113])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    v1_funct_2(sK3,k1_relat_1(sK3),sK2) | (~spl4_1 | ~spl4_5)),
% 0.21/0.51    inference(backward_demodulation,[],[f73,f105])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) | ~spl4_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    spl4_1 <=> v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    ~v1_funct_2(sK3,k1_relat_1(sK3),sK2) | spl4_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f123])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    spl4_7 <=> v1_funct_2(sK3,k1_relat_1(sK3),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    spl4_6 | ~spl4_7 | spl4_3 | ~spl4_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f117,f103,f80,f123,f119])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    spl4_3 <=> k1_xboole_0 = sK2),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | ~v1_funct_2(sK3,k1_relat_1(sK3),sK2) | k2_relset_1(k1_relat_1(sK3),sK2,sK3) = k7_relset_1(k1_relat_1(sK3),sK2,sK3,k1_relat_1(sK3)) | ~spl4_5),
% 0.21/0.51    inference(resolution,[],[f116,f111])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_xboole_0 = X0 | ~v1_funct_2(sK3,X1,X0) | k7_relset_1(X1,X0,sK3,X1) = k2_relset_1(X1,X0,sK3)) )),
% 0.21/0.51    inference(resolution,[],[f53,f33])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_funct_2)).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    spl4_4),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f108])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    $false | spl4_4),
% 0.21/0.51    inference(resolution,[],[f101,f59])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) | spl4_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f99])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    spl4_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    ~spl4_4 | spl4_5 | ~spl4_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f97,f76,f103,f99])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    spl4_2 <=> k2_enumset1(sK1,sK1,sK1,sK1) = k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) | ~spl4_2),
% 0.21/0.51    inference(superposition,[],[f45,f78])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    k2_enumset1(sK1,sK1,sK1,sK1) = k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) | ~spl4_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f76])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ~spl4_3),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f93])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    $false | ~spl4_3),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f92])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | ~spl4_3),
% 0.21/0.51    inference(superposition,[],[f36,f82])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | ~spl4_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f80])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    k1_xboole_0 != sK2),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    spl4_1),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    $false | spl4_1),
% 0.21/0.51    inference(resolution,[],[f74,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2)),
% 0.21/0.51    inference(definition_unfolding,[],[f34,f57])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    v1_funct_2(sK3,k1_tarski(sK1),sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ~v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) | spl4_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f72])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ~spl4_1 | spl4_2 | spl4_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f70,f80,f76,f72])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) | ~v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2)),
% 0.21/0.51    inference(resolution,[],[f69,f59])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = X2 | k1_relset_1(X1,X2,X0) = X1 | ~v1_funct_2(X0,X1,X2)) )),
% 0.21/0.51    inference(resolution,[],[f46,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (sP0(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(definition_folding,[],[f22,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 0.21/0.51    inference(rectify,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f26])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (21158)------------------------------
% 0.21/0.51  % (21158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21158)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (21158)Memory used [KB]: 6268
% 0.21/0.51  % (21158)Time elapsed: 0.099 s
% 0.21/0.51  % (21158)------------------------------
% 0.21/0.51  % (21158)------------------------------
% 0.21/0.51  % (21145)Success in time 0.149 s
%------------------------------------------------------------------------------
