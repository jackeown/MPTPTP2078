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
% DateTime   : Thu Dec  3 13:04:36 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 350 expanded)
%              Number of leaves         :   21 ( 107 expanded)
%              Depth                    :   16
%              Number of atoms          :  296 ( 858 expanded)
%              Number of equality atoms :  139 ( 410 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f209,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f146,f164,f166,f187,f197,f208])).

fof(f208,plain,(
    ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | ~ spl4_7 ),
    inference(resolution,[],[f206,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] : r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))
      | k1_xboole_0 != X3 ) ),
    inference(definition_unfolding,[],[f62,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
      | k1_xboole_0 != X3 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

fof(f206,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)))
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f204,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(f204,plain,
    ( ~ r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)))
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f100,f196])).

fof(f196,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl4_7
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f100,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f72,f92])).

fof(f92,plain,(
    ! [X0] : k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f73,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f42,f71])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f57])).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f36])).

% (28535)Refutation not found, incomplete strategy% (28535)------------------------------
% (28535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f36,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

% (28535)Termination reason: Refutation not found, incomplete strategy

% (28535)Memory used [KB]: 10746
% (28535)Time elapsed: 0.119 s
fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

% (28535)------------------------------
% (28535)------------------------------
fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f72,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f44,f71,f71])).

fof(f44,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f197,plain,
    ( ~ spl4_3
    | spl4_7
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f193,f104,f195,f139])).

fof(f139,plain,
    ( spl4_3
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f104,plain,
    ( spl4_1
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f193,plain,
    ( k1_xboole_0 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(trivial_inequality_removal,[],[f192])).

fof(f192,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(superposition,[],[f48,f105])).

fof(f105,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f187,plain,(
    ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f94,f185])).

fof(f185,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl4_6 ),
    inference(resolution,[],[f167,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
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

fof(f167,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f100,f163])).

fof(f163,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl4_6
  <=> k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f94,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f73,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f166,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f41,f160])).

fof(f160,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl4_5
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f41,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f164,plain,
    ( ~ spl4_3
    | ~ spl4_5
    | spl4_6
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f157,f107,f162,f159,f139])).

fof(f107,plain,
    ( spl4_2
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f157,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(equality_resolution,[],[f119])).

fof(f119,plain,
    ( ! [X6] :
        ( k1_relat_1(sK3) != k1_relat_1(X6)
        | k2_relat_1(X6) = k2_enumset1(k1_funct_1(X6,sK0),k1_funct_1(X6,sK0),k1_funct_1(X6,sK0),k1_funct_1(X6,sK0))
        | ~ v1_funct_1(X6)
        | ~ v1_relat_1(X6) )
    | ~ spl4_2 ),
    inference(superposition,[],[f74,f108])).

fof(f108,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0)
      | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f53,f71,f71])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f146,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f94,f140])).

fof(f140,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f139])).

fof(f109,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f102,f107,f104])).

fof(f102,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
    inference(resolution,[],[f99,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))
      | k2_enumset1(X0,X0,X0,X2) = X3
      | k2_enumset1(X1,X1,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X1) = X3
      | k2_enumset1(X2,X2,X2,X2) = X3
      | k2_enumset1(X1,X1,X1,X1) = X3
      | k2_enumset1(X0,X0,X0,X0) = X3
      | k1_xboole_0 = X3
      | k2_enumset1(X0,X0,X1,X2) = X3 ) ),
    inference(definition_unfolding,[],[f61,f57,f70,f70,f70,f71,f71,f71,f57])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | k2_tarski(X0,X2) = X3
      | k2_tarski(X1,X2) = X3
      | k2_tarski(X0,X1) = X3
      | k1_tarski(X2) = X3
      | k1_tarski(X1) = X3
      | k1_tarski(X0) = X3
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f99,plain,(
    r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(global_subsumption,[],[f94,f98])).

fof(f98,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f52,f97])).

fof(f97,plain,(
    sK3 = k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(global_subsumption,[],[f94,f96])).

fof(f96,plain,
    ( sK3 = k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f93,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f93,plain,(
    v4_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f73,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n020.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 18:53:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.50  % (28526)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (28526)Refutation not found, incomplete strategy% (28526)------------------------------
% 0.21/0.50  % (28526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (28533)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (28526)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (28526)Memory used [KB]: 1791
% 0.21/0.51  % (28526)Time elapsed: 0.093 s
% 0.21/0.51  % (28526)------------------------------
% 0.21/0.51  % (28526)------------------------------
% 0.21/0.51  % (28529)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (28541)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (28534)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (28528)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (28535)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (28540)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (28542)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (28550)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (28548)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (28544)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (28537)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (28531)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (28530)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (28551)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.38/0.54  % (28549)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.38/0.54  % (28527)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.38/0.54  % (28552)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.38/0.54  % (28532)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.38/0.54  % (28553)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.38/0.54  % (28555)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.38/0.54  % (28554)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.38/0.54  % (28528)Refutation found. Thanks to Tanya!
% 1.38/0.54  % SZS status Theorem for theBenchmark
% 1.38/0.54  % SZS output start Proof for theBenchmark
% 1.38/0.54  fof(f209,plain,(
% 1.38/0.54    $false),
% 1.38/0.54    inference(avatar_sat_refutation,[],[f109,f146,f164,f166,f187,f197,f208])).
% 1.38/0.54  fof(f208,plain,(
% 1.38/0.54    ~spl4_7),
% 1.38/0.54    inference(avatar_contradiction_clause,[],[f207])).
% 1.38/0.54  fof(f207,plain,(
% 1.38/0.54    $false | ~spl4_7),
% 1.38/0.54    inference(resolution,[],[f206,f91])).
% 1.38/0.54  fof(f91,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X1,X2))) )),
% 1.38/0.54    inference(equality_resolution,[],[f82])).
% 1.38/0.54  fof(f82,plain,(
% 1.38/0.54    ( ! [X2,X0,X3,X1] : (r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) | k1_xboole_0 != X3) )),
% 1.38/0.54    inference(definition_unfolding,[],[f62,f57])).
% 1.38/0.54  fof(f57,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f3])).
% 1.38/0.54  fof(f3,axiom,(
% 1.38/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.38/0.54  fof(f62,plain,(
% 1.38/0.54    ( ! [X2,X0,X3,X1] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) | k1_xboole_0 != X3) )),
% 1.38/0.54    inference(cnf_transformation,[],[f40])).
% 1.38/0.54  fof(f40,plain,(
% 1.38/0.54    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 1.38/0.54    inference(flattening,[],[f39])).
% 1.38/0.54  fof(f39,plain,(
% 1.38/0.54    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 1.38/0.54    inference(nnf_transformation,[],[f35])).
% 1.38/0.54  fof(f35,plain,(
% 1.38/0.54    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 1.38/0.54    inference(ennf_transformation,[],[f4])).
% 1.38/0.54  fof(f4,axiom,(
% 1.38/0.54    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).
% 1.38/0.54  fof(f206,plain,(
% 1.38/0.54    ~r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) | ~spl4_7),
% 1.38/0.54    inference(forward_demodulation,[],[f204,f46])).
% 1.38/0.54  fof(f46,plain,(
% 1.38/0.54    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f9])).
% 1.38/0.54  fof(f9,axiom,(
% 1.38/0.54    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 1.38/0.54  fof(f204,plain,(
% 1.38/0.54    ~r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) | ~spl4_7),
% 1.38/0.54    inference(backward_demodulation,[],[f100,f196])).
% 1.38/0.54  fof(f196,plain,(
% 1.38/0.54    k1_xboole_0 = sK3 | ~spl4_7),
% 1.38/0.54    inference(avatar_component_clause,[],[f195])).
% 1.38/0.54  fof(f195,plain,(
% 1.38/0.54    spl4_7 <=> k1_xboole_0 = sK3),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.38/0.54  fof(f100,plain,(
% 1.38/0.54    ~r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.38/0.54    inference(backward_demodulation,[],[f72,f92])).
% 1.38/0.54  fof(f92,plain,(
% 1.38/0.54    ( ! [X0] : (k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 1.38/0.54    inference(resolution,[],[f73,f60])).
% 1.38/0.54  fof(f60,plain,(
% 1.38/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f34])).
% 1.38/0.54  fof(f34,plain,(
% 1.38/0.54    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.54    inference(ennf_transformation,[],[f16])).
% 1.38/0.54  fof(f16,axiom,(
% 1.38/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.38/0.54  fof(f73,plain,(
% 1.38/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.38/0.54    inference(definition_unfolding,[],[f42,f71])).
% 1.38/0.54  fof(f71,plain,(
% 1.38/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.38/0.54    inference(definition_unfolding,[],[f47,f70])).
% 1.38/0.54  fof(f70,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.38/0.54    inference(definition_unfolding,[],[f50,f57])).
% 1.38/0.54  fof(f50,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f2])).
% 1.38/0.54  fof(f2,axiom,(
% 1.38/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.38/0.54  fof(f47,plain,(
% 1.38/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f1])).
% 1.38/0.54  fof(f1,axiom,(
% 1.38/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.38/0.54  fof(f42,plain,(
% 1.38/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.38/0.54    inference(cnf_transformation,[],[f37])).
% 1.38/0.54  fof(f37,plain,(
% 1.38/0.54    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 1.38/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f36])).
% 1.38/0.54  % (28535)Refutation not found, incomplete strategy% (28535)------------------------------
% 1.38/0.54  % (28535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  fof(f36,plain,(
% 1.38/0.54    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 1.38/0.54    introduced(choice_axiom,[])).
% 1.38/0.54  % (28535)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (28535)Memory used [KB]: 10746
% 1.38/0.54  % (28535)Time elapsed: 0.119 s
% 1.38/0.54  fof(f23,plain,(
% 1.38/0.54    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 1.38/0.54    inference(flattening,[],[f22])).
% 1.38/0.54  % (28535)------------------------------
% 1.38/0.54  % (28535)------------------------------
% 1.38/0.54  fof(f22,plain,(
% 1.38/0.54    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 1.38/0.54    inference(ennf_transformation,[],[f19])).
% 1.38/0.54  fof(f19,plain,(
% 1.38/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.38/0.54    inference(pure_predicate_removal,[],[f18])).
% 1.38/0.54  fof(f18,negated_conjecture,(
% 1.38/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.38/0.54    inference(negated_conjecture,[],[f17])).
% 1.38/0.54  fof(f17,conjecture,(
% 1.38/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 1.38/0.54  fof(f72,plain,(
% 1.38/0.54    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.38/0.54    inference(definition_unfolding,[],[f44,f71,f71])).
% 1.38/0.54  fof(f44,plain,(
% 1.38/0.54    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.38/0.54    inference(cnf_transformation,[],[f37])).
% 1.38/0.54  fof(f197,plain,(
% 1.38/0.54    ~spl4_3 | spl4_7 | ~spl4_1),
% 1.38/0.54    inference(avatar_split_clause,[],[f193,f104,f195,f139])).
% 1.38/0.54  fof(f139,plain,(
% 1.38/0.54    spl4_3 <=> v1_relat_1(sK3)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.38/0.54  fof(f104,plain,(
% 1.38/0.54    spl4_1 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.38/0.54  fof(f193,plain,(
% 1.38/0.54    k1_xboole_0 = sK3 | ~v1_relat_1(sK3) | ~spl4_1),
% 1.38/0.54    inference(trivial_inequality_removal,[],[f192])).
% 1.38/0.54  fof(f192,plain,(
% 1.38/0.54    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK3 | ~v1_relat_1(sK3) | ~spl4_1),
% 1.38/0.54    inference(superposition,[],[f48,f105])).
% 1.38/0.54  fof(f105,plain,(
% 1.38/0.54    k1_xboole_0 = k1_relat_1(sK3) | ~spl4_1),
% 1.38/0.54    inference(avatar_component_clause,[],[f104])).
% 1.38/0.54  fof(f48,plain,(
% 1.38/0.54    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f25])).
% 1.38/0.54  fof(f25,plain,(
% 1.38/0.54    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.38/0.54    inference(flattening,[],[f24])).
% 1.38/0.54  fof(f24,plain,(
% 1.38/0.54    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.38/0.54    inference(ennf_transformation,[],[f11])).
% 1.38/0.54  fof(f11,axiom,(
% 1.38/0.54    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.38/0.54  fof(f187,plain,(
% 1.38/0.54    ~spl4_6),
% 1.38/0.54    inference(avatar_contradiction_clause,[],[f186])).
% 1.38/0.54  fof(f186,plain,(
% 1.38/0.54    $false | ~spl4_6),
% 1.38/0.54    inference(subsumption_resolution,[],[f94,f185])).
% 1.38/0.54  fof(f185,plain,(
% 1.38/0.54    ~v1_relat_1(sK3) | ~spl4_6),
% 1.38/0.54    inference(resolution,[],[f167,f51])).
% 1.38/0.54  fof(f51,plain,(
% 1.38/0.54    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f26])).
% 1.38/0.54  fof(f26,plain,(
% 1.38/0.54    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.38/0.54    inference(ennf_transformation,[],[f8])).
% 1.38/0.54  fof(f8,axiom,(
% 1.38/0.54    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 1.38/0.54  fof(f167,plain,(
% 1.38/0.54    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~spl4_6),
% 1.38/0.54    inference(backward_demodulation,[],[f100,f163])).
% 1.38/0.54  fof(f163,plain,(
% 1.38/0.54    k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~spl4_6),
% 1.38/0.54    inference(avatar_component_clause,[],[f162])).
% 1.38/0.54  fof(f162,plain,(
% 1.38/0.54    spl4_6 <=> k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.38/0.54  fof(f94,plain,(
% 1.38/0.54    v1_relat_1(sK3)),
% 1.38/0.54    inference(resolution,[],[f73,f58])).
% 1.38/0.54  fof(f58,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f32])).
% 1.38/0.54  fof(f32,plain,(
% 1.38/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.54    inference(ennf_transformation,[],[f14])).
% 1.38/0.54  fof(f14,axiom,(
% 1.38/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.38/0.54  fof(f166,plain,(
% 1.38/0.54    spl4_5),
% 1.38/0.54    inference(avatar_contradiction_clause,[],[f165])).
% 1.38/0.54  fof(f165,plain,(
% 1.38/0.54    $false | spl4_5),
% 1.38/0.54    inference(subsumption_resolution,[],[f41,f160])).
% 1.38/0.54  fof(f160,plain,(
% 1.38/0.54    ~v1_funct_1(sK3) | spl4_5),
% 1.38/0.54    inference(avatar_component_clause,[],[f159])).
% 1.38/0.54  fof(f159,plain,(
% 1.38/0.54    spl4_5 <=> v1_funct_1(sK3)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.38/0.54  fof(f41,plain,(
% 1.38/0.54    v1_funct_1(sK3)),
% 1.38/0.54    inference(cnf_transformation,[],[f37])).
% 1.38/0.54  fof(f164,plain,(
% 1.38/0.54    ~spl4_3 | ~spl4_5 | spl4_6 | ~spl4_2),
% 1.38/0.54    inference(avatar_split_clause,[],[f157,f107,f162,f159,f139])).
% 1.38/0.54  fof(f107,plain,(
% 1.38/0.54    spl4_2 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.38/0.54  fof(f157,plain,(
% 1.38/0.54    k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_2),
% 1.38/0.54    inference(equality_resolution,[],[f119])).
% 1.38/0.54  fof(f119,plain,(
% 1.38/0.54    ( ! [X6] : (k1_relat_1(sK3) != k1_relat_1(X6) | k2_relat_1(X6) = k2_enumset1(k1_funct_1(X6,sK0),k1_funct_1(X6,sK0),k1_funct_1(X6,sK0),k1_funct_1(X6,sK0)) | ~v1_funct_1(X6) | ~v1_relat_1(X6)) ) | ~spl4_2),
% 1.38/0.54    inference(superposition,[],[f74,f108])).
% 1.38/0.54  fof(f108,plain,(
% 1.38/0.54    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | ~spl4_2),
% 1.38/0.54    inference(avatar_component_clause,[],[f107])).
% 1.38/0.54  fof(f74,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0) | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.38/0.54    inference(definition_unfolding,[],[f53,f71,f71])).
% 1.38/0.54  fof(f53,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f29])).
% 1.38/0.54  fof(f29,plain,(
% 1.38/0.54    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.38/0.54    inference(flattening,[],[f28])).
% 1.38/0.54  fof(f28,plain,(
% 1.38/0.54    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.38/0.54    inference(ennf_transformation,[],[f13])).
% 1.38/0.54  fof(f13,axiom,(
% 1.38/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 1.38/0.54  fof(f146,plain,(
% 1.38/0.54    spl4_3),
% 1.38/0.54    inference(avatar_contradiction_clause,[],[f145])).
% 1.38/0.54  fof(f145,plain,(
% 1.38/0.54    $false | spl4_3),
% 1.38/0.54    inference(subsumption_resolution,[],[f94,f140])).
% 1.38/0.54  fof(f140,plain,(
% 1.38/0.54    ~v1_relat_1(sK3) | spl4_3),
% 1.38/0.54    inference(avatar_component_clause,[],[f139])).
% 1.38/0.54  fof(f109,plain,(
% 1.38/0.54    spl4_1 | spl4_2),
% 1.38/0.54    inference(avatar_split_clause,[],[f102,f107,f104])).
% 1.38/0.54  fof(f102,plain,(
% 1.38/0.54    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.38/0.54    inference(duplicate_literal_removal,[],[f101])).
% 1.38/0.54  fof(f101,plain,(
% 1.38/0.54    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)),
% 1.38/0.54    inference(resolution,[],[f99,f83])).
% 1.38/0.54  fof(f83,plain,(
% 1.38/0.54    ( ! [X2,X0,X3,X1] : (~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | k1_xboole_0 = X3 | k2_enumset1(X0,X0,X1,X2) = X3) )),
% 1.38/0.54    inference(definition_unfolding,[],[f61,f57,f70,f70,f70,f71,f71,f71,f57])).
% 1.38/0.54  fof(f61,plain,(
% 1.38/0.54    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 1.38/0.54    inference(cnf_transformation,[],[f40])).
% 1.38/0.54  fof(f99,plain,(
% 1.38/0.54    r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.38/0.54    inference(global_subsumption,[],[f94,f98])).
% 1.38/0.54  fof(f98,plain,(
% 1.38/0.54    r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK3)),
% 1.38/0.54    inference(superposition,[],[f52,f97])).
% 1.38/0.54  fof(f97,plain,(
% 1.38/0.54    sK3 = k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.38/0.54    inference(global_subsumption,[],[f94,f96])).
% 1.38/0.54  fof(f96,plain,(
% 1.38/0.54    sK3 = k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK3)),
% 1.38/0.54    inference(resolution,[],[f93,f54])).
% 1.38/0.54  fof(f54,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f31])).
% 1.38/0.54  fof(f31,plain,(
% 1.38/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.38/0.54    inference(flattening,[],[f30])).
% 1.38/0.54  fof(f30,plain,(
% 1.38/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.38/0.54    inference(ennf_transformation,[],[f10])).
% 1.38/0.54  fof(f10,axiom,(
% 1.38/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.38/0.54  fof(f93,plain,(
% 1.38/0.54    v4_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.38/0.54    inference(resolution,[],[f73,f59])).
% 1.38/0.54  fof(f59,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f33])).
% 1.38/0.54  fof(f33,plain,(
% 1.38/0.54    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.54    inference(ennf_transformation,[],[f20])).
% 1.38/0.54  fof(f20,plain,(
% 1.38/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.38/0.54    inference(pure_predicate_removal,[],[f15])).
% 1.38/0.54  fof(f15,axiom,(
% 1.38/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.38/0.54  fof(f52,plain,(
% 1.38/0.54    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f27])).
% 1.38/0.54  fof(f27,plain,(
% 1.38/0.54    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.38/0.54    inference(ennf_transformation,[],[f12])).
% 1.38/0.54  fof(f12,axiom,(
% 1.38/0.54    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 1.38/0.54  % SZS output end Proof for theBenchmark
% 1.38/0.54  % (28528)------------------------------
% 1.38/0.54  % (28528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (28528)Termination reason: Refutation
% 1.38/0.54  
% 1.38/0.54  % (28528)Memory used [KB]: 10746
% 1.38/0.54  % (28528)Time elapsed: 0.122 s
% 1.38/0.54  % (28528)------------------------------
% 1.38/0.54  % (28528)------------------------------
% 1.38/0.55  % (28522)Success in time 0.181 s
%------------------------------------------------------------------------------
