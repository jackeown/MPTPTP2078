%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 156 expanded)
%              Number of leaves         :   24 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :  209 ( 293 expanded)
%              Number of equality atoms :   20 (  50 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f504,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f78,f262,f320,f324,f381,f503])).

fof(f503,plain,
    ( spl3_10
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f499])).

fof(f499,plain,
    ( $false
    | spl3_10
    | ~ spl3_12 ),
    inference(resolution,[],[f491,f265])).

fof(f265,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl3_12
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f491,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl3_10 ),
    inference(resolution,[],[f307,f257])).

fof(f257,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl3_10
  <=> r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f307,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f107,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f107,plain,(
    ! [X2,X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,X1)),k3_tarski(k1_enumset1(X0,X0,X1)),X2))) ),
    inference(resolution,[],[f62,f59])).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f42,f56])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(k1_enumset1(X0,X0,X1)),X2)
      | r1_tarski(X0,X2) ) ),
    inference(definition_unfolding,[],[f51,f56])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f381,plain,(
    spl3_11 ),
    inference(avatar_contradiction_clause,[],[f379])).

fof(f379,plain,
    ( $false
    | spl3_11 ),
    inference(resolution,[],[f376,f179])).

fof(f179,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f175,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f175,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f123,f37])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f53,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
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

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f376,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl3_11 ),
    inference(resolution,[],[f261,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f56])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f261,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl3_11
  <=> r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f324,plain,(
    spl3_17 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | spl3_17 ),
    inference(resolution,[],[f319,f82])).

fof(f82,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f54,f37])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f319,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | spl3_17 ),
    inference(avatar_component_clause,[],[f317])).

fof(f317,plain,
    ( spl3_17
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f320,plain,
    ( ~ spl3_17
    | ~ spl3_2
    | spl3_12 ),
    inference(avatar_split_clause,[],[f314,f264,f73,f317])).

fof(f73,plain,
    ( spl3_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f314,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK0)
    | spl3_12 ),
    inference(resolution,[],[f266,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f45,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f266,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f264])).

fof(f262,plain,
    ( ~ spl3_2
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f236,f259,f255,f73])).

fof(f236,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | ~ r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f146,f57])).

fof(f57,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f38,f56])).

fof(f38,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f146,plain,(
    ! [X4,X3] :
      ( r1_tarski(k3_relat_1(X3),X4)
      | ~ r1_tarski(k2_relat_1(X3),X4)
      | ~ r1_tarski(k1_relat_1(X3),X4)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f63,f58])).

fof(f58,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f39,f56])).

fof(f39,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f78,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | spl3_1 ),
    inference(resolution,[],[f71,f41])).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f71,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl3_1
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f76,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f66,f73,f69])).

fof(f66,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f40,f37])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:49:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.41  % (7536)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.45  % (7523)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (7525)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (7521)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (7526)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (7535)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (7530)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (7524)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (7534)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (7525)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f504,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f76,f78,f262,f320,f324,f381,f503])).
% 0.21/0.48  fof(f503,plain,(
% 0.21/0.48    spl3_10 | ~spl3_12),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f499])).
% 0.21/0.48  fof(f499,plain,(
% 0.21/0.48    $false | (spl3_10 | ~spl3_12)),
% 0.21/0.48    inference(resolution,[],[f491,f265])).
% 0.21/0.48  fof(f265,plain,(
% 0.21/0.48    r1_tarski(k1_relat_1(sK2),sK0) | ~spl3_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f264])).
% 0.21/0.48  fof(f264,plain,(
% 0.21/0.48    spl3_12 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.48  fof(f491,plain,(
% 0.21/0.48    ~r1_tarski(k1_relat_1(sK2),sK0) | spl3_10),
% 0.21/0.48    inference(resolution,[],[f307,f257])).
% 0.21/0.48  fof(f257,plain,(
% 0.21/0.48    ~r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) | spl3_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f255])).
% 0.21/0.48  fof(f255,plain,(
% 0.21/0.48    spl3_10 <=> r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.48  fof(f307,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(superposition,[],[f107,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f46,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f43,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,X1)),k3_tarski(k1_enumset1(X0,X0,X1)),X2)))) )),
% 0.21/0.48    inference(resolution,[],[f62,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f42,f56])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(k1_enumset1(X0,X0,X1)),X2) | r1_tarski(X0,X2)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f51,f56])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.21/0.48  fof(f381,plain,(
% 0.21/0.48    spl3_11),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f379])).
% 0.21/0.48  fof(f379,plain,(
% 0.21/0.48    $false | spl3_11),
% 0.21/0.48    inference(resolution,[],[f376,f179])).
% 0.21/0.48  fof(f179,plain,(
% 0.21/0.48    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.21/0.48    inference(resolution,[],[f175,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.48    inference(nnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.48  fof(f175,plain,(
% 0.21/0.48    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.21/0.48    inference(resolution,[],[f123,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 0.21/0.48    inference(negated_conjecture,[],[f17])).
% 0.21/0.48  fof(f17,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f122])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(superposition,[],[f53,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.48  fof(f376,plain,(
% 0.21/0.48    ~r1_tarski(k2_relat_1(sK2),sK1) | spl3_11),
% 0.21/0.48    inference(resolution,[],[f261,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f50,f56])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.21/0.48  fof(f261,plain,(
% 0.21/0.48    ~r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) | spl3_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f259])).
% 0.21/0.48  fof(f259,plain,(
% 0.21/0.48    spl3_11 <=> r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.48  fof(f324,plain,(
% 0.21/0.48    spl3_17),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f323])).
% 0.21/0.48  fof(f323,plain,(
% 0.21/0.48    $false | spl3_17),
% 0.21/0.48    inference(resolution,[],[f319,f82])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    v4_relat_1(sK2,sK0)),
% 0.21/0.48    inference(resolution,[],[f54,f37])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f14])).
% 0.21/0.48  fof(f14,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.48  fof(f319,plain,(
% 0.21/0.48    ~v4_relat_1(sK2,sK0) | spl3_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f317])).
% 0.21/0.48  fof(f317,plain,(
% 0.21/0.48    spl3_17 <=> v4_relat_1(sK2,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.48  fof(f320,plain,(
% 0.21/0.48    ~spl3_17 | ~spl3_2 | spl3_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f314,f264,f73,f317])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    spl3_2 <=> v1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f314,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | ~v4_relat_1(sK2,sK0) | spl3_12),
% 0.21/0.48    inference(resolution,[],[f266,f87])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f86])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(superposition,[],[f45,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.21/0.48  fof(f266,plain,(
% 0.21/0.48    ~r1_tarski(k1_relat_1(sK2),sK0) | spl3_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f264])).
% 0.21/0.48  fof(f262,plain,(
% 0.21/0.48    ~spl3_2 | ~spl3_10 | ~spl3_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f236,f259,f255,f73])).
% 0.21/0.48  fof(f236,plain,(
% 0.21/0.48    ~r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) | ~r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) | ~v1_relat_1(sK2)),
% 0.21/0.48    inference(resolution,[],[f146,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ~r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))),
% 0.21/0.48    inference(definition_unfolding,[],[f38,f56])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    ( ! [X4,X3] : (r1_tarski(k3_relat_1(X3),X4) | ~r1_tarski(k2_relat_1(X3),X4) | ~r1_tarski(k1_relat_1(X3),X4) | ~v1_relat_1(X3)) )),
% 0.21/0.48    inference(superposition,[],[f63,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0] : (k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f39,f56])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f55,f56])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    spl3_1),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f77])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    $false | spl3_1),
% 0.21/0.48    inference(resolution,[],[f71,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    spl3_1 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ~spl3_1 | spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f66,f73,f69])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.48    inference(resolution,[],[f40,f37])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (7525)------------------------------
% 0.21/0.48  % (7525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (7525)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (7525)Memory used [KB]: 6396
% 0.21/0.48  % (7525)Time elapsed: 0.059 s
% 0.21/0.48  % (7525)------------------------------
% 0.21/0.48  % (7525)------------------------------
% 0.21/0.48  % (7522)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (7528)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (7520)Success in time 0.127 s
%------------------------------------------------------------------------------
