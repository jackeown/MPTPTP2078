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
% DateTime   : Thu Dec  3 13:04:35 EST 2020

% Result     : Theorem 1.85s
% Output     : Refutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 273 expanded)
%              Number of leaves         :   21 (  88 expanded)
%              Depth                    :   14
%              Number of atoms          :  334 ( 697 expanded)
%              Number of equality atoms :  163 ( 329 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f381,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f131,f263,f288,f294,f304,f380])).

fof(f380,plain,
    ( ~ spl4_8
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f379])).

fof(f379,plain,
    ( $false
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f356,f296])).

fof(f296,plain,
    ( ! [X3] : r1_tarski(k9_relat_1(sK3,X3),k2_relat_1(sK3))
    | ~ spl4_8 ),
    inference(resolution,[],[f257,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f257,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl4_8
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f356,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f101,f262])).

fof(f262,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f260])).

fof(f260,plain,
    ( spl4_9
  <=> k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f101,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(subsumption_resolution,[],[f99,f73])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f40,f71])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK3,k1_tarski(sK0),sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f32])).

fof(f32,plain,
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

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

% (5443)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f99,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(superposition,[],[f72,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f72,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f42,f71,f71])).

fof(f42,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f304,plain,(
    ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f303])).

fof(f303,plain,
    ( $false
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f302,f43])).

fof(f43,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f302,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))))
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f298,f44])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(f298,plain,
    ( ~ m1_subset_1(k9_relat_1(k1_xboole_0,sK2),k1_zfmisc_1(k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))))
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f100,f287])).

fof(f287,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl4_11
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f100,plain,(
    ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))) ),
    inference(subsumption_resolution,[],[f98,f73])).

fof(f98,plain,
    ( ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(superposition,[],[f94,f60])).

fof(f94,plain,(
    ~ m1_subset_1(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k1_zfmisc_1(k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))) ),
    inference(resolution,[],[f72,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f294,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f293])).

fof(f293,plain,
    ( $false
    | spl4_8 ),
    inference(subsumption_resolution,[],[f73,f289])).

fof(f289,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_8 ),
    inference(resolution,[],[f258,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f258,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f256])).

fof(f288,plain,
    ( ~ spl4_8
    | spl4_11
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f283,f124,f285,f256])).

fof(f124,plain,
    ( spl4_1
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f283,plain,
    ( k1_xboole_0 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(trivial_inequality_removal,[],[f282])).

fof(f282,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(superposition,[],[f46,f126])).

fof(f126,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f124])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f263,plain,
    ( ~ spl4_8
    | spl4_9
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f254,f128,f260,f256])).

fof(f128,plain,
    ( spl4_2
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f254,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(trivial_inequality_removal,[],[f253])).

fof(f253,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f158,f38])).

fof(f38,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f158,plain,
    ( ! [X10] :
        ( ~ v1_funct_1(X10)
        | k2_relat_1(X10) = k2_enumset1(k1_funct_1(X10,sK0),k1_funct_1(X10,sK0),k1_funct_1(X10,sK0),k1_funct_1(X10,sK0))
        | k1_relat_1(sK3) != k1_relat_1(X10)
        | ~ v1_relat_1(X10) )
    | ~ spl4_2 ),
    inference(superposition,[],[f75,f130])).

fof(f130,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f128])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0)
      | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f52,f71,f71])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f131,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f122,f128,f124])).

fof(f122,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
    inference(resolution,[],[f118,f73])).

fof(f118,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(X1,X1,X2,X3),X6)))
      | k1_relat_1(X0) = k2_enumset1(X3,X3,X3,X3)
      | k1_relat_1(X0) = k2_enumset1(X2,X2,X2,X2)
      | k1_relat_1(X0) = k2_enumset1(X1,X1,X1,X1)
      | k1_xboole_0 = k1_relat_1(X0)
      | k1_relat_1(X0) = k2_enumset1(X1,X1,X2,X3)
      | k1_relat_1(X0) = k2_enumset1(X2,X2,X2,X3)
      | k1_relat_1(X0) = k2_enumset1(X1,X1,X1,X3)
      | k1_relat_1(X0) = k2_enumset1(X1,X1,X1,X2) ) ),
    inference(condensation,[],[f117])).

fof(f117,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k1_relat_1(X0) = k2_enumset1(X1,X1,X1,X2)
      | k1_relat_1(X0) = k2_enumset1(X3,X3,X3,X3)
      | k1_relat_1(X0) = k2_enumset1(X2,X2,X2,X2)
      | k1_relat_1(X0) = k2_enumset1(X1,X1,X1,X1)
      | k1_xboole_0 = k1_relat_1(X0)
      | k1_relat_1(X0) = k2_enumset1(X1,X1,X2,X3)
      | k1_relat_1(X0) = k2_enumset1(X2,X2,X2,X3)
      | k1_relat_1(X0) = k2_enumset1(X1,X1,X1,X3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(X1,X1,X2,X3),X6))) ) ),
    inference(resolution,[],[f116,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f116,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v4_relat_1(X0,k2_enumset1(X3,X3,X1,X2))
      | k1_relat_1(X0) = k2_enumset1(X3,X3,X3,X1)
      | k1_relat_1(X0) = k2_enumset1(X2,X2,X2,X2)
      | k1_relat_1(X0) = k2_enumset1(X1,X1,X1,X1)
      | k1_relat_1(X0) = k2_enumset1(X3,X3,X3,X3)
      | k1_xboole_0 = k1_relat_1(X0)
      | k1_relat_1(X0) = k2_enumset1(X3,X3,X1,X2)
      | k1_relat_1(X0) = k2_enumset1(X1,X1,X1,X2)
      | k1_relat_1(X0) = k2_enumset1(X3,X3,X3,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(resolution,[],[f113,f56])).

fof(f113,plain,(
    ! [X30,X28,X31,X29] :
      ( ~ v1_relat_1(X30)
      | k1_relat_1(X30) = k2_enumset1(X31,X31,X31,X29)
      | k1_relat_1(X30) = k2_enumset1(X28,X28,X28,X31)
      | k1_relat_1(X30) = k2_enumset1(X29,X29,X29,X29)
      | k1_relat_1(X30) = k2_enumset1(X31,X31,X31,X31)
      | k1_relat_1(X30) = k2_enumset1(X28,X28,X28,X28)
      | k1_xboole_0 = k1_relat_1(X30)
      | k1_relat_1(X30) = k2_enumset1(X28,X28,X31,X29)
      | ~ v4_relat_1(X30,k2_enumset1(X28,X28,X31,X29))
      | k2_enumset1(X28,X28,X28,X29) = k1_relat_1(X30) ) ),
    inference(resolution,[],[f84,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f84,plain,(
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
    inference(definition_unfolding,[],[f61,f55,f70,f70,f70,f71,f71,f71,f55])).

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
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:38:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (5466)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (5450)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (5446)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.58/0.58  % (5454)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.58/0.58  % (5456)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.58/0.59  % (5470)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.85/0.59  % (5448)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.85/0.59  % (5467)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.85/0.60  % (5454)Refutation not found, incomplete strategy% (5454)------------------------------
% 1.85/0.60  % (5454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.60  % (5454)Termination reason: Refutation not found, incomplete strategy
% 1.85/0.60  
% 1.85/0.60  % (5454)Memory used [KB]: 10618
% 1.85/0.60  % (5454)Time elapsed: 0.146 s
% 1.85/0.60  % (5454)------------------------------
% 1.85/0.60  % (5454)------------------------------
% 1.85/0.60  % (5458)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.85/0.60  % (5446)Refutation found. Thanks to Tanya!
% 1.85/0.60  % SZS status Theorem for theBenchmark
% 1.85/0.60  % SZS output start Proof for theBenchmark
% 1.85/0.60  fof(f381,plain,(
% 1.85/0.60    $false),
% 1.85/0.60    inference(avatar_sat_refutation,[],[f131,f263,f288,f294,f304,f380])).
% 1.85/0.60  fof(f380,plain,(
% 1.85/0.60    ~spl4_8 | ~spl4_9),
% 1.85/0.60    inference(avatar_contradiction_clause,[],[f379])).
% 1.85/0.60  fof(f379,plain,(
% 1.85/0.60    $false | (~spl4_8 | ~spl4_9)),
% 1.85/0.60    inference(subsumption_resolution,[],[f356,f296])).
% 1.85/0.60  fof(f296,plain,(
% 1.85/0.60    ( ! [X3] : (r1_tarski(k9_relat_1(sK3,X3),k2_relat_1(sK3))) ) | ~spl4_8),
% 1.85/0.60    inference(resolution,[],[f257,f49])).
% 1.85/0.60  fof(f49,plain,(
% 1.85/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))) )),
% 1.85/0.60    inference(cnf_transformation,[],[f22])).
% 1.85/0.60  fof(f22,plain,(
% 1.85/0.60    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.85/0.60    inference(ennf_transformation,[],[f9])).
% 1.85/0.60  fof(f9,axiom,(
% 1.85/0.60    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.85/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 1.85/0.60  fof(f257,plain,(
% 1.85/0.60    v1_relat_1(sK3) | ~spl4_8),
% 1.85/0.60    inference(avatar_component_clause,[],[f256])).
% 1.85/0.60  fof(f256,plain,(
% 1.85/0.60    spl4_8 <=> v1_relat_1(sK3)),
% 1.85/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.85/0.60  fof(f356,plain,(
% 1.85/0.60    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~spl4_9),
% 1.85/0.60    inference(backward_demodulation,[],[f101,f262])).
% 1.85/0.60  fof(f262,plain,(
% 1.85/0.60    k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~spl4_9),
% 1.85/0.60    inference(avatar_component_clause,[],[f260])).
% 1.85/0.60  fof(f260,plain,(
% 1.85/0.60    spl4_9 <=> k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)),
% 1.85/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.85/0.60  fof(f101,plain,(
% 1.85/0.60    ~r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.85/0.60    inference(subsumption_resolution,[],[f99,f73])).
% 1.85/0.60  fof(f73,plain,(
% 1.85/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.85/0.60    inference(definition_unfolding,[],[f40,f71])).
% 1.85/0.60  fof(f71,plain,(
% 1.85/0.60    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.85/0.60    inference(definition_unfolding,[],[f45,f70])).
% 1.85/0.60  fof(f70,plain,(
% 1.85/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.85/0.60    inference(definition_unfolding,[],[f48,f55])).
% 1.85/0.60  fof(f55,plain,(
% 1.85/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.85/0.60    inference(cnf_transformation,[],[f3])).
% 1.85/0.60  fof(f3,axiom,(
% 1.85/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.85/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.85/0.60  fof(f48,plain,(
% 1.85/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.85/0.60    inference(cnf_transformation,[],[f2])).
% 1.85/0.60  fof(f2,axiom,(
% 1.85/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.85/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.85/0.60  fof(f45,plain,(
% 1.85/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.85/0.60    inference(cnf_transformation,[],[f1])).
% 1.85/0.60  fof(f1,axiom,(
% 1.85/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.85/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.85/0.60  fof(f40,plain,(
% 1.85/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.85/0.60    inference(cnf_transformation,[],[f33])).
% 1.85/0.60  fof(f33,plain,(
% 1.85/0.60    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3)),
% 1.85/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f32])).
% 1.85/0.60  fof(f32,plain,(
% 1.85/0.60    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3))),
% 1.85/0.60    introduced(choice_axiom,[])).
% 1.85/0.60  fof(f19,plain,(
% 1.85/0.60    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 1.85/0.60    inference(flattening,[],[f18])).
% 1.85/0.60  % (5443)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.85/0.60  fof(f18,plain,(
% 1.85/0.60    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 1.85/0.60    inference(ennf_transformation,[],[f17])).
% 1.85/0.60  fof(f17,negated_conjecture,(
% 1.85/0.60    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.85/0.60    inference(negated_conjecture,[],[f16])).
% 1.85/0.60  fof(f16,conjecture,(
% 1.85/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.85/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 1.85/0.60  fof(f99,plain,(
% 1.85/0.60    ~r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.85/0.60    inference(superposition,[],[f72,f60])).
% 1.85/0.60  fof(f60,plain,(
% 1.85/0.60    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.85/0.60    inference(cnf_transformation,[],[f30])).
% 1.85/0.60  fof(f30,plain,(
% 1.85/0.60    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.85/0.60    inference(ennf_transformation,[],[f15])).
% 1.85/0.60  fof(f15,axiom,(
% 1.85/0.60    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.85/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.85/0.60  fof(f72,plain,(
% 1.85/0.60    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.85/0.60    inference(definition_unfolding,[],[f42,f71,f71])).
% 1.85/0.60  fof(f42,plain,(
% 1.85/0.60    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.85/0.60    inference(cnf_transformation,[],[f33])).
% 1.85/0.60  fof(f304,plain,(
% 1.85/0.60    ~spl4_11),
% 1.85/0.60    inference(avatar_contradiction_clause,[],[f303])).
% 1.85/0.60  fof(f303,plain,(
% 1.85/0.60    $false | ~spl4_11),
% 1.85/0.60    inference(subsumption_resolution,[],[f302,f43])).
% 1.85/0.60  fof(f43,plain,(
% 1.85/0.60    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.85/0.60    inference(cnf_transformation,[],[f5])).
% 1.85/0.60  fof(f5,axiom,(
% 1.85/0.60    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.85/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.85/0.60  fof(f302,plain,(
% 1.85/0.60    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)))) | ~spl4_11),
% 1.85/0.60    inference(forward_demodulation,[],[f298,f44])).
% 1.85/0.60  fof(f44,plain,(
% 1.85/0.60    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 1.85/0.60    inference(cnf_transformation,[],[f10])).
% 1.85/0.60  fof(f10,axiom,(
% 1.85/0.60    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 1.85/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 1.85/0.60  fof(f298,plain,(
% 1.85/0.60    ~m1_subset_1(k9_relat_1(k1_xboole_0,sK2),k1_zfmisc_1(k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)))) | ~spl4_11),
% 1.85/0.60    inference(backward_demodulation,[],[f100,f287])).
% 1.85/0.60  fof(f287,plain,(
% 1.85/0.60    k1_xboole_0 = sK3 | ~spl4_11),
% 1.85/0.60    inference(avatar_component_clause,[],[f285])).
% 1.85/0.60  fof(f285,plain,(
% 1.85/0.60    spl4_11 <=> k1_xboole_0 = sK3),
% 1.85/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.85/0.60  fof(f100,plain,(
% 1.85/0.60    ~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))))),
% 1.85/0.60    inference(subsumption_resolution,[],[f98,f73])).
% 1.85/0.60  fof(f98,plain,(
% 1.85/0.60    ~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.85/0.60    inference(superposition,[],[f94,f60])).
% 1.85/0.60  fof(f94,plain,(
% 1.85/0.60    ~m1_subset_1(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k1_zfmisc_1(k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))))),
% 1.85/0.60    inference(resolution,[],[f72,f53])).
% 1.85/0.60  fof(f53,plain,(
% 1.85/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.85/0.60    inference(cnf_transformation,[],[f35])).
% 1.85/0.60  fof(f35,plain,(
% 1.85/0.60    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.85/0.60    inference(nnf_transformation,[],[f6])).
% 1.85/0.60  fof(f6,axiom,(
% 1.85/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.85/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.85/0.60  fof(f294,plain,(
% 1.85/0.60    spl4_8),
% 1.85/0.60    inference(avatar_contradiction_clause,[],[f293])).
% 1.85/0.60  fof(f293,plain,(
% 1.85/0.60    $false | spl4_8),
% 1.85/0.60    inference(subsumption_resolution,[],[f73,f289])).
% 1.85/0.60  fof(f289,plain,(
% 1.85/0.60    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_8),
% 1.85/0.60    inference(resolution,[],[f258,f56])).
% 1.85/0.60  fof(f56,plain,(
% 1.85/0.60    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.85/0.60    inference(cnf_transformation,[],[f26])).
% 1.85/0.60  fof(f26,plain,(
% 1.85/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.85/0.60    inference(ennf_transformation,[],[f13])).
% 1.85/0.60  fof(f13,axiom,(
% 1.85/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.85/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.85/0.60  fof(f258,plain,(
% 1.85/0.60    ~v1_relat_1(sK3) | spl4_8),
% 1.85/0.60    inference(avatar_component_clause,[],[f256])).
% 1.85/0.60  fof(f288,plain,(
% 1.85/0.60    ~spl4_8 | spl4_11 | ~spl4_1),
% 1.85/0.60    inference(avatar_split_clause,[],[f283,f124,f285,f256])).
% 1.85/0.60  fof(f124,plain,(
% 1.85/0.60    spl4_1 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 1.85/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.85/0.60  fof(f283,plain,(
% 1.85/0.60    k1_xboole_0 = sK3 | ~v1_relat_1(sK3) | ~spl4_1),
% 1.85/0.60    inference(trivial_inequality_removal,[],[f282])).
% 1.85/0.60  fof(f282,plain,(
% 1.85/0.60    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK3 | ~v1_relat_1(sK3) | ~spl4_1),
% 1.85/0.60    inference(superposition,[],[f46,f126])).
% 1.85/0.60  fof(f126,plain,(
% 1.85/0.60    k1_xboole_0 = k1_relat_1(sK3) | ~spl4_1),
% 1.85/0.60    inference(avatar_component_clause,[],[f124])).
% 1.85/0.60  fof(f46,plain,(
% 1.85/0.60    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.85/0.60    inference(cnf_transformation,[],[f21])).
% 1.85/0.60  fof(f21,plain,(
% 1.85/0.60    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.85/0.60    inference(flattening,[],[f20])).
% 1.85/0.60  fof(f20,plain,(
% 1.85/0.60    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.85/0.60    inference(ennf_transformation,[],[f11])).
% 1.85/0.60  fof(f11,axiom,(
% 1.85/0.60    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.85/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.85/0.60  fof(f263,plain,(
% 1.85/0.60    ~spl4_8 | spl4_9 | ~spl4_2),
% 1.85/0.60    inference(avatar_split_clause,[],[f254,f128,f260,f256])).
% 1.85/0.60  fof(f128,plain,(
% 1.85/0.60    spl4_2 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)),
% 1.85/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.85/0.60  fof(f254,plain,(
% 1.85/0.60    k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~v1_relat_1(sK3) | ~spl4_2),
% 1.85/0.60    inference(trivial_inequality_removal,[],[f253])).
% 1.85/0.60  fof(f253,plain,(
% 1.85/0.60    k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | k1_relat_1(sK3) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | ~spl4_2),
% 1.85/0.60    inference(resolution,[],[f158,f38])).
% 1.85/0.60  fof(f38,plain,(
% 1.85/0.60    v1_funct_1(sK3)),
% 1.85/0.60    inference(cnf_transformation,[],[f33])).
% 1.85/0.60  fof(f158,plain,(
% 1.85/0.60    ( ! [X10] : (~v1_funct_1(X10) | k2_relat_1(X10) = k2_enumset1(k1_funct_1(X10,sK0),k1_funct_1(X10,sK0),k1_funct_1(X10,sK0),k1_funct_1(X10,sK0)) | k1_relat_1(sK3) != k1_relat_1(X10) | ~v1_relat_1(X10)) ) | ~spl4_2),
% 1.85/0.60    inference(superposition,[],[f75,f130])).
% 1.85/0.60  fof(f130,plain,(
% 1.85/0.60    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | ~spl4_2),
% 1.85/0.60    inference(avatar_component_clause,[],[f128])).
% 1.85/0.60  fof(f75,plain,(
% 1.85/0.60    ( ! [X0,X1] : (k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0) | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.85/0.60    inference(definition_unfolding,[],[f52,f71,f71])).
% 1.85/0.60  fof(f52,plain,(
% 1.85/0.60    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.85/0.60    inference(cnf_transformation,[],[f25])).
% 1.85/0.60  fof(f25,plain,(
% 1.85/0.60    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.85/0.60    inference(flattening,[],[f24])).
% 1.85/0.60  fof(f24,plain,(
% 1.85/0.60    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.85/0.60    inference(ennf_transformation,[],[f12])).
% 1.85/0.60  fof(f12,axiom,(
% 1.85/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.85/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 1.85/0.60  fof(f131,plain,(
% 1.85/0.60    spl4_1 | spl4_2),
% 1.85/0.60    inference(avatar_split_clause,[],[f122,f128,f124])).
% 1.85/0.60  fof(f122,plain,(
% 1.85/0.60    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.85/0.60    inference(duplicate_literal_removal,[],[f119])).
% 1.85/0.60  fof(f119,plain,(
% 1.85/0.60    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)),
% 1.85/0.60    inference(resolution,[],[f118,f73])).
% 1.85/0.60  fof(f118,plain,(
% 1.85/0.60    ( ! [X6,X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(X1,X1,X2,X3),X6))) | k1_relat_1(X0) = k2_enumset1(X3,X3,X3,X3) | k1_relat_1(X0) = k2_enumset1(X2,X2,X2,X2) | k1_relat_1(X0) = k2_enumset1(X1,X1,X1,X1) | k1_xboole_0 = k1_relat_1(X0) | k1_relat_1(X0) = k2_enumset1(X1,X1,X2,X3) | k1_relat_1(X0) = k2_enumset1(X2,X2,X2,X3) | k1_relat_1(X0) = k2_enumset1(X1,X1,X1,X3) | k1_relat_1(X0) = k2_enumset1(X1,X1,X1,X2)) )),
% 1.85/0.60    inference(condensation,[],[f117])).
% 1.85/0.60  fof(f117,plain,(
% 1.85/0.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k1_relat_1(X0) = k2_enumset1(X1,X1,X1,X2) | k1_relat_1(X0) = k2_enumset1(X3,X3,X3,X3) | k1_relat_1(X0) = k2_enumset1(X2,X2,X2,X2) | k1_relat_1(X0) = k2_enumset1(X1,X1,X1,X1) | k1_xboole_0 = k1_relat_1(X0) | k1_relat_1(X0) = k2_enumset1(X1,X1,X2,X3) | k1_relat_1(X0) = k2_enumset1(X2,X2,X2,X3) | k1_relat_1(X0) = k2_enumset1(X1,X1,X1,X3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(X1,X1,X2,X3),X6)))) )),
% 1.85/0.60    inference(resolution,[],[f116,f57])).
% 1.85/0.60  fof(f57,plain,(
% 1.85/0.60    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.85/0.60    inference(cnf_transformation,[],[f27])).
% 1.85/0.60  fof(f27,plain,(
% 1.85/0.60    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.85/0.60    inference(ennf_transformation,[],[f14])).
% 1.85/0.60  fof(f14,axiom,(
% 1.85/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.85/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.85/0.60  fof(f116,plain,(
% 1.85/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (~v4_relat_1(X0,k2_enumset1(X3,X3,X1,X2)) | k1_relat_1(X0) = k2_enumset1(X3,X3,X3,X1) | k1_relat_1(X0) = k2_enumset1(X2,X2,X2,X2) | k1_relat_1(X0) = k2_enumset1(X1,X1,X1,X1) | k1_relat_1(X0) = k2_enumset1(X3,X3,X3,X3) | k1_xboole_0 = k1_relat_1(X0) | k1_relat_1(X0) = k2_enumset1(X3,X3,X1,X2) | k1_relat_1(X0) = k2_enumset1(X1,X1,X1,X2) | k1_relat_1(X0) = k2_enumset1(X3,X3,X3,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 1.85/0.60    inference(resolution,[],[f113,f56])).
% 1.85/0.60  fof(f113,plain,(
% 1.85/0.60    ( ! [X30,X28,X31,X29] : (~v1_relat_1(X30) | k1_relat_1(X30) = k2_enumset1(X31,X31,X31,X29) | k1_relat_1(X30) = k2_enumset1(X28,X28,X28,X31) | k1_relat_1(X30) = k2_enumset1(X29,X29,X29,X29) | k1_relat_1(X30) = k2_enumset1(X31,X31,X31,X31) | k1_relat_1(X30) = k2_enumset1(X28,X28,X28,X28) | k1_xboole_0 = k1_relat_1(X30) | k1_relat_1(X30) = k2_enumset1(X28,X28,X31,X29) | ~v4_relat_1(X30,k2_enumset1(X28,X28,X31,X29)) | k2_enumset1(X28,X28,X28,X29) = k1_relat_1(X30)) )),
% 1.85/0.60    inference(resolution,[],[f84,f50])).
% 1.85/0.60  fof(f50,plain,(
% 1.85/0.60    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.85/0.60    inference(cnf_transformation,[],[f34])).
% 1.85/0.60  fof(f34,plain,(
% 1.85/0.60    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.85/0.60    inference(nnf_transformation,[],[f23])).
% 1.85/0.60  fof(f23,plain,(
% 1.85/0.60    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.85/0.60    inference(ennf_transformation,[],[f8])).
% 1.85/0.60  fof(f8,axiom,(
% 1.85/0.60    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.85/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.85/0.60  fof(f84,plain,(
% 1.85/0.60    ( ! [X2,X0,X3,X1] : (~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | k1_xboole_0 = X3 | k2_enumset1(X0,X0,X1,X2) = X3) )),
% 1.85/0.60    inference(definition_unfolding,[],[f61,f55,f70,f70,f70,f71,f71,f71,f55])).
% 1.85/0.60  fof(f61,plain,(
% 1.85/0.60    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 1.85/0.60    inference(cnf_transformation,[],[f37])).
% 1.85/0.60  fof(f37,plain,(
% 1.85/0.60    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 1.85/0.60    inference(flattening,[],[f36])).
% 1.85/0.60  fof(f36,plain,(
% 1.85/0.60    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 1.85/0.60    inference(nnf_transformation,[],[f31])).
% 1.85/0.60  fof(f31,plain,(
% 1.85/0.60    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 1.85/0.60    inference(ennf_transformation,[],[f4])).
% 1.85/0.60  fof(f4,axiom,(
% 1.85/0.60    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 1.85/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).
% 1.85/0.60  % SZS output end Proof for theBenchmark
% 1.85/0.60  % (5446)------------------------------
% 1.85/0.60  % (5446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.60  % (5446)Termination reason: Refutation
% 1.85/0.60  
% 1.85/0.60  % (5446)Memory used [KB]: 10874
% 1.85/0.60  % (5446)Time elapsed: 0.168 s
% 1.85/0.60  % (5446)------------------------------
% 1.85/0.60  % (5446)------------------------------
% 1.85/0.60  % (5449)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.85/0.60  % (5442)Success in time 0.244 s
%------------------------------------------------------------------------------
