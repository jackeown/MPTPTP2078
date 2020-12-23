%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 152 expanded)
%              Number of leaves         :   27 (  72 expanded)
%              Depth                    :    6
%              Number of atoms          :  246 ( 414 expanded)
%              Number of equality atoms :   14 (  24 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f270,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f51,f55,f63,f67,f71,f90,f94,f107,f116,f123,f151,f155,f225,f251,f267])).

fof(f267,plain,
    ( ~ spl2_4
    | spl2_24
    | ~ spl2_29 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | ~ spl2_4
    | spl2_24
    | ~ spl2_29 ),
    inference(subsumption_resolution,[],[f196,f252])).

fof(f252,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0)
    | ~ spl2_4
    | ~ spl2_29 ),
    inference(superposition,[],[f50,f250])).

fof(f250,plain,
    ( ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl2_29
  <=> ! [X3,X2] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f50,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl2_4
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f196,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | spl2_24 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl2_24
  <=> r1_tarski(k3_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f251,plain,
    ( spl2_29
    | ~ spl2_9
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f159,f149,f69,f249])).

fof(f69,plain,
    ( spl2_9
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f149,plain,
    ( spl2_19
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f159,plain,
    ( ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)
    | ~ spl2_9
    | ~ spl2_19 ),
    inference(superposition,[],[f150,f70])).

fof(f70,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f150,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f149])).

fof(f225,plain,
    ( ~ spl2_2
    | ~ spl2_24
    | ~ spl2_13
    | spl2_15
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f156,f153,f104,f92,f194,f39])).

fof(f39,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f92,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f104,plain,
    ( spl2_15
  <=> r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f153,plain,
    ( spl2_20
  <=> ! [X0] : v1_relat_1(k3_xboole_0(sK0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f156,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl2_13
    | spl2_15
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f112,f154])).

fof(f154,plain,
    ( ! [X0] : v1_relat_1(k3_xboole_0(sK0,X0))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f153])).

fof(f112,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_13
    | spl2_15 ),
    inference(resolution,[],[f106,f93])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f92])).

fof(f106,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1))
    | spl2_15 ),
    inference(avatar_component_clause,[],[f104])).

fof(f155,plain,
    ( spl2_20
    | ~ spl2_1
    | ~ spl2_8
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f117,f114,f65,f34,f153])).

fof(f34,plain,
    ( spl2_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f65,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f114,plain,
    ( spl2_16
  <=> ! [X1,X0] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f117,plain,
    ( ! [X0] : v1_relat_1(k3_xboole_0(sK0,X0))
    | ~ spl2_1
    | ~ spl2_8
    | ~ spl2_16 ),
    inference(unit_resulting_resolution,[],[f36,f115,f66])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f115,plain,
    ( ! [X0,X1] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f114])).

fof(f36,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f151,plain,
    ( spl2_19
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f80,f69,f53,f149])).

fof(f53,plain,
    ( spl2_5
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f80,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(superposition,[],[f70,f54])).

fof(f54,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f123,plain,
    ( ~ spl2_1
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_13
    | spl2_14
    | ~ spl2_16 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_13
    | spl2_14
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f108,f117])).

fof(f108,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_13
    | spl2_14 ),
    inference(unit_resulting_resolution,[],[f36,f50,f102,f93])).

fof(f102,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0))
    | spl2_14 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl2_14
  <=> r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f116,plain,
    ( spl2_16
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f73,f61,f49,f114])).

fof(f61,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f73,plain,
    ( ! [X0,X1] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f50,f62])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f107,plain,
    ( ~ spl2_14
    | ~ spl2_15
    | spl2_3
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f96,f88,f44,f104,f100])).

fof(f44,plain,
    ( spl2_3
  <=> r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f88,plain,
    ( spl2_12
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f96,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0))
    | spl2_3
    | ~ spl2_12 ),
    inference(resolution,[],[f89,f46])).

fof(f46,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f89,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f88])).

fof(f94,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f24,f92])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(f90,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f32,f88])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f71,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f28,f69])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f67,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f25,f65])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f63,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f31,f61])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f55,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f27,f53])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f51,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f26,f49])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f47,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f23,f44])).

fof(f23,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).

fof(f42,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f22,f39])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f21,f34])).

fof(f21,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:40:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (20922)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.44  % (20922)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f270,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f37,f42,f47,f51,f55,f63,f67,f71,f90,f94,f107,f116,f123,f151,f155,f225,f251,f267])).
% 0.21/0.44  fof(f267,plain,(
% 0.21/0.44    ~spl2_4 | spl2_24 | ~spl2_29),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f266])).
% 0.21/0.44  fof(f266,plain,(
% 0.21/0.44    $false | (~spl2_4 | spl2_24 | ~spl2_29)),
% 0.21/0.44    inference(subsumption_resolution,[],[f196,f252])).
% 0.21/0.44  fof(f252,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) ) | (~spl2_4 | ~spl2_29)),
% 0.21/0.44    inference(superposition,[],[f50,f250])).
% 0.21/0.44  fof(f250,plain,(
% 0.21/0.44    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) ) | ~spl2_29),
% 0.21/0.44    inference(avatar_component_clause,[],[f249])).
% 0.21/0.44  fof(f249,plain,(
% 0.21/0.44    spl2_29 <=> ! [X3,X2] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl2_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f49])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    spl2_4 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.44  fof(f196,plain,(
% 0.21/0.44    ~r1_tarski(k3_xboole_0(sK0,sK1),sK1) | spl2_24),
% 0.21/0.44    inference(avatar_component_clause,[],[f194])).
% 0.21/0.44  fof(f194,plain,(
% 0.21/0.44    spl2_24 <=> r1_tarski(k3_xboole_0(sK0,sK1),sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.21/0.44  fof(f251,plain,(
% 0.21/0.44    spl2_29 | ~spl2_9 | ~spl2_19),
% 0.21/0.44    inference(avatar_split_clause,[],[f159,f149,f69,f249])).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    spl2_9 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.44  fof(f149,plain,(
% 0.21/0.44    spl2_19 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.44  fof(f159,plain,(
% 0.21/0.44    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) ) | (~spl2_9 | ~spl2_19)),
% 0.21/0.44    inference(superposition,[],[f150,f70])).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) ) | ~spl2_9),
% 0.21/0.44    inference(avatar_component_clause,[],[f69])).
% 0.21/0.44  fof(f150,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) ) | ~spl2_19),
% 0.21/0.44    inference(avatar_component_clause,[],[f149])).
% 0.21/0.44  fof(f225,plain,(
% 0.21/0.44    ~spl2_2 | ~spl2_24 | ~spl2_13 | spl2_15 | ~spl2_20),
% 0.21/0.44    inference(avatar_split_clause,[],[f156,f153,f104,f92,f194,f39])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    spl2_2 <=> v1_relat_1(sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.44  fof(f92,plain,(
% 0.21/0.44    spl2_13 <=> ! [X1,X0] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.44  fof(f104,plain,(
% 0.21/0.44    spl2_15 <=> r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.44  fof(f153,plain,(
% 0.21/0.44    spl2_20 <=> ! [X0] : v1_relat_1(k3_xboole_0(sK0,X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.44  fof(f156,plain,(
% 0.21/0.44    ~r1_tarski(k3_xboole_0(sK0,sK1),sK1) | ~v1_relat_1(sK1) | (~spl2_13 | spl2_15 | ~spl2_20)),
% 0.21/0.44    inference(subsumption_resolution,[],[f112,f154])).
% 0.21/0.44  fof(f154,plain,(
% 0.21/0.44    ( ! [X0] : (v1_relat_1(k3_xboole_0(sK0,X0))) ) | ~spl2_20),
% 0.21/0.44    inference(avatar_component_clause,[],[f153])).
% 0.21/0.44  fof(f112,plain,(
% 0.21/0.44    ~r1_tarski(k3_xboole_0(sK0,sK1),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | (~spl2_13 | spl2_15)),
% 0.21/0.44    inference(resolution,[],[f106,f93])).
% 0.21/0.44  fof(f93,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_13),
% 0.21/0.44    inference(avatar_component_clause,[],[f92])).
% 0.21/0.44  fof(f106,plain,(
% 0.21/0.44    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1)) | spl2_15),
% 0.21/0.44    inference(avatar_component_clause,[],[f104])).
% 0.21/0.44  fof(f155,plain,(
% 0.21/0.44    spl2_20 | ~spl2_1 | ~spl2_8 | ~spl2_16),
% 0.21/0.44    inference(avatar_split_clause,[],[f117,f114,f65,f34,f153])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    spl2_1 <=> v1_relat_1(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    spl2_8 <=> ! [X1,X0] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.44  fof(f114,plain,(
% 0.21/0.44    spl2_16 <=> ! [X1,X0] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.44  fof(f117,plain,(
% 0.21/0.44    ( ! [X0] : (v1_relat_1(k3_xboole_0(sK0,X0))) ) | (~spl2_1 | ~spl2_8 | ~spl2_16)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f36,f115,f66])).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_8),
% 0.21/0.44    inference(avatar_component_clause,[],[f65])).
% 0.21/0.44  fof(f115,plain,(
% 0.21/0.44    ( ! [X0,X1] : (m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | ~spl2_16),
% 0.21/0.44    inference(avatar_component_clause,[],[f114])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    v1_relat_1(sK0) | ~spl2_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f34])).
% 0.21/0.44  fof(f151,plain,(
% 0.21/0.44    spl2_19 | ~spl2_5 | ~spl2_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f80,f69,f53,f149])).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    spl2_5 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.44  fof(f80,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) ) | (~spl2_5 | ~spl2_9)),
% 0.21/0.44    inference(superposition,[],[f70,f54])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl2_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f53])).
% 0.21/0.44  fof(f123,plain,(
% 0.21/0.44    ~spl2_1 | ~spl2_4 | ~spl2_8 | ~spl2_13 | spl2_14 | ~spl2_16),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f122])).
% 0.21/0.44  fof(f122,plain,(
% 0.21/0.44    $false | (~spl2_1 | ~spl2_4 | ~spl2_8 | ~spl2_13 | spl2_14 | ~spl2_16)),
% 0.21/0.44    inference(subsumption_resolution,[],[f108,f117])).
% 0.21/0.44  fof(f108,plain,(
% 0.21/0.44    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | (~spl2_1 | ~spl2_4 | ~spl2_13 | spl2_14)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f36,f50,f102,f93])).
% 0.21/0.44  fof(f102,plain,(
% 0.21/0.44    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0)) | spl2_14),
% 0.21/0.44    inference(avatar_component_clause,[],[f100])).
% 0.21/0.44  fof(f100,plain,(
% 0.21/0.44    spl2_14 <=> r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.44  fof(f116,plain,(
% 0.21/0.44    spl2_16 | ~spl2_4 | ~spl2_7),
% 0.21/0.44    inference(avatar_split_clause,[],[f73,f61,f49,f114])).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    spl2_7 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    ( ! [X0,X1] : (m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | (~spl2_4 | ~spl2_7)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f50,f62])).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl2_7),
% 0.21/0.44    inference(avatar_component_clause,[],[f61])).
% 0.21/0.44  fof(f107,plain,(
% 0.21/0.44    ~spl2_14 | ~spl2_15 | spl2_3 | ~spl2_12),
% 0.21/0.44    inference(avatar_split_clause,[],[f96,f88,f44,f104,f100])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    spl2_3 <=> r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.44  fof(f88,plain,(
% 0.21/0.44    spl2_12 <=> ! [X1,X0,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.44  fof(f96,plain,(
% 0.21/0.44    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1)) | ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0)) | (spl2_3 | ~spl2_12)),
% 0.21/0.44    inference(resolution,[],[f89,f46])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) | spl2_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f44])).
% 0.21/0.44  fof(f89,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl2_12),
% 0.21/0.44    inference(avatar_component_clause,[],[f88])).
% 0.21/0.44  fof(f94,plain,(
% 0.21/0.44    spl2_13),
% 0.21/0.44    inference(avatar_split_clause,[],[f24,f92])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(flattening,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : ((r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).
% 0.21/0.44  fof(f90,plain,(
% 0.21/0.44    spl2_12),
% 0.21/0.44    inference(avatar_split_clause,[],[f32,f88])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(flattening,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    spl2_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f28,f69])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.44  fof(f67,plain,(
% 0.21/0.44    spl2_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f25,f65])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    spl2_7),
% 0.21/0.44    inference(avatar_split_clause,[],[f31,f61])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.44    inference(nnf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    spl2_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f27,f53])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    spl2_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f26,f49])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    ~spl2_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f23,f44])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f18,f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,negated_conjecture,(
% 0.21/0.44    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.21/0.44    inference(negated_conjecture,[],[f9])).
% 0.21/0.44  fof(f9,conjecture,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    spl2_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f22,f39])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    v1_relat_1(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    spl2_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f21,f34])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    v1_relat_1(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (20922)------------------------------
% 0.21/0.44  % (20922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (20922)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (20922)Memory used [KB]: 6268
% 0.21/0.44  % (20922)Time elapsed: 0.010 s
% 0.21/0.44  % (20922)------------------------------
% 0.21/0.44  % (20922)------------------------------
% 0.21/0.44  % (20913)Success in time 0.088 s
%------------------------------------------------------------------------------
