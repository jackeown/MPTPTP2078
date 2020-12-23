%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:28 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 148 expanded)
%              Number of leaves         :   27 (  70 expanded)
%              Depth                    :    6
%              Number of atoms          :  232 ( 348 expanded)
%              Number of equality atoms :   64 ( 103 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f138,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f44,f48,f52,f56,f60,f64,f68,f72,f80,f87,f93,f100,f106,f113,f120,f133])).

fof(f133,plain,
    ( ~ spl2_5
    | spl2_16
    | ~ spl2_18 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | ~ spl2_5
    | spl2_16
    | ~ spl2_18 ),
    inference(subsumption_resolution,[],[f131,f105])).

fof(f105,plain,
    ( sK1 != k3_xboole_0(sK0,sK1)
    | spl2_16 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl2_16
  <=> sK1 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f131,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl2_5
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f123,f51])).

fof(f51,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl2_5
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f123,plain,
    ( k3_xboole_0(sK0,sK1) = k1_relat_1(k6_relat_1(sK1))
    | ~ spl2_5
    | ~ spl2_18 ),
    inference(superposition,[],[f51,f119])).

fof(f119,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl2_18
  <=> k6_relat_1(sK1) = k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f120,plain,
    ( spl2_18
    | ~ spl2_6
    | ~ spl2_13
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f115,f111,f84,f54,f117])).

fof(f54,plain,
    ( spl2_6
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f84,plain,
    ( spl2_13
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f111,plain,
    ( spl2_17
  <=> ! [X1,X0] :
        ( k6_relat_1(X0) = k6_relat_1(k3_xboole_0(X0,X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f115,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_6
    | ~ spl2_13
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f114,f55])).

fof(f55,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f114,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k3_xboole_0(sK1,sK0))
    | ~ spl2_13
    | ~ spl2_17 ),
    inference(resolution,[],[f112,f86])).

fof(f86,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f84])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k6_relat_1(k3_xboole_0(X0,X1)) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f111])).

fof(f113,plain,
    ( spl2_17
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f109,f70,f58,f50,f42,f111])).

fof(f42,plain,
    ( spl2_3
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f58,plain,
    ( spl2_7
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f70,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k5_relat_1(k6_relat_1(X0),X1) = X1
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( k6_relat_1(X0) = k6_relat_1(k3_xboole_0(X0,X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f108,f59])).

fof(f59,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) )
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f107,f51])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(k6_relat_1(X0)),X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) )
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(resolution,[],[f71,f43])).

fof(f43,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | k5_relat_1(k6_relat_1(X0),X1) = X1 )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f70])).

fof(f106,plain,
    ( ~ spl2_16
    | spl2_1
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f101,f98,f32,f103])).

fof(f32,plain,
    ( spl2_1
  <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f98,plain,
    ( spl2_15
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k9_relat_1(k6_relat_1(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f101,plain,
    ( sK1 != k3_xboole_0(sK0,sK1)
    | spl2_1
    | ~ spl2_15 ),
    inference(superposition,[],[f34,f99])).

fof(f99,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k9_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f98])).

fof(f34,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f100,plain,
    ( spl2_15
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f96,f91,f66,f46,f42,f98])).

fof(f46,plain,
    ( spl2_4
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f66,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f91,plain,
    ( spl2_14
  <=> ! [X1,X0] : k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f96,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k9_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f95,f47])).

fof(f47,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f95,plain,
    ( ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k6_relat_1(k3_xboole_0(X0,X1)))
    | ~ spl2_3
    | ~ spl2_9
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f94,f92])).

fof(f92,plain,
    ( ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f91])).

fof(f94,plain,
    ( ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(resolution,[],[f67,f43])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f66])).

fof(f93,plain,
    ( spl2_14
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f89,f62,f58,f42,f91])).

fof(f62,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f89,plain,
    ( ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f88,f59])).

fof(f88,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(resolution,[],[f63,f43])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f62])).

fof(f87,plain,
    ( spl2_13
    | ~ spl2_2
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f81,f78,f37,f84])).

fof(f37,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f78,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f81,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_2
    | ~ spl2_12 ),
    inference(resolution,[],[f79,f39])).

fof(f39,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f78])).

fof(f80,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f29,f78])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f72,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f28,f70])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f68,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f27,f66])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f64,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f26,f62])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f60,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f25,f58])).

fof(f25,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f56,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f24,f54])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f52,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f22,f50])).

fof(f22,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f48,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f23,f46])).

fof(f23,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f44,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f21,f42])).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f40,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f19,f37])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(k6_relat_1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

fof(f35,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f20,f32])).

fof(f20,plain,(
    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:20:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.40  % (19868)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.13/0.40  % (19868)Refutation found. Thanks to Tanya!
% 0.13/0.40  % SZS status Theorem for theBenchmark
% 0.13/0.40  % SZS output start Proof for theBenchmark
% 0.13/0.40  fof(f138,plain,(
% 0.13/0.40    $false),
% 0.13/0.40    inference(avatar_sat_refutation,[],[f35,f40,f44,f48,f52,f56,f60,f64,f68,f72,f80,f87,f93,f100,f106,f113,f120,f133])).
% 0.13/0.40  fof(f133,plain,(
% 0.13/0.40    ~spl2_5 | spl2_16 | ~spl2_18),
% 0.13/0.40    inference(avatar_contradiction_clause,[],[f132])).
% 0.13/0.40  fof(f132,plain,(
% 0.13/0.40    $false | (~spl2_5 | spl2_16 | ~spl2_18)),
% 0.13/0.40    inference(subsumption_resolution,[],[f131,f105])).
% 0.13/0.40  fof(f105,plain,(
% 0.13/0.40    sK1 != k3_xboole_0(sK0,sK1) | spl2_16),
% 0.13/0.40    inference(avatar_component_clause,[],[f103])).
% 0.13/0.40  fof(f103,plain,(
% 0.13/0.40    spl2_16 <=> sK1 = k3_xboole_0(sK0,sK1)),
% 0.13/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.13/0.40  fof(f131,plain,(
% 0.13/0.40    sK1 = k3_xboole_0(sK0,sK1) | (~spl2_5 | ~spl2_18)),
% 0.13/0.40    inference(forward_demodulation,[],[f123,f51])).
% 0.13/0.40  fof(f51,plain,(
% 0.13/0.40    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_5),
% 0.13/0.40    inference(avatar_component_clause,[],[f50])).
% 0.13/0.40  fof(f50,plain,(
% 0.13/0.40    spl2_5 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.13/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.13/0.40  fof(f123,plain,(
% 0.13/0.40    k3_xboole_0(sK0,sK1) = k1_relat_1(k6_relat_1(sK1)) | (~spl2_5 | ~spl2_18)),
% 0.13/0.40    inference(superposition,[],[f51,f119])).
% 0.13/0.40  fof(f119,plain,(
% 0.13/0.40    k6_relat_1(sK1) = k6_relat_1(k3_xboole_0(sK0,sK1)) | ~spl2_18),
% 0.13/0.40    inference(avatar_component_clause,[],[f117])).
% 0.13/0.40  fof(f117,plain,(
% 0.13/0.40    spl2_18 <=> k6_relat_1(sK1) = k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.13/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.13/0.40  fof(f120,plain,(
% 0.13/0.40    spl2_18 | ~spl2_6 | ~spl2_13 | ~spl2_17),
% 0.13/0.40    inference(avatar_split_clause,[],[f115,f111,f84,f54,f117])).
% 0.13/0.40  fof(f54,plain,(
% 0.13/0.40    spl2_6 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.13/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.13/0.40  fof(f84,plain,(
% 0.13/0.40    spl2_13 <=> r1_tarski(sK1,sK0)),
% 0.13/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.13/0.40  fof(f111,plain,(
% 0.13/0.40    spl2_17 <=> ! [X1,X0] : (k6_relat_1(X0) = k6_relat_1(k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1))),
% 0.13/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.13/0.40  fof(f115,plain,(
% 0.13/0.40    k6_relat_1(sK1) = k6_relat_1(k3_xboole_0(sK0,sK1)) | (~spl2_6 | ~spl2_13 | ~spl2_17)),
% 0.13/0.40    inference(forward_demodulation,[],[f114,f55])).
% 0.13/0.40  fof(f55,plain,(
% 0.13/0.40    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_6),
% 0.13/0.40    inference(avatar_component_clause,[],[f54])).
% 0.13/0.40  fof(f114,plain,(
% 0.13/0.40    k6_relat_1(sK1) = k6_relat_1(k3_xboole_0(sK1,sK0)) | (~spl2_13 | ~spl2_17)),
% 0.13/0.40    inference(resolution,[],[f112,f86])).
% 0.13/0.40  fof(f86,plain,(
% 0.13/0.40    r1_tarski(sK1,sK0) | ~spl2_13),
% 0.13/0.40    inference(avatar_component_clause,[],[f84])).
% 0.13/0.40  fof(f112,plain,(
% 0.13/0.40    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k6_relat_1(k3_xboole_0(X0,X1))) ) | ~spl2_17),
% 0.13/0.40    inference(avatar_component_clause,[],[f111])).
% 0.13/0.40  fof(f113,plain,(
% 0.13/0.40    spl2_17 | ~spl2_3 | ~spl2_5 | ~spl2_7 | ~spl2_10),
% 0.13/0.40    inference(avatar_split_clause,[],[f109,f70,f58,f50,f42,f111])).
% 0.13/0.40  fof(f42,plain,(
% 0.13/0.40    spl2_3 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.13/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.13/0.40  fof(f58,plain,(
% 0.13/0.40    spl2_7 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.13/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.13/0.40  fof(f70,plain,(
% 0.13/0.40    spl2_10 <=> ! [X1,X0] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.13/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.13/0.40  fof(f109,plain,(
% 0.13/0.40    ( ! [X0,X1] : (k6_relat_1(X0) = k6_relat_1(k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) ) | (~spl2_3 | ~spl2_5 | ~spl2_7 | ~spl2_10)),
% 0.13/0.40    inference(forward_demodulation,[],[f108,f59])).
% 0.13/0.40  fof(f59,plain,(
% 0.13/0.40    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) ) | ~spl2_7),
% 0.13/0.40    inference(avatar_component_clause,[],[f58])).
% 0.13/0.40  fof(f108,plain,(
% 0.13/0.40    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ) | (~spl2_3 | ~spl2_5 | ~spl2_10)),
% 0.13/0.40    inference(forward_demodulation,[],[f107,f51])).
% 0.13/0.40  fof(f107,plain,(
% 0.13/0.40    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ) | (~spl2_3 | ~spl2_10)),
% 0.13/0.40    inference(resolution,[],[f71,f43])).
% 0.13/0.40  fof(f43,plain,(
% 0.13/0.40    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_3),
% 0.13/0.40    inference(avatar_component_clause,[],[f42])).
% 0.13/0.40  fof(f71,plain,(
% 0.13/0.40    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1) ) | ~spl2_10),
% 0.13/0.40    inference(avatar_component_clause,[],[f70])).
% 0.13/0.40  fof(f106,plain,(
% 0.13/0.40    ~spl2_16 | spl2_1 | ~spl2_15),
% 0.13/0.40    inference(avatar_split_clause,[],[f101,f98,f32,f103])).
% 0.13/0.40  fof(f32,plain,(
% 0.13/0.40    spl2_1 <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.13/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.13/0.40  fof(f98,plain,(
% 0.13/0.40    spl2_15 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k9_relat_1(k6_relat_1(X0),X1)),
% 0.13/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.13/0.40  fof(f101,plain,(
% 0.13/0.40    sK1 != k3_xboole_0(sK0,sK1) | (spl2_1 | ~spl2_15)),
% 0.13/0.40    inference(superposition,[],[f34,f99])).
% 0.13/0.40  fof(f99,plain,(
% 0.13/0.40    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k9_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_15),
% 0.13/0.40    inference(avatar_component_clause,[],[f98])).
% 0.13/0.40  fof(f34,plain,(
% 0.13/0.40    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) | spl2_1),
% 0.13/0.40    inference(avatar_component_clause,[],[f32])).
% 0.13/0.40  fof(f100,plain,(
% 0.13/0.40    spl2_15 | ~spl2_3 | ~spl2_4 | ~spl2_9 | ~spl2_14),
% 0.13/0.40    inference(avatar_split_clause,[],[f96,f91,f66,f46,f42,f98])).
% 0.13/0.40  fof(f46,plain,(
% 0.13/0.40    spl2_4 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.13/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.13/0.40  fof(f66,plain,(
% 0.13/0.40    spl2_9 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.13/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.13/0.40  fof(f91,plain,(
% 0.13/0.40    spl2_14 <=> ! [X1,X0] : k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1)),
% 0.13/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.13/0.40  fof(f96,plain,(
% 0.13/0.40    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k9_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_3 | ~spl2_4 | ~spl2_9 | ~spl2_14)),
% 0.13/0.40    inference(forward_demodulation,[],[f95,f47])).
% 0.13/0.40  fof(f47,plain,(
% 0.13/0.40    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_4),
% 0.13/0.40    inference(avatar_component_clause,[],[f46])).
% 0.13/0.40  fof(f95,plain,(
% 0.13/0.40    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k6_relat_1(k3_xboole_0(X0,X1)))) ) | (~spl2_3 | ~spl2_9 | ~spl2_14)),
% 0.13/0.40    inference(forward_demodulation,[],[f94,f92])).
% 0.13/0.40  fof(f92,plain,(
% 0.13/0.40    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_14),
% 0.13/0.40    inference(avatar_component_clause,[],[f91])).
% 0.13/0.40  fof(f94,plain,(
% 0.13/0.40    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) | (~spl2_3 | ~spl2_9)),
% 0.13/0.40    inference(resolution,[],[f67,f43])).
% 0.13/0.40  fof(f67,plain,(
% 0.13/0.40    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl2_9),
% 0.13/0.40    inference(avatar_component_clause,[],[f66])).
% 0.13/0.40  fof(f93,plain,(
% 0.13/0.40    spl2_14 | ~spl2_3 | ~spl2_7 | ~spl2_8),
% 0.13/0.40    inference(avatar_split_clause,[],[f89,f62,f58,f42,f91])).
% 0.13/0.40  fof(f62,plain,(
% 0.13/0.40    spl2_8 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.13/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.13/0.40  fof(f89,plain,(
% 0.13/0.40    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_3 | ~spl2_7 | ~spl2_8)),
% 0.13/0.40    inference(forward_demodulation,[],[f88,f59])).
% 0.13/0.40  fof(f88,plain,(
% 0.13/0.40    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_3 | ~spl2_8)),
% 0.13/0.40    inference(resolution,[],[f63,f43])).
% 0.13/0.40  fof(f63,plain,(
% 0.13/0.40    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_8),
% 0.13/0.40    inference(avatar_component_clause,[],[f62])).
% 0.13/0.40  fof(f87,plain,(
% 0.13/0.40    spl2_13 | ~spl2_2 | ~spl2_12),
% 0.13/0.40    inference(avatar_split_clause,[],[f81,f78,f37,f84])).
% 0.13/0.40  fof(f37,plain,(
% 0.13/0.40    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.13/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.13/0.40  fof(f78,plain,(
% 0.13/0.40    spl2_12 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.13/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.13/0.40  fof(f81,plain,(
% 0.13/0.40    r1_tarski(sK1,sK0) | (~spl2_2 | ~spl2_12)),
% 0.13/0.40    inference(resolution,[],[f79,f39])).
% 0.13/0.40  fof(f39,plain,(
% 0.13/0.40    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_2),
% 0.13/0.40    inference(avatar_component_clause,[],[f37])).
% 0.13/0.40  fof(f79,plain,(
% 0.13/0.40    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl2_12),
% 0.13/0.40    inference(avatar_component_clause,[],[f78])).
% 0.13/0.40  fof(f80,plain,(
% 0.13/0.40    spl2_12),
% 0.13/0.40    inference(avatar_split_clause,[],[f29,f78])).
% 0.13/0.40  fof(f29,plain,(
% 0.13/0.40    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.13/0.40    inference(cnf_transformation,[],[f18])).
% 0.13/0.40  fof(f18,plain,(
% 0.13/0.40    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.13/0.40    inference(nnf_transformation,[],[f2])).
% 0.13/0.40  fof(f2,axiom,(
% 0.13/0.40    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.13/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.13/0.40  fof(f72,plain,(
% 0.13/0.40    spl2_10),
% 0.13/0.40    inference(avatar_split_clause,[],[f28,f70])).
% 0.13/0.40  fof(f28,plain,(
% 0.13/0.40    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.13/0.40    inference(cnf_transformation,[],[f15])).
% 0.13/0.40  fof(f15,plain,(
% 0.13/0.40    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.13/0.40    inference(flattening,[],[f14])).
% 0.13/0.40  fof(f14,plain,(
% 0.13/0.40    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.13/0.40    inference(ennf_transformation,[],[f6])).
% 0.13/0.40  fof(f6,axiom,(
% 0.13/0.40    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.13/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 0.13/0.40  fof(f68,plain,(
% 0.13/0.40    spl2_9),
% 0.13/0.40    inference(avatar_split_clause,[],[f27,f66])).
% 0.13/0.40  fof(f27,plain,(
% 0.13/0.40    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.13/0.40    inference(cnf_transformation,[],[f13])).
% 0.13/0.40  fof(f13,plain,(
% 0.13/0.40    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.13/0.40    inference(ennf_transformation,[],[f4])).
% 0.13/0.40  fof(f4,axiom,(
% 0.13/0.40    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.13/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.13/0.40  fof(f64,plain,(
% 0.13/0.40    spl2_8),
% 0.13/0.40    inference(avatar_split_clause,[],[f26,f62])).
% 0.13/0.40  fof(f26,plain,(
% 0.13/0.40    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.13/0.40    inference(cnf_transformation,[],[f12])).
% 0.13/0.40  fof(f12,plain,(
% 0.13/0.40    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.13/0.40    inference(ennf_transformation,[],[f7])).
% 0.13/0.40  fof(f7,axiom,(
% 0.13/0.40    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.13/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.13/0.40  fof(f60,plain,(
% 0.13/0.40    spl2_7),
% 0.13/0.40    inference(avatar_split_clause,[],[f25,f58])).
% 0.13/0.40  fof(f25,plain,(
% 0.13/0.40    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.13/0.40    inference(cnf_transformation,[],[f8])).
% 0.13/0.40  fof(f8,axiom,(
% 0.13/0.40    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.13/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.13/0.40  fof(f56,plain,(
% 0.13/0.40    spl2_6),
% 0.13/0.40    inference(avatar_split_clause,[],[f24,f54])).
% 0.13/0.40  fof(f24,plain,(
% 0.13/0.40    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.13/0.40    inference(cnf_transformation,[],[f1])).
% 0.13/0.40  fof(f1,axiom,(
% 0.13/0.40    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.13/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.13/0.40  fof(f52,plain,(
% 0.13/0.40    spl2_5),
% 0.13/0.40    inference(avatar_split_clause,[],[f22,f50])).
% 0.13/0.40  fof(f22,plain,(
% 0.13/0.40    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.13/0.40    inference(cnf_transformation,[],[f5])).
% 0.13/0.40  fof(f5,axiom,(
% 0.13/0.40    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.13/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.13/0.40  fof(f48,plain,(
% 0.13/0.40    spl2_4),
% 0.13/0.40    inference(avatar_split_clause,[],[f23,f46])).
% 0.13/0.40  fof(f23,plain,(
% 0.13/0.40    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.13/0.40    inference(cnf_transformation,[],[f5])).
% 0.13/0.40  fof(f44,plain,(
% 0.13/0.40    spl2_3),
% 0.13/0.40    inference(avatar_split_clause,[],[f21,f42])).
% 0.13/0.40  fof(f21,plain,(
% 0.13/0.40    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.13/0.40    inference(cnf_transformation,[],[f3])).
% 0.13/0.40  fof(f3,axiom,(
% 0.13/0.40    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.13/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.13/0.40  fof(f40,plain,(
% 0.13/0.40    spl2_2),
% 0.13/0.40    inference(avatar_split_clause,[],[f19,f37])).
% 0.13/0.40  fof(f19,plain,(
% 0.13/0.40    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.13/0.40    inference(cnf_transformation,[],[f17])).
% 0.13/0.40  fof(f17,plain,(
% 0.13/0.40    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.13/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f16])).
% 0.13/0.40  fof(f16,plain,(
% 0.13/0.40    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.13/0.40    introduced(choice_axiom,[])).
% 0.13/0.40  fof(f11,plain,(
% 0.13/0.40    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.13/0.40    inference(ennf_transformation,[],[f10])).
% 0.13/0.40  fof(f10,negated_conjecture,(
% 0.13/0.40    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.13/0.40    inference(negated_conjecture,[],[f9])).
% 0.13/0.40  fof(f9,conjecture,(
% 0.13/0.40    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.13/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).
% 0.13/0.40  fof(f35,plain,(
% 0.13/0.40    ~spl2_1),
% 0.13/0.40    inference(avatar_split_clause,[],[f20,f32])).
% 0.13/0.40  fof(f20,plain,(
% 0.13/0.40    sK1 != k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.13/0.40    inference(cnf_transformation,[],[f17])).
% 0.13/0.40  % SZS output end Proof for theBenchmark
% 0.13/0.40  % (19868)------------------------------
% 0.13/0.40  % (19868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.40  % (19868)Termination reason: Refutation
% 0.13/0.40  
% 0.13/0.40  % (19868)Memory used [KB]: 10618
% 0.13/0.40  % (19868)Time elapsed: 0.006 s
% 0.13/0.40  % (19868)------------------------------
% 0.13/0.40  % (19868)------------------------------
% 0.13/0.40  % (19858)Success in time 0.046 s
%------------------------------------------------------------------------------
