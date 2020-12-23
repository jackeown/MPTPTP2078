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
% DateTime   : Thu Dec  3 12:51:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 121 expanded)
%              Number of leaves         :   22 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :  219 ( 332 expanded)
%              Number of equality atoms :   31 (  55 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f193,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f48,f52,f56,f60,f70,f76,f82,f86,f117,f129,f166,f192])).

fof(f192,plain,
    ( ~ spl3_1
    | spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_15
    | ~ spl3_19 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | ~ spl3_1
    | spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_15
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f169,f188])).

fof(f188,plain,
    ( ! [X0] : r1_xboole_0(k4_xboole_0(X0,sK1),sK0)
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f128,f59])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f128,plain,
    ( ! [X0] : r1_xboole_0(sK0,k4_xboole_0(X0,sK1))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl3_15
  <=> ! [X0] : r1_xboole_0(sK0,k4_xboole_0(X0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f169,plain,
    ( ~ r1_xboole_0(k4_xboole_0(k1_zfmisc_1(k3_tarski(k1_relat_1(sK2))),sK1),sK0)
    | ~ spl3_1
    | spl3_3
    | ~ spl3_4
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f37,f51,f47,f165])).

fof(f165,plain,
    ( ! [X2,X0,X3,X1] :
        ( k1_xboole_0 = k7_relat_1(k4_xboole_0(X0,k7_relat_1(X0,X2)),X3)
        | ~ r1_xboole_0(k4_xboole_0(X1,X2),X3)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k1_relat_1(X0),X1) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl3_19
  <=> ! [X1,X3,X0,X2] :
        ( k1_xboole_0 = k7_relat_1(k4_xboole_0(X0,k7_relat_1(X0,X2)),X3)
        | ~ r1_xboole_0(k4_xboole_0(X1,X2),X3)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k1_relat_1(X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f47,plain,
    ( k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_3
  <=> k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f51,plain,
    ( ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_4
  <=> ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f37,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f166,plain,
    ( spl3_19
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f96,f80,f74,f164])).

fof(f74,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f80,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(X2,k7_relat_1(X2,X1))
        | ~ r1_tarski(k1_relat_1(X2),X0)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f96,plain,
    ( ! [X2,X0,X3,X1] :
        ( k1_xboole_0 = k7_relat_1(k4_xboole_0(X0,k7_relat_1(X0,X2)),X3)
        | ~ r1_xboole_0(k4_xboole_0(X1,X2),X3)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k1_relat_1(X0),X1) )
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,
    ( ! [X2,X0,X3,X1] :
        ( k1_xboole_0 = k7_relat_1(k4_xboole_0(X0,k7_relat_1(X0,X2)),X3)
        | ~ r1_xboole_0(k4_xboole_0(X1,X2),X3)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k1_relat_1(X0),X1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(superposition,[],[f75,f81])).

fof(f81,plain,
    ( ! [X2,X0,X1] :
        ( k7_relat_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(X2,k7_relat_1(X2,X1))
        | ~ r1_tarski(k1_relat_1(X2),X0)
        | ~ v1_relat_1(X2) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f80])).

fof(f75,plain,
    ( ! [X2,X0,X1] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1)
        | ~ v1_relat_1(X2) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f74])).

fof(f129,plain,
    ( spl3_15
    | ~ spl3_11
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f122,f115,f84,f127])).

fof(f84,plain,
    ( spl3_11
  <=> ! [X0] :
        ( ~ r1_xboole_0(sK1,X0)
        | r1_xboole_0(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f115,plain,
    ( spl3_14
  <=> ! [X1,X0] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f122,plain,
    ( ! [X0] : r1_xboole_0(sK0,k4_xboole_0(X0,sK1))
    | ~ spl3_11
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f116,f85])).

fof(f85,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK1,X0)
        | r1_xboole_0(sK0,X0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f84])).

fof(f116,plain,
    ( ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f115])).

fof(f117,plain,
    ( spl3_14
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f65,f58,f54,f115])).

fof(f54,plain,
    ( spl3_5
  <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f65,plain,
    ( ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f55,f59])).

fof(f55,plain,
    ( ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f86,plain,
    ( spl3_11
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f71,f68,f40,f84])).

fof(f40,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f68,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f71,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK1,X0)
        | r1_xboole_0(sK0,X0) )
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(resolution,[],[f69,f42])).

fof(f42,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f69,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X2) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f68])).

fof(f82,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f33,f80])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(X2,k7_relat_1(X2,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f32,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k4_xboole_0(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f29,f26])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X0)
       => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

fof(f76,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f28,f74])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

fof(f70,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f30,f68])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f60,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f27,f58])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f56,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f25,f54])).

fof(f25,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f52,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f24,f50])).

fof(f24,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f48,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f31,f45])).

fof(f31,plain,(
    k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(forward_demodulation,[],[f23,f26])).

fof(f23,plain,(
    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).

fof(f43,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f22,f40])).

fof(f22,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f38,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f21,f35])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:26:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (14111)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (14119)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.46  % (14111)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f193,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f38,f43,f48,f52,f56,f60,f70,f76,f82,f86,f117,f129,f166,f192])).
% 0.21/0.47  fof(f192,plain,(
% 0.21/0.47    ~spl3_1 | spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_15 | ~spl3_19),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f190])).
% 0.21/0.47  fof(f190,plain,(
% 0.21/0.47    $false | (~spl3_1 | spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_15 | ~spl3_19)),
% 0.21/0.47    inference(subsumption_resolution,[],[f169,f188])).
% 0.21/0.47  fof(f188,plain,(
% 0.21/0.47    ( ! [X0] : (r1_xboole_0(k4_xboole_0(X0,sK1),sK0)) ) | (~spl3_6 | ~spl3_15)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f128,f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl3_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f58])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    spl3_6 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    ( ! [X0] : (r1_xboole_0(sK0,k4_xboole_0(X0,sK1))) ) | ~spl3_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f127])).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    spl3_15 <=> ! [X0] : r1_xboole_0(sK0,k4_xboole_0(X0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.47  fof(f169,plain,(
% 0.21/0.47    ~r1_xboole_0(k4_xboole_0(k1_zfmisc_1(k3_tarski(k1_relat_1(sK2))),sK1),sK0) | (~spl3_1 | spl3_3 | ~spl3_4 | ~spl3_19)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f37,f51,f47,f165])).
% 0.21/0.47  fof(f165,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k7_relat_1(k4_xboole_0(X0,k7_relat_1(X0,X2)),X3) | ~r1_xboole_0(k4_xboole_0(X1,X2),X3) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),X1)) ) | ~spl3_19),
% 0.21/0.47    inference(avatar_component_clause,[],[f164])).
% 0.21/0.47  fof(f164,plain,(
% 0.21/0.47    spl3_19 <=> ! [X1,X3,X0,X2] : (k1_xboole_0 = k7_relat_1(k4_xboole_0(X0,k7_relat_1(X0,X2)),X3) | ~r1_xboole_0(k4_xboole_0(X1,X2),X3) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0) | spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    spl3_3 <=> k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) ) | ~spl3_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    spl3_4 <=> ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    v1_relat_1(sK2) | ~spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    spl3_1 <=> v1_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f166,plain,(
% 0.21/0.47    spl3_19 | ~spl3_9 | ~spl3_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f96,f80,f74,f164])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    spl3_9 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    spl3_10 <=> ! [X1,X0,X2] : (k7_relat_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(X2,k7_relat_1(X2,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k7_relat_1(k4_xboole_0(X0,k7_relat_1(X0,X2)),X3) | ~r1_xboole_0(k4_xboole_0(X1,X2),X3) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),X1)) ) | (~spl3_9 | ~spl3_10)),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f93])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k7_relat_1(k4_xboole_0(X0,k7_relat_1(X0,X2)),X3) | ~r1_xboole_0(k4_xboole_0(X1,X2),X3) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0)) ) | (~spl3_9 | ~spl3_10)),
% 0.21/0.47    inference(superposition,[],[f75,f81])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k7_relat_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(X2,k7_relat_1(X2,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) ) | ~spl3_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f80])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) ) | ~spl3_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f74])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    spl3_15 | ~spl3_11 | ~spl3_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f122,f115,f84,f127])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    spl3_11 <=> ! [X0] : (~r1_xboole_0(sK1,X0) | r1_xboole_0(sK0,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    spl3_14 <=> ! [X1,X0] : r1_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    ( ! [X0] : (r1_xboole_0(sK0,k4_xboole_0(X0,sK1))) ) | (~spl3_11 | ~spl3_14)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f116,f85])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_xboole_0(sK1,X0) | r1_xboole_0(sK0,X0)) ) | ~spl3_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f84])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl3_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f115])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    spl3_14 | ~spl3_5 | ~spl3_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f65,f58,f54,f115])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    spl3_5 <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) ) | (~spl3_5 | ~spl3_6)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f55,f59])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) ) | ~spl3_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f54])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    spl3_11 | ~spl3_2 | ~spl3_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f71,f68,f40,f84])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    spl3_8 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_xboole_0(sK1,X0) | r1_xboole_0(sK0,X0)) ) | (~spl3_2 | ~spl3_8)),
% 0.21/0.47    inference(resolution,[],[f69,f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f40])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) ) | ~spl3_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f68])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    spl3_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f33,f80])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k7_relat_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(X2,k7_relat_1(X2,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f32,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k4_xboole_0(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f29,f26])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0)) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(k1_relat_1(X2),X0) => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    spl3_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f28,f74])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    spl3_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f30,f68])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    spl3_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f27,f58])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    spl3_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f25,f54])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f24,f50])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ~spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f31,f45])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 0.21/0.47    inference(forward_demodulation,[],[f23,f26])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 0.21/0.47    inference(negated_conjecture,[],[f8])).
% 0.21/0.47  fof(f8,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f22,f40])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    r1_tarski(sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f21,f35])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    v1_relat_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (14111)------------------------------
% 0.21/0.47  % (14111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (14111)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (14111)Memory used [KB]: 6268
% 0.21/0.47  % (14111)Time elapsed: 0.064 s
% 0.21/0.47  % (14111)------------------------------
% 0.21/0.47  % (14111)------------------------------
% 0.21/0.47  % (14099)Success in time 0.109 s
%------------------------------------------------------------------------------
