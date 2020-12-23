%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 130 expanded)
%              Number of leaves         :   26 (  57 expanded)
%              Depth                    :    8
%              Number of atoms          :  241 ( 354 expanded)
%              Number of equality atoms :   16 (  21 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f306,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f52,f56,f60,f68,f74,f80,f91,f97,f111,f115,f252,f300,f305])).

fof(f305,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_18
    | spl2_19 ),
    inference(avatar_contradiction_clause,[],[f304])).

fof(f304,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_18
    | spl2_19 ),
    inference(subsumption_resolution,[],[f269,f303])).

fof(f303,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK0,sK1)))
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_14
    | spl2_19 ),
    inference(forward_demodulation,[],[f302,f67])).

fof(f67,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl2_7
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f302,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,sK0)))
    | ~ spl2_2
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_14
    | spl2_19 ),
    inference(forward_demodulation,[],[f301,f79])).

fof(f79,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl2_9
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f301,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))))
    | ~ spl2_2
    | ~ spl2_11
    | ~ spl2_14
    | spl2_19 ),
    inference(forward_demodulation,[],[f299,f139])).

fof(f139,plain,
    ( ! [X0] : k2_relat_1(k2_xboole_0(sK1,k4_xboole_0(sK0,X0))) = k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k4_xboole_0(sK0,X0)))
    | ~ spl2_2
    | ~ spl2_11
    | ~ spl2_14 ),
    inference(unit_resulting_resolution,[],[f46,f96,f114])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl2_14
  <=> ! [X1,X0] :
        ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f96,plain,
    ( ! [X0] : v1_relat_1(k4_xboole_0(sK0,X0))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl2_11
  <=> ! [X0] : v1_relat_1(k4_xboole_0(sK0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f46,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f299,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k4_xboole_0(sK0,sK1))))
    | spl2_19 ),
    inference(avatar_component_clause,[],[f297])).

fof(f297,plain,
    ( spl2_19
  <=> r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k4_xboole_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f269,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK0,sK1)))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_13
    | ~ spl2_18 ),
    inference(unit_resulting_resolution,[],[f41,f55,f251,f110])).

fof(f110,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f251,plain,
    ( v1_relat_1(k2_xboole_0(sK0,sK1))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl2_18
  <=> v1_relat_1(k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f55,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl2_4
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f41,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl2_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f300,plain,
    ( ~ spl2_19
    | spl2_3
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f98,f89,f49,f297])).

fof(f49,plain,
    ( spl2_3
  <=> r1_tarski(k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f89,plain,
    ( spl2_10
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k4_xboole_0(X0,X1),X2)
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f98,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k4_xboole_0(sK0,sK1))))
    | spl2_3
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f51,f90])).

fof(f90,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | r1_tarski(k4_xboole_0(X0,X1),X2) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f89])).

fof(f51,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k4_xboole_0(sK0,sK1)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f252,plain,
    ( spl2_18
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f83,f72,f44,f39,f249])).

fof(f72,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( v1_relat_1(k2_xboole_0(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f83,plain,
    ( v1_relat_1(k2_xboole_0(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f41,f46,f73])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k2_xboole_0(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f72])).

fof(f115,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f26,f113])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_relat_1)).

fof(f111,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f28,f109])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
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
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f97,plain,
    ( spl2_11
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f69,f58,f39,f95])).

fof(f58,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( v1_relat_1(k4_xboole_0(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f69,plain,
    ( ! [X0] : v1_relat_1(k4_xboole_0(sK0,X0))
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f41,f59])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k4_xboole_0(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f91,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f35,f89])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f80,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f32,f78])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f74,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f34,f72])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_relat_1)).

fof(f68,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f31,f66])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f60,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f33,f58])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

fof(f56,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f29,f54])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f52,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f37,f49])).

fof(f37,plain,(
    ~ r1_tarski(k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f36,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f36,plain,(
    ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f25,f30])).

fof(f25,plain,(
    ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(sK0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(sK0,X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).

fof(f47,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f24,f44])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f23,f39])).

fof(f23,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:47:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.36  ipcrm: permission denied for id (810614784)
% 0.12/0.36  ipcrm: permission denied for id (813727747)
% 0.12/0.36  ipcrm: permission denied for id (810680324)
% 0.12/0.37  ipcrm: permission denied for id (813760517)
% 0.12/0.37  ipcrm: permission denied for id (810713096)
% 0.12/0.37  ipcrm: permission denied for id (813858825)
% 0.12/0.37  ipcrm: permission denied for id (813891594)
% 0.12/0.37  ipcrm: permission denied for id (813924363)
% 0.12/0.37  ipcrm: permission denied for id (813957132)
% 0.12/0.37  ipcrm: permission denied for id (810844173)
% 0.12/0.38  ipcrm: permission denied for id (810876942)
% 0.12/0.38  ipcrm: permission denied for id (810909711)
% 0.12/0.38  ipcrm: permission denied for id (813989904)
% 0.12/0.38  ipcrm: permission denied for id (816513041)
% 0.12/0.38  ipcrm: permission denied for id (816545810)
% 0.12/0.38  ipcrm: permission denied for id (814088211)
% 0.12/0.38  ipcrm: permission denied for id (814153749)
% 0.12/0.38  ipcrm: permission denied for id (814186518)
% 0.12/0.39  ipcrm: permission denied for id (811073559)
% 0.12/0.39  ipcrm: permission denied for id (816611352)
% 0.12/0.39  ipcrm: permission denied for id (811139097)
% 0.12/0.39  ipcrm: permission denied for id (814252058)
% 0.12/0.39  ipcrm: permission denied for id (814284827)
% 0.12/0.39  ipcrm: permission denied for id (816644124)
% 0.12/0.39  ipcrm: permission denied for id (814350365)
% 0.12/0.39  ipcrm: permission denied for id (811204638)
% 0.12/0.39  ipcrm: permission denied for id (811237407)
% 0.12/0.39  ipcrm: permission denied for id (811270176)
% 0.12/0.40  ipcrm: permission denied for id (814383137)
% 0.12/0.40  ipcrm: permission denied for id (816676898)
% 0.12/0.40  ipcrm: permission denied for id (811335715)
% 0.12/0.40  ipcrm: permission denied for id (811368484)
% 0.12/0.40  ipcrm: permission denied for id (811401253)
% 0.12/0.40  ipcrm: permission denied for id (811434022)
% 0.12/0.40  ipcrm: permission denied for id (816742440)
% 0.12/0.40  ipcrm: permission denied for id (816775209)
% 0.12/0.41  ipcrm: permission denied for id (814612522)
% 0.20/0.41  ipcrm: permission denied for id (814645291)
% 0.20/0.41  ipcrm: permission denied for id (814678060)
% 0.20/0.41  ipcrm: permission denied for id (811565101)
% 0.20/0.41  ipcrm: permission denied for id (814710830)
% 0.20/0.41  ipcrm: permission denied for id (816807983)
% 0.20/0.41  ipcrm: permission denied for id (811630640)
% 0.20/0.41  ipcrm: permission denied for id (814809138)
% 0.20/0.42  ipcrm: permission denied for id (811696179)
% 0.20/0.42  ipcrm: permission denied for id (811761717)
% 0.20/0.42  ipcrm: permission denied for id (814874678)
% 0.20/0.42  ipcrm: permission denied for id (811827255)
% 0.20/0.42  ipcrm: permission denied for id (814907448)
% 0.20/0.42  ipcrm: permission denied for id (811892793)
% 0.20/0.42  ipcrm: permission denied for id (814940218)
% 0.20/0.42  ipcrm: permission denied for id (811925563)
% 0.20/0.43  ipcrm: permission denied for id (816939069)
% 0.20/0.43  ipcrm: permission denied for id (817037376)
% 0.20/0.43  ipcrm: permission denied for id (815136833)
% 0.20/0.43  ipcrm: permission denied for id (815169602)
% 0.20/0.43  ipcrm: permission denied for id (817070147)
% 0.20/0.43  ipcrm: permission denied for id (812122180)
% 0.20/0.44  ipcrm: permission denied for id (812154950)
% 0.20/0.44  ipcrm: permission denied for id (812187719)
% 0.20/0.44  ipcrm: permission denied for id (812220488)
% 0.20/0.44  ipcrm: permission denied for id (812253257)
% 0.20/0.44  ipcrm: permission denied for id (812318795)
% 0.20/0.44  ipcrm: permission denied for id (815300684)
% 0.20/0.44  ipcrm: permission denied for id (817168461)
% 0.20/0.45  ipcrm: permission denied for id (815366222)
% 0.20/0.45  ipcrm: permission denied for id (815431760)
% 0.20/0.45  ipcrm: permission denied for id (812384338)
% 0.20/0.45  ipcrm: permission denied for id (812417107)
% 0.20/0.45  ipcrm: permission denied for id (815497300)
% 0.20/0.45  ipcrm: permission denied for id (815530069)
% 0.20/0.45  ipcrm: permission denied for id (815562838)
% 0.20/0.46  ipcrm: permission denied for id (812548183)
% 0.20/0.46  ipcrm: permission denied for id (815595608)
% 0.20/0.46  ipcrm: permission denied for id (817266777)
% 0.20/0.46  ipcrm: permission denied for id (812613722)
% 0.20/0.46  ipcrm: permission denied for id (817332316)
% 0.20/0.46  ipcrm: permission denied for id (812744797)
% 0.20/0.46  ipcrm: permission denied for id (815726686)
% 0.20/0.46  ipcrm: permission denied for id (817365087)
% 0.20/0.46  ipcrm: permission denied for id (812810336)
% 0.20/0.47  ipcrm: permission denied for id (812843105)
% 0.20/0.47  ipcrm: permission denied for id (812875874)
% 0.20/0.47  ipcrm: permission denied for id (812908643)
% 0.20/0.47  ipcrm: permission denied for id (812941412)
% 0.20/0.47  ipcrm: permission denied for id (812974181)
% 0.20/0.47  ipcrm: permission denied for id (813006950)
% 0.20/0.47  ipcrm: permission denied for id (817397863)
% 0.20/0.47  ipcrm: permission denied for id (815825000)
% 0.20/0.47  ipcrm: permission denied for id (813105257)
% 0.20/0.48  ipcrm: permission denied for id (817430634)
% 0.20/0.48  ipcrm: permission denied for id (813138027)
% 0.20/0.48  ipcrm: permission denied for id (815890540)
% 0.20/0.48  ipcrm: permission denied for id (813203565)
% 0.20/0.48  ipcrm: permission denied for id (817463406)
% 0.20/0.48  ipcrm: permission denied for id (813269104)
% 0.20/0.48  ipcrm: permission denied for id (816021618)
% 0.20/0.49  ipcrm: permission denied for id (813334643)
% 0.20/0.49  ipcrm: permission denied for id (816054388)
% 0.20/0.49  ipcrm: permission denied for id (816087157)
% 0.20/0.49  ipcrm: permission denied for id (813400182)
% 0.20/0.49  ipcrm: permission denied for id (816119927)
% 0.20/0.49  ipcrm: permission denied for id (816152696)
% 0.20/0.49  ipcrm: permission denied for id (816185465)
% 0.20/0.49  ipcrm: permission denied for id (816218234)
% 0.20/0.49  ipcrm: permission denied for id (817561723)
% 0.20/0.50  ipcrm: permission denied for id (816283772)
% 0.20/0.50  ipcrm: permission denied for id (816349310)
% 0.20/0.50  ipcrm: permission denied for id (813629567)
% 0.20/0.56  % (30304)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.57  % (30304)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f306,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(avatar_sat_refutation,[],[f42,f47,f52,f56,f60,f68,f74,f80,f91,f97,f111,f115,f252,f300,f305])).
% 0.20/0.57  fof(f305,plain,(
% 0.20/0.57    ~spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_7 | ~spl2_9 | ~spl2_11 | ~spl2_13 | ~spl2_14 | ~spl2_18 | spl2_19),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f304])).
% 0.20/0.57  fof(f304,plain,(
% 0.20/0.57    $false | (~spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_7 | ~spl2_9 | ~spl2_11 | ~spl2_13 | ~spl2_14 | ~spl2_18 | spl2_19)),
% 0.20/0.57    inference(subsumption_resolution,[],[f269,f303])).
% 0.20/0.57  fof(f303,plain,(
% 0.20/0.57    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK0,sK1))) | (~spl2_2 | ~spl2_7 | ~spl2_9 | ~spl2_11 | ~spl2_14 | spl2_19)),
% 0.20/0.57    inference(forward_demodulation,[],[f302,f67])).
% 0.20/0.57  fof(f67,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl2_7),
% 0.20/0.57    inference(avatar_component_clause,[],[f66])).
% 0.20/0.57  fof(f66,plain,(
% 0.20/0.57    spl2_7 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.57  fof(f302,plain,(
% 0.20/0.57    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,sK0))) | (~spl2_2 | ~spl2_9 | ~spl2_11 | ~spl2_14 | spl2_19)),
% 0.20/0.57    inference(forward_demodulation,[],[f301,f79])).
% 0.20/0.57  fof(f79,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl2_9),
% 0.20/0.57    inference(avatar_component_clause,[],[f78])).
% 0.20/0.57  fof(f78,plain,(
% 0.20/0.57    spl2_9 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.57  fof(f301,plain,(
% 0.20/0.57    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) | (~spl2_2 | ~spl2_11 | ~spl2_14 | spl2_19)),
% 0.20/0.57    inference(forward_demodulation,[],[f299,f139])).
% 0.20/0.57  fof(f139,plain,(
% 0.20/0.57    ( ! [X0] : (k2_relat_1(k2_xboole_0(sK1,k4_xboole_0(sK0,X0))) = k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k4_xboole_0(sK0,X0)))) ) | (~spl2_2 | ~spl2_11 | ~spl2_14)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f46,f96,f114])).
% 0.20/0.57  fof(f114,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_14),
% 0.20/0.57    inference(avatar_component_clause,[],[f113])).
% 0.20/0.57  fof(f113,plain,(
% 0.20/0.57    spl2_14 <=> ! [X1,X0] : (k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.57  fof(f96,plain,(
% 0.20/0.57    ( ! [X0] : (v1_relat_1(k4_xboole_0(sK0,X0))) ) | ~spl2_11),
% 0.20/0.57    inference(avatar_component_clause,[],[f95])).
% 0.20/0.57  fof(f95,plain,(
% 0.20/0.57    spl2_11 <=> ! [X0] : v1_relat_1(k4_xboole_0(sK0,X0))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.57  fof(f46,plain,(
% 0.20/0.57    v1_relat_1(sK1) | ~spl2_2),
% 0.20/0.57    inference(avatar_component_clause,[],[f44])).
% 0.20/0.57  fof(f44,plain,(
% 0.20/0.57    spl2_2 <=> v1_relat_1(sK1)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.57  fof(f299,plain,(
% 0.20/0.57    ~r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k4_xboole_0(sK0,sK1)))) | spl2_19),
% 0.20/0.57    inference(avatar_component_clause,[],[f297])).
% 0.20/0.57  fof(f297,plain,(
% 0.20/0.57    spl2_19 <=> r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k4_xboole_0(sK0,sK1))))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.20/0.57  fof(f269,plain,(
% 0.20/0.57    r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK0,sK1))) | (~spl2_1 | ~spl2_4 | ~spl2_13 | ~spl2_18)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f41,f55,f251,f110])).
% 0.20/0.57  fof(f110,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_13),
% 0.20/0.57    inference(avatar_component_clause,[],[f109])).
% 0.20/0.57  fof(f109,plain,(
% 0.20/0.57    spl2_13 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.57  fof(f251,plain,(
% 0.20/0.57    v1_relat_1(k2_xboole_0(sK0,sK1)) | ~spl2_18),
% 0.20/0.57    inference(avatar_component_clause,[],[f249])).
% 0.20/0.57  fof(f249,plain,(
% 0.20/0.57    spl2_18 <=> v1_relat_1(k2_xboole_0(sK0,sK1))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.20/0.57  fof(f55,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl2_4),
% 0.20/0.57    inference(avatar_component_clause,[],[f54])).
% 0.20/0.57  fof(f54,plain,(
% 0.20/0.57    spl2_4 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    v1_relat_1(sK0) | ~spl2_1),
% 0.20/0.57    inference(avatar_component_clause,[],[f39])).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    spl2_1 <=> v1_relat_1(sK0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.57  fof(f300,plain,(
% 0.20/0.57    ~spl2_19 | spl2_3 | ~spl2_10),
% 0.20/0.57    inference(avatar_split_clause,[],[f98,f89,f49,f297])).
% 0.20/0.57  fof(f49,plain,(
% 0.20/0.57    spl2_3 <=> r1_tarski(k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k4_xboole_0(sK0,sK1)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.57  fof(f89,plain,(
% 0.20/0.57    spl2_10 <=> ! [X1,X0,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.57  fof(f98,plain,(
% 0.20/0.57    ~r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k4_xboole_0(sK0,sK1)))) | (spl2_3 | ~spl2_10)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f51,f90])).
% 0.20/0.57  fof(f90,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) ) | ~spl2_10),
% 0.20/0.57    inference(avatar_component_clause,[],[f89])).
% 0.20/0.57  fof(f51,plain,(
% 0.20/0.57    ~r1_tarski(k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k4_xboole_0(sK0,sK1))) | spl2_3),
% 0.20/0.57    inference(avatar_component_clause,[],[f49])).
% 0.20/0.57  fof(f252,plain,(
% 0.20/0.57    spl2_18 | ~spl2_1 | ~spl2_2 | ~spl2_8),
% 0.20/0.57    inference(avatar_split_clause,[],[f83,f72,f44,f39,f249])).
% 0.20/0.57  fof(f72,plain,(
% 0.20/0.57    spl2_8 <=> ! [X1,X0] : (v1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.57  fof(f83,plain,(
% 0.20/0.57    v1_relat_1(k2_xboole_0(sK0,sK1)) | (~spl2_1 | ~spl2_2 | ~spl2_8)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f41,f46,f73])).
% 0.20/0.57  fof(f73,plain,(
% 0.20/0.57    ( ! [X0,X1] : (v1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_8),
% 0.20/0.57    inference(avatar_component_clause,[],[f72])).
% 0.20/0.57  fof(f115,plain,(
% 0.20/0.57    spl2_14),
% 0.20/0.57    inference(avatar_split_clause,[],[f26,f113])).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f13])).
% 0.20/0.57  fof(f13,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f9])).
% 0.20/0.57  fof(f9,axiom,(
% 0.20/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_relat_1)).
% 0.20/0.57  fof(f111,plain,(
% 0.20/0.57    spl2_13),
% 0.20/0.57    inference(avatar_split_clause,[],[f28,f109])).
% 0.20/0.57  fof(f28,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f15])).
% 0.20/0.57  fof(f15,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(flattening,[],[f14])).
% 0.20/0.57  fof(f14,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,axiom,(
% 0.20/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.20/0.57  fof(f97,plain,(
% 0.20/0.57    spl2_11 | ~spl2_1 | ~spl2_5),
% 0.20/0.57    inference(avatar_split_clause,[],[f69,f58,f39,f95])).
% 0.20/0.57  fof(f58,plain,(
% 0.20/0.57    spl2_5 <=> ! [X1,X0] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.57  fof(f69,plain,(
% 0.20/0.57    ( ! [X0] : (v1_relat_1(k4_xboole_0(sK0,X0))) ) | (~spl2_1 | ~spl2_5)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f41,f59])).
% 0.20/0.57  fof(f59,plain,(
% 0.20/0.57    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl2_5),
% 0.20/0.57    inference(avatar_component_clause,[],[f58])).
% 0.20/0.57  fof(f91,plain,(
% 0.20/0.57    spl2_10),
% 0.20/0.57    inference(avatar_split_clause,[],[f35,f89])).
% 0.20/0.57  fof(f35,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f19,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.20/0.57    inference(ennf_transformation,[],[f3])).
% 0.20/0.57  fof(f3,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.20/0.57  fof(f80,plain,(
% 0.20/0.57    spl2_9),
% 0.20/0.57    inference(avatar_split_clause,[],[f32,f78])).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f2])).
% 0.20/0.57  fof(f2,axiom,(
% 0.20/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.57  fof(f74,plain,(
% 0.20/0.57    spl2_8),
% 0.20/0.57    inference(avatar_split_clause,[],[f34,f72])).
% 0.20/0.57  fof(f34,plain,(
% 0.20/0.57    ( ! [X0,X1] : (v1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f18])).
% 0.20/0.57  fof(f18,plain,(
% 0.20/0.57    ! [X0,X1] : (v1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(flattening,[],[f17])).
% 0.20/0.57  fof(f17,plain,(
% 0.20/0.57    ! [X0,X1] : (v1_relat_1(k2_xboole_0(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f7])).
% 0.20/0.57  fof(f7,axiom,(
% 0.20/0.57    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k2_xboole_0(X0,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_relat_1)).
% 0.20/0.57  fof(f68,plain,(
% 0.20/0.57    spl2_7),
% 0.20/0.57    inference(avatar_split_clause,[],[f31,f66])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f1])).
% 0.20/0.57  fof(f1,axiom,(
% 0.20/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.57  fof(f60,plain,(
% 0.20/0.57    spl2_5),
% 0.20/0.57    inference(avatar_split_clause,[],[f33,f58])).
% 0.20/0.57  fof(f33,plain,(
% 0.20/0.57    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f16])).
% 0.20/0.57  fof(f16,plain,(
% 0.20/0.57    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,axiom,(
% 0.20/0.57    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).
% 0.20/0.57  fof(f56,plain,(
% 0.20/0.57    spl2_4),
% 0.20/0.57    inference(avatar_split_clause,[],[f29,f54])).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f4])).
% 0.20/0.57  fof(f4,axiom,(
% 0.20/0.57    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.57  fof(f52,plain,(
% 0.20/0.57    ~spl2_3),
% 0.20/0.57    inference(avatar_split_clause,[],[f37,f49])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    ~r1_tarski(k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k4_xboole_0(sK0,sK1)))),
% 0.20/0.57    inference(forward_demodulation,[],[f36,f30])).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f5])).
% 0.20/0.57  fof(f5,axiom,(
% 0.20/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    ~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k4_xboole_0(sK0,sK1)))),
% 0.20/0.57    inference(forward_demodulation,[],[f25,f30])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    ~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))),
% 0.20/0.57    inference(cnf_transformation,[],[f22])).
% 0.20/0.57  fof(f22,plain,(
% 0.20/0.57    (~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f21,f20])).
% 0.20/0.57  fof(f20,plain,(
% 0.20/0.57    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(sK0,X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f21,plain,(
% 0.20/0.57    ? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(sK0,X1))) & v1_relat_1(X1)) => (~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) & v1_relat_1(sK1))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f12,plain,(
% 0.20/0.57    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f11])).
% 0.20/0.57  fof(f11,negated_conjecture,(
% 0.20/0.57    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 0.20/0.57    inference(negated_conjecture,[],[f10])).
% 0.20/0.57  fof(f10,conjecture,(
% 0.20/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).
% 0.20/0.57  fof(f47,plain,(
% 0.20/0.57    spl2_2),
% 0.20/0.57    inference(avatar_split_clause,[],[f24,f44])).
% 0.20/0.57  fof(f24,plain,(
% 0.20/0.57    v1_relat_1(sK1)),
% 0.20/0.57    inference(cnf_transformation,[],[f22])).
% 0.20/0.57  fof(f42,plain,(
% 0.20/0.57    spl2_1),
% 0.20/0.57    inference(avatar_split_clause,[],[f23,f39])).
% 0.20/0.57  fof(f23,plain,(
% 0.20/0.57    v1_relat_1(sK0)),
% 0.20/0.57    inference(cnf_transformation,[],[f22])).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (30304)------------------------------
% 0.20/0.57  % (30304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (30304)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (30304)Memory used [KB]: 6268
% 0.20/0.57  % (30304)Time elapsed: 0.011 s
% 0.20/0.57  % (30304)------------------------------
% 0.20/0.57  % (30304)------------------------------
% 0.20/0.57  % (30165)Success in time 0.218 s
%------------------------------------------------------------------------------
