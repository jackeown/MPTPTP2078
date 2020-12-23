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
% DateTime   : Thu Dec  3 12:47:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 133 expanded)
%              Number of leaves         :   22 (  61 expanded)
%              Depth                    :    8
%              Number of atoms          :  249 ( 434 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f118,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f36,f41,f46,f50,f54,f58,f62,f66,f80,f96,f105,f111,f117])).

fof(f117,plain,
    ( ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | spl3_13
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | spl3_13
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f115,f103])).

fof(f103,plain,
    ( v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl3_14
  <=> v1_relat_1(k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f115,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | spl3_13 ),
    inference(subsumption_resolution,[],[f114,f35])).

fof(f35,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl3_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f114,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | spl3_13 ),
    inference(subsumption_resolution,[],[f113,f45])).

fof(f45,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl3_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f113,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ spl3_5
    | ~ spl3_11
    | spl3_13 ),
    inference(subsumption_resolution,[],[f112,f77])).

fof(f77,plain,
    ( ! [X2,X3] : r1_tarski(k3_xboole_0(X3,X2),X2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl3_11
  <=> ! [X3,X2] : r1_tarski(k3_xboole_0(X3,X2),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f112,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ spl3_5
    | spl3_13 ),
    inference(resolution,[],[f95,f49])).

fof(f49,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl3_5
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f95,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK2))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl3_13
  <=> r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f111,plain,
    ( ~ spl3_3
    | ~ spl3_8
    | spl3_14 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_8
    | spl3_14 ),
    inference(subsumption_resolution,[],[f107,f40])).

fof(f40,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl3_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f107,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl3_8
    | spl3_14 ),
    inference(resolution,[],[f104,f61])).

fof(f61,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( v1_relat_1(k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f104,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f102])).

fof(f105,plain,
    ( ~ spl3_14
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | spl3_12 ),
    inference(avatar_split_clause,[],[f100,f89,f52,f48,f43,f38,f102])).

fof(f52,plain,
    ( spl3_6
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f89,plain,
    ( spl3_12
  <=> r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f100,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | spl3_12 ),
    inference(subsumption_resolution,[],[f99,f40])).

fof(f99,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | spl3_12 ),
    inference(subsumption_resolution,[],[f98,f45])).

fof(f98,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ spl3_5
    | ~ spl3_6
    | spl3_12 ),
    inference(subsumption_resolution,[],[f97,f53])).

fof(f53,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f52])).

fof(f97,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ spl3_5
    | spl3_12 ),
    inference(resolution,[],[f49,f91])).

fof(f91,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f89])).

fof(f96,plain,
    ( ~ spl3_12
    | ~ spl3_13
    | spl3_1
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f87,f64,f28,f93,f89])).

fof(f28,plain,
    ( spl3_1
  <=> r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f64,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f87,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK2))
    | ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1))
    | spl3_1
    | ~ spl3_9 ),
    inference(resolution,[],[f30,f65])).

fof(f65,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f64])).

fof(f30,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f80,plain,
    ( spl3_11
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f70,f56,f52,f76])).

fof(f56,plain,
    ( spl3_7
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f70,plain,
    ( ! [X2,X3] : r1_tarski(k3_xboole_0(X3,X2),X2)
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(superposition,[],[f53,f57])).

fof(f57,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f56])).

fof(f66,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f26,f64])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f62,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f25,f60])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f58,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f24,f56])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f54,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f23,f52])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f50,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f22,f48])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

fof(f46,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f18,f43])).

fof(f18,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f16,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)))
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

fof(f41,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f19,f38])).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f36,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f20,f33])).

fof(f20,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f31,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f21,f28])).

fof(f21,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:48:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.41  % (18014)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.41  % (18012)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.41  % (18012)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f118,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f31,f36,f41,f46,f50,f54,f58,f62,f66,f80,f96,f105,f111,f117])).
% 0.21/0.41  fof(f117,plain,(
% 0.21/0.41    ~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_11 | spl3_13 | ~spl3_14),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f116])).
% 0.21/0.41  fof(f116,plain,(
% 0.21/0.41    $false | (~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_11 | spl3_13 | ~spl3_14)),
% 0.21/0.41    inference(subsumption_resolution,[],[f115,f103])).
% 0.21/0.41  fof(f103,plain,(
% 0.21/0.41    v1_relat_1(k3_xboole_0(sK1,sK2)) | ~spl3_14),
% 0.21/0.41    inference(avatar_component_clause,[],[f102])).
% 0.21/0.41  fof(f102,plain,(
% 0.21/0.41    spl3_14 <=> v1_relat_1(k3_xboole_0(sK1,sK2))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.41  fof(f115,plain,(
% 0.21/0.41    ~v1_relat_1(k3_xboole_0(sK1,sK2)) | (~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_11 | spl3_13)),
% 0.21/0.41    inference(subsumption_resolution,[],[f114,f35])).
% 0.21/0.41  fof(f35,plain,(
% 0.21/0.41    v1_relat_1(sK2) | ~spl3_2),
% 0.21/0.41    inference(avatar_component_clause,[],[f33])).
% 0.21/0.41  fof(f33,plain,(
% 0.21/0.41    spl3_2 <=> v1_relat_1(sK2)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.41  fof(f114,plain,(
% 0.21/0.41    ~v1_relat_1(sK2) | ~v1_relat_1(k3_xboole_0(sK1,sK2)) | (~spl3_4 | ~spl3_5 | ~spl3_11 | spl3_13)),
% 0.21/0.41    inference(subsumption_resolution,[],[f113,f45])).
% 0.21/0.41  fof(f45,plain,(
% 0.21/0.41    v1_relat_1(sK0) | ~spl3_4),
% 0.21/0.41    inference(avatar_component_clause,[],[f43])).
% 0.21/0.41  fof(f43,plain,(
% 0.21/0.41    spl3_4 <=> v1_relat_1(sK0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.41  fof(f113,plain,(
% 0.21/0.41    ~v1_relat_1(sK0) | ~v1_relat_1(sK2) | ~v1_relat_1(k3_xboole_0(sK1,sK2)) | (~spl3_5 | ~spl3_11 | spl3_13)),
% 0.21/0.41    inference(subsumption_resolution,[],[f112,f77])).
% 0.21/0.41  fof(f77,plain,(
% 0.21/0.41    ( ! [X2,X3] : (r1_tarski(k3_xboole_0(X3,X2),X2)) ) | ~spl3_11),
% 0.21/0.41    inference(avatar_component_clause,[],[f76])).
% 0.21/0.41  fof(f76,plain,(
% 0.21/0.41    spl3_11 <=> ! [X3,X2] : r1_tarski(k3_xboole_0(X3,X2),X2)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.41  fof(f112,plain,(
% 0.21/0.41    ~r1_tarski(k3_xboole_0(sK1,sK2),sK2) | ~v1_relat_1(sK0) | ~v1_relat_1(sK2) | ~v1_relat_1(k3_xboole_0(sK1,sK2)) | (~spl3_5 | spl3_13)),
% 0.21/0.41    inference(resolution,[],[f95,f49])).
% 0.21/0.41  fof(f49,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl3_5),
% 0.21/0.41    inference(avatar_component_clause,[],[f48])).
% 0.21/0.41  fof(f48,plain,(
% 0.21/0.41    spl3_5 <=> ! [X1,X0,X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.41  fof(f95,plain,(
% 0.21/0.41    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK2)) | spl3_13),
% 0.21/0.41    inference(avatar_component_clause,[],[f93])).
% 0.21/0.42  fof(f93,plain,(
% 0.21/0.42    spl3_13 <=> r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK2))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.42  fof(f111,plain,(
% 0.21/0.42    ~spl3_3 | ~spl3_8 | spl3_14),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f110])).
% 0.21/0.42  fof(f110,plain,(
% 0.21/0.42    $false | (~spl3_3 | ~spl3_8 | spl3_14)),
% 0.21/0.42    inference(subsumption_resolution,[],[f107,f40])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    v1_relat_1(sK1) | ~spl3_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f38])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    spl3_3 <=> v1_relat_1(sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.42  fof(f107,plain,(
% 0.21/0.42    ~v1_relat_1(sK1) | (~spl3_8 | spl3_14)),
% 0.21/0.42    inference(resolution,[],[f104,f61])).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl3_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f60])).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    spl3_8 <=> ! [X1,X0] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.42  fof(f104,plain,(
% 0.21/0.42    ~v1_relat_1(k3_xboole_0(sK1,sK2)) | spl3_14),
% 0.21/0.42    inference(avatar_component_clause,[],[f102])).
% 0.21/0.42  fof(f105,plain,(
% 0.21/0.42    ~spl3_14 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | spl3_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f100,f89,f52,f48,f43,f38,f102])).
% 0.21/0.42  fof(f52,plain,(
% 0.21/0.42    spl3_6 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.42  fof(f89,plain,(
% 0.21/0.42    spl3_12 <=> r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.42  fof(f100,plain,(
% 0.21/0.42    ~v1_relat_1(k3_xboole_0(sK1,sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | spl3_12)),
% 0.21/0.42    inference(subsumption_resolution,[],[f99,f40])).
% 0.21/0.42  fof(f99,plain,(
% 0.21/0.42    ~v1_relat_1(sK1) | ~v1_relat_1(k3_xboole_0(sK1,sK2)) | (~spl3_4 | ~spl3_5 | ~spl3_6 | spl3_12)),
% 0.21/0.42    inference(subsumption_resolution,[],[f98,f45])).
% 0.21/0.42  fof(f98,plain,(
% 0.21/0.42    ~v1_relat_1(sK0) | ~v1_relat_1(sK1) | ~v1_relat_1(k3_xboole_0(sK1,sK2)) | (~spl3_5 | ~spl3_6 | spl3_12)),
% 0.21/0.42    inference(subsumption_resolution,[],[f97,f53])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl3_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f52])).
% 0.21/0.42  fof(f97,plain,(
% 0.21/0.42    ~r1_tarski(k3_xboole_0(sK1,sK2),sK1) | ~v1_relat_1(sK0) | ~v1_relat_1(sK1) | ~v1_relat_1(k3_xboole_0(sK1,sK2)) | (~spl3_5 | spl3_12)),
% 0.21/0.42    inference(resolution,[],[f49,f91])).
% 0.21/0.42  fof(f91,plain,(
% 0.21/0.42    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1)) | spl3_12),
% 0.21/0.42    inference(avatar_component_clause,[],[f89])).
% 0.21/0.42  fof(f96,plain,(
% 0.21/0.42    ~spl3_12 | ~spl3_13 | spl3_1 | ~spl3_9),
% 0.21/0.42    inference(avatar_split_clause,[],[f87,f64,f28,f93,f89])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    spl3_1 <=> r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    spl3_9 <=> ! [X1,X0,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK2)) | ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1)) | (spl3_1 | ~spl3_9)),
% 0.21/0.42    inference(resolution,[],[f30,f65])).
% 0.21/0.42  fof(f65,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl3_9),
% 0.21/0.42    inference(avatar_component_clause,[],[f64])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) | spl3_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f28])).
% 0.21/0.42  fof(f80,plain,(
% 0.21/0.42    spl3_11 | ~spl3_6 | ~spl3_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f70,f56,f52,f76])).
% 0.21/0.42  fof(f56,plain,(
% 0.21/0.42    spl3_7 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    ( ! [X2,X3] : (r1_tarski(k3_xboole_0(X3,X2),X2)) ) | (~spl3_6 | ~spl3_7)),
% 0.21/0.42    inference(superposition,[],[f53,f57])).
% 0.21/0.42  fof(f57,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f56])).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    spl3_9),
% 0.21/0.42    inference(avatar_split_clause,[],[f26,f64])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.42    inference(flattening,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    spl3_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f25,f60])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    spl3_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f24,f56])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    spl3_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f23,f52])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    spl3_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f22,f48])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(flattening,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    spl3_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f18,f43])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    v1_relat_1(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ((~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) & v1_relat_1(sK2)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f16,f15,f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) & v1_relat_1(sK2))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,negated_conjecture,(
% 0.21/0.42    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 0.21/0.42    inference(negated_conjecture,[],[f6])).
% 0.21/0.42  fof(f6,conjecture,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    spl3_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f19,f38])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    v1_relat_1(sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f17])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    spl3_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f20,f33])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    v1_relat_1(sK2)),
% 0.21/0.42    inference(cnf_transformation,[],[f17])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    ~spl3_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f21,f28])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))),
% 0.21/0.42    inference(cnf_transformation,[],[f17])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (18012)------------------------------
% 0.21/0.42  % (18012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (18012)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (18012)Memory used [KB]: 10618
% 0.21/0.42  % (18012)Time elapsed: 0.007 s
% 0.21/0.42  % (18012)------------------------------
% 0.21/0.42  % (18012)------------------------------
% 0.21/0.42  % (18006)Success in time 0.063 s
%------------------------------------------------------------------------------
