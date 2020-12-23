%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 130 expanded)
%              Number of leaves         :   22 (  58 expanded)
%              Depth                    :    7
%              Number of atoms          :  215 ( 356 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f357,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f49,f55,f59,f63,f75,f90,f98,f109,f121,f132,f137,f253,f356])).

fof(f356,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_16
    | spl3_17
    | ~ spl3_25 ),
    inference(avatar_contradiction_clause,[],[f355])).

fof(f355,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_16
    | spl3_17
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f136,f330])).

% (10319)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
fof(f330,plain,
    ( ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,k10_relat_1(sK2,X1))),X1)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_16
    | ~ spl3_25 ),
    inference(unit_resulting_resolution,[],[f38,f43,f131,f252])).

fof(f252,plain,
    ( ! [X4,X5,X3] :
        ( ~ r1_tarski(X5,k9_relat_1(X4,k10_relat_1(X4,X3)))
        | r1_tarski(X5,X3)
        | ~ v1_funct_1(X4)
        | ~ v1_relat_1(X4) )
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl3_25
  <=> ! [X3,X5,X4] :
        ( ~ r1_tarski(X5,k9_relat_1(X4,k10_relat_1(X4,X3)))
        | r1_tarski(X5,X3)
        | ~ v1_funct_1(X4)
        | ~ v1_relat_1(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f131,plain,
    ( ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X1,X0)),k9_relat_1(sK2,X0))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl3_16
  <=> ! [X1,X0] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X1,X0)),k9_relat_1(sK2,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f43,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f38,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f136,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1)
    | spl3_17 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl3_17
  <=> r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f253,plain,
    ( spl3_25
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f114,f107,f73,f251])).

fof(f73,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X1)
        | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f107,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f114,plain,
    ( ! [X4,X5,X3] :
        ( ~ r1_tarski(X5,k9_relat_1(X4,k10_relat_1(X4,X3)))
        | r1_tarski(X5,X3)
        | ~ v1_funct_1(X4)
        | ~ v1_relat_1(X4) )
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(superposition,[],[f74,f108])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f107])).

fof(f74,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
        | r1_tarski(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f73])).

fof(f137,plain,
    ( ~ spl3_17
    | ~ spl3_1
    | spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f105,f96,f88,f57,f52,f36,f134])).

fof(f52,plain,
    ( spl3_4
  <=> r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK1,k9_relat_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f57,plain,
    ( spl3_5
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f88,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f96,plain,
    ( spl3_13
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f105,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1)
    | ~ spl3_1
    | spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f100,f104])).

fof(f104,plain,
    ( ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k9_relat_1(sK2,X0))
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f38,f58,f97])).

fof(f97,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f96])).

fof(f58,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f100,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1)
    | spl3_4
    | ~ spl3_11 ),
    inference(resolution,[],[f89,f54])).

fof(f54,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK1,k9_relat_1(sK2,sK0)))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f89,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f88])).

fof(f132,plain,
    ( spl3_16
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f126,f119,f61,f130])).

fof(f61,plain,
    ( spl3_6
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f119,plain,
    ( spl3_15
  <=> ! [X1,X0] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k9_relat_1(sK2,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f126,plain,
    ( ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X1,X0)),k9_relat_1(sK2,X0))
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(superposition,[],[f120,f62])).

fof(f62,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f120,plain,
    ( ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k9_relat_1(sK2,X0))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f119])).

fof(f121,plain,
    ( spl3_15
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f104,f96,f57,f36,f119])).

fof(f109,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f30,f107])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f98,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f32,f96])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(f90,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f34,f88])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f75,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f33,f73])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f63,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f27,f61])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f59,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f26,f57])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f55,plain,
    ( ~ spl3_4
    | spl3_3 ),
    inference(avatar_split_clause,[],[f50,f46,f52])).

fof(f46,plain,
    ( spl3_3
  <=> r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f50,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK1,k9_relat_1(sK2,sK0)))
    | spl3_3 ),
    inference(forward_demodulation,[],[f48,f27])).

fof(f48,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f49,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f25,f46])).

fof(f25,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).

fof(f44,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f24,f41])).

fof(f24,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f23,f36])).

fof(f23,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:57:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.44  % (10311)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.45  % (10311)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f357,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f39,f44,f49,f55,f59,f63,f75,f90,f98,f109,f121,f132,f137,f253,f356])).
% 0.22/0.45  fof(f356,plain,(
% 0.22/0.45    ~spl3_1 | ~spl3_2 | ~spl3_16 | spl3_17 | ~spl3_25),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f355])).
% 0.22/0.45  fof(f355,plain,(
% 0.22/0.45    $false | (~spl3_1 | ~spl3_2 | ~spl3_16 | spl3_17 | ~spl3_25)),
% 0.22/0.45    inference(subsumption_resolution,[],[f136,f330])).
% 0.22/0.45  % (10319)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.45  fof(f330,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,k10_relat_1(sK2,X1))),X1)) ) | (~spl3_1 | ~spl3_2 | ~spl3_16 | ~spl3_25)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f38,f43,f131,f252])).
% 0.22/0.45  fof(f252,plain,(
% 0.22/0.45    ( ! [X4,X5,X3] : (~r1_tarski(X5,k9_relat_1(X4,k10_relat_1(X4,X3))) | r1_tarski(X5,X3) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) ) | ~spl3_25),
% 0.22/0.45    inference(avatar_component_clause,[],[f251])).
% 0.22/0.45  fof(f251,plain,(
% 0.22/0.45    spl3_25 <=> ! [X3,X5,X4] : (~r1_tarski(X5,k9_relat_1(X4,k10_relat_1(X4,X3))) | r1_tarski(X5,X3) | ~v1_funct_1(X4) | ~v1_relat_1(X4))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.45  fof(f131,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X1,X0)),k9_relat_1(sK2,X0))) ) | ~spl3_16),
% 0.22/0.45    inference(avatar_component_clause,[],[f130])).
% 0.22/0.45  fof(f130,plain,(
% 0.22/0.45    spl3_16 <=> ! [X1,X0] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X1,X0)),k9_relat_1(sK2,X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.45  fof(f43,plain,(
% 0.22/0.45    v1_funct_1(sK2) | ~spl3_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f41])).
% 0.22/0.45  fof(f41,plain,(
% 0.22/0.45    spl3_2 <=> v1_funct_1(sK2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.45  fof(f38,plain,(
% 0.22/0.45    v1_relat_1(sK2) | ~spl3_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f36])).
% 0.22/0.45  fof(f36,plain,(
% 0.22/0.45    spl3_1 <=> v1_relat_1(sK2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.45  fof(f136,plain,(
% 0.22/0.45    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1) | spl3_17),
% 0.22/0.45    inference(avatar_component_clause,[],[f134])).
% 0.22/0.45  fof(f134,plain,(
% 0.22/0.45    spl3_17 <=> r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.45  fof(f253,plain,(
% 0.22/0.45    spl3_25 | ~spl3_9 | ~spl3_14),
% 0.22/0.45    inference(avatar_split_clause,[],[f114,f107,f73,f251])).
% 0.22/0.45  fof(f73,plain,(
% 0.22/0.45    spl3_9 <=> ! [X1,X0,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.45  fof(f107,plain,(
% 0.22/0.45    spl3_14 <=> ! [X1,X0] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.45  fof(f114,plain,(
% 0.22/0.45    ( ! [X4,X5,X3] : (~r1_tarski(X5,k9_relat_1(X4,k10_relat_1(X4,X3))) | r1_tarski(X5,X3) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) ) | (~spl3_9 | ~spl3_14)),
% 0.22/0.45    inference(superposition,[],[f74,f108])).
% 0.22/0.45  fof(f108,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | ~spl3_14),
% 0.22/0.45    inference(avatar_component_clause,[],[f107])).
% 0.22/0.45  fof(f74,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,X2)) | r1_tarski(X0,X1)) ) | ~spl3_9),
% 0.22/0.45    inference(avatar_component_clause,[],[f73])).
% 0.22/0.45  fof(f137,plain,(
% 0.22/0.45    ~spl3_17 | ~spl3_1 | spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_13),
% 0.22/0.45    inference(avatar_split_clause,[],[f105,f96,f88,f57,f52,f36,f134])).
% 0.22/0.45  fof(f52,plain,(
% 0.22/0.45    spl3_4 <=> r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK1,k9_relat_1(sK2,sK0)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.45  fof(f57,plain,(
% 0.22/0.45    spl3_5 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.45  fof(f88,plain,(
% 0.22/0.45    spl3_11 <=> ! [X1,X0,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.45  fof(f96,plain,(
% 0.22/0.45    spl3_13 <=> ! [X1,X0,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.45  fof(f105,plain,(
% 0.22/0.45    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1) | (~spl3_1 | spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_13)),
% 0.22/0.45    inference(subsumption_resolution,[],[f100,f104])).
% 0.22/0.45  fof(f104,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k9_relat_1(sK2,X0))) ) | (~spl3_1 | ~spl3_5 | ~spl3_13)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f38,f58,f97])).
% 0.22/0.45  fof(f97,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) ) | ~spl3_13),
% 0.22/0.45    inference(avatar_component_clause,[],[f96])).
% 0.22/0.45  fof(f58,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl3_5),
% 0.22/0.45    inference(avatar_component_clause,[],[f57])).
% 0.22/0.45  fof(f100,plain,(
% 0.22/0.45    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0)) | ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1) | (spl3_4 | ~spl3_11)),
% 0.22/0.45    inference(resolution,[],[f89,f54])).
% 0.22/0.45  fof(f54,plain,(
% 0.22/0.45    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK1,k9_relat_1(sK2,sK0))) | spl3_4),
% 0.22/0.45    inference(avatar_component_clause,[],[f52])).
% 0.22/0.45  fof(f89,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl3_11),
% 0.22/0.45    inference(avatar_component_clause,[],[f88])).
% 0.22/0.45  fof(f132,plain,(
% 0.22/0.45    spl3_16 | ~spl3_6 | ~spl3_15),
% 0.22/0.45    inference(avatar_split_clause,[],[f126,f119,f61,f130])).
% 0.22/0.45  fof(f61,plain,(
% 0.22/0.45    spl3_6 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.45  fof(f119,plain,(
% 0.22/0.45    spl3_15 <=> ! [X1,X0] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k9_relat_1(sK2,X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.45  fof(f126,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X1,X0)),k9_relat_1(sK2,X0))) ) | (~spl3_6 | ~spl3_15)),
% 0.22/0.45    inference(superposition,[],[f120,f62])).
% 0.22/0.45  fof(f62,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_6),
% 0.22/0.45    inference(avatar_component_clause,[],[f61])).
% 0.22/0.45  fof(f120,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k9_relat_1(sK2,X0))) ) | ~spl3_15),
% 0.22/0.45    inference(avatar_component_clause,[],[f119])).
% 0.22/0.45  fof(f121,plain,(
% 0.22/0.45    spl3_15 | ~spl3_1 | ~spl3_5 | ~spl3_13),
% 0.22/0.45    inference(avatar_split_clause,[],[f104,f96,f57,f36,f119])).
% 0.22/0.45  fof(f109,plain,(
% 0.22/0.45    spl3_14),
% 0.22/0.45    inference(avatar_split_clause,[],[f30,f107])).
% 0.22/0.45  fof(f30,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(flattening,[],[f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.45    inference(ennf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,axiom,(
% 0.22/0.45    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 0.22/0.45  fof(f98,plain,(
% 0.22/0.45    spl3_13),
% 0.22/0.45    inference(avatar_split_clause,[],[f32,f96])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.45    inference(flattening,[],[f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.45    inference(ennf_transformation,[],[f8])).
% 0.22/0.45  fof(f8,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).
% 0.22/0.45  fof(f90,plain,(
% 0.22/0.45    spl3_11),
% 0.22/0.45    inference(avatar_split_clause,[],[f34,f88])).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f20])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.45    inference(flattening,[],[f19])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.45    inference(ennf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.22/0.45  fof(f75,plain,(
% 0.22/0.45    spl3_9),
% 0.22/0.45    inference(avatar_split_clause,[],[f33,f73])).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.45    inference(ennf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.22/0.45  fof(f63,plain,(
% 0.22/0.45    spl3_6),
% 0.22/0.45    inference(avatar_split_clause,[],[f27,f61])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.45  fof(f59,plain,(
% 0.22/0.45    spl3_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f26,f57])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.45  fof(f55,plain,(
% 0.22/0.45    ~spl3_4 | spl3_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f50,f46,f52])).
% 0.22/0.45  fof(f46,plain,(
% 0.22/0.45    spl3_3 <=> r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.45  fof(f50,plain,(
% 0.22/0.45    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK1,k9_relat_1(sK2,sK0))) | spl3_3),
% 0.22/0.45    inference(forward_demodulation,[],[f48,f27])).
% 0.22/0.45  fof(f48,plain,(
% 0.22/0.45    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) | spl3_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f46])).
% 0.22/0.45  fof(f49,plain,(
% 0.22/0.45    ~spl3_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f25,f46])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))),
% 0.22/0.45    inference(cnf_transformation,[],[f22])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f21])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.45    inference(flattening,[],[f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.45    inference(ennf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,negated_conjecture,(
% 0.22/0.45    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 0.22/0.45    inference(negated_conjecture,[],[f10])).
% 0.22/0.45  fof(f10,conjecture,(
% 0.22/0.45    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).
% 0.22/0.45  fof(f44,plain,(
% 0.22/0.45    spl3_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f24,f41])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    v1_funct_1(sK2)),
% 0.22/0.45    inference(cnf_transformation,[],[f22])).
% 0.22/0.45  fof(f39,plain,(
% 0.22/0.45    spl3_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f23,f36])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    v1_relat_1(sK2)),
% 0.22/0.45    inference(cnf_transformation,[],[f22])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (10311)------------------------------
% 0.22/0.45  % (10311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (10311)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (10311)Memory used [KB]: 6396
% 0.22/0.45  % (10311)Time elapsed: 0.015 s
% 0.22/0.45  % (10311)------------------------------
% 0.22/0.45  % (10311)------------------------------
% 0.22/0.45  % (10300)Success in time 0.087 s
%------------------------------------------------------------------------------
