%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t97_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:35 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   30 (  45 expanded)
%              Number of leaves         :    7 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 118 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f61,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f39,f46,f60])).

fof(f60,plain,
    ( ~ spl3_0
    | ~ spl3_2
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f59])).

fof(f59,plain,
    ( $false
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f58,f45])).

fof(f45,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK1),sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_5
  <=> ~ r1_tarski(k5_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f58,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK1),sK2)
    | ~ spl3_0
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f56,f24])).

fof(f24,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t97_xboole_1.p',d6_xboole_0)).

fof(f56,plain,
    ( r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2)
    | ~ spl3_0
    | ~ spl3_2 ),
    inference(resolution,[],[f53,f38])).

fof(f38,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK0),sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl3_2
  <=> r1_tarski(k4_xboole_0(sK1,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f53,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),sK2) )
    | ~ spl3_0 ),
    inference(resolution,[],[f25,f31])).

fof(f31,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl3_0
  <=> r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t97_xboole_1.p',t8_xboole_1)).

fof(f46,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f20,f44])).

fof(f20,plain,(
    ~ r1_tarski(k5_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK1),sK2)
    & r1_tarski(k4_xboole_0(sK1,sK0),sK2)
    & r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_xboole_0(X0,X1),X2)
        & r1_tarski(k4_xboole_0(X1,X0),X2)
        & r1_tarski(k4_xboole_0(X0,X1),X2) )
   => ( ~ r1_tarski(k5_xboole_0(sK0,sK1),sK2)
      & r1_tarski(k4_xboole_0(sK1,sK0),sK2)
      & r1_tarski(k4_xboole_0(sK0,sK1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X1),X2)
      & r1_tarski(k4_xboole_0(X1,X0),X2)
      & r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X1),X2)
      & r1_tarski(k4_xboole_0(X1,X0),X2)
      & r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(k4_xboole_0(X1,X0),X2)
          & r1_tarski(k4_xboole_0(X0,X1),X2) )
       => r1_tarski(k5_xboole_0(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k4_xboole_0(X1,X0),X2)
        & r1_tarski(k4_xboole_0(X0,X1),X2) )
     => r1_tarski(k5_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t97_xboole_1.p',t97_xboole_1)).

fof(f39,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f19,f37])).

fof(f19,plain,(
    r1_tarski(k4_xboole_0(sK1,sK0),sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f32,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f18,f30])).

fof(f18,plain,(
    r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
