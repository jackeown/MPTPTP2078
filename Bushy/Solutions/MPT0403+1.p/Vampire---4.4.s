%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : setfam_1__t29_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:17 EDT 2019

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   50 (  75 expanded)
%              Number of leaves         :   10 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :  113 ( 175 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4550,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f87,f168,f420,f1036,f4549])).

fof(f4549,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_124 ),
    inference(avatar_contradiction_clause,[],[f4548])).

fof(f4548,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_124 ),
    inference(subsumption_resolution,[],[f4546,f86])).

fof(f86,plain,
    ( r2_hidden(sK2(sK0,k2_setfam_1(sK0,sK0)),sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl8_2
  <=> r2_hidden(sK2(sK0,k2_setfam_1(sK0,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f4546,plain,
    ( ~ r2_hidden(sK2(sK0,k2_setfam_1(sK0,sK0)),sK0)
    | ~ spl8_1
    | ~ spl8_124 ),
    inference(resolution,[],[f4523,f45])).

fof(f45,plain,(
    ! [X0] : r1_setfam_1(X0,X0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : r1_setfam_1(X0,X0) ),
    inference(rectify,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : r1_setfam_1(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t29_setfam_1.p',reflexivity_r1_setfam_1)).

fof(f4523,plain,
    ( ! [X0] :
        ( ~ r1_setfam_1(X0,sK0)
        | ~ r2_hidden(sK2(sK0,k2_setfam_1(sK0,sK0)),X0) )
    | ~ spl8_1
    | ~ spl8_124 ),
    inference(subsumption_resolution,[],[f4521,f78])).

fof(f78,plain,
    ( ~ r1_setfam_1(sK0,k2_setfam_1(sK0,sK0))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl8_1
  <=> ~ r1_setfam_1(sK0,k2_setfam_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f4521,plain,
    ( ! [X0] :
        ( r1_setfam_1(sK0,k2_setfam_1(sK0,sK0))
        | ~ r2_hidden(sK2(sK0,k2_setfam_1(sK0,sK0)),X0)
        | ~ r1_setfam_1(X0,sK0) )
    | ~ spl8_124 ),
    inference(resolution,[],[f1058,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,sK3(X1,X2))
      | ~ r2_hidden(X2,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t29_setfam_1.p',d2_setfam_1)).

fof(f1058,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2(X0,k2_setfam_1(sK0,sK0)),sK3(sK0,sK2(sK0,k2_setfam_1(sK0,sK0))))
        | r1_setfam_1(X0,k2_setfam_1(sK0,sK0)) )
    | ~ spl8_124 ),
    inference(resolution,[],[f1035,f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r1_tarski(sK2(X0,X1),X3)
      | r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1035,plain,
    ( r2_hidden(sK3(sK0,sK2(sK0,k2_setfam_1(sK0,sK0))),k2_setfam_1(sK0,sK0))
    | ~ spl8_124 ),
    inference(avatar_component_clause,[],[f1034])).

fof(f1034,plain,
    ( spl8_124
  <=> r2_hidden(sK3(sK0,sK2(sK0,k2_setfam_1(sK0,sK0))),k2_setfam_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_124])])).

fof(f1036,plain,
    ( spl8_124
    | ~ spl8_54 ),
    inference(avatar_split_clause,[],[f448,f418,f1034])).

fof(f418,plain,
    ( spl8_54
  <=> sP5(sK3(sK0,sK2(sK0,k2_setfam_1(sK0,sK0))),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).

fof(f448,plain,
    ( r2_hidden(sK3(sK0,sK2(sK0,k2_setfam_1(sK0,sK0))),k2_setfam_1(sK0,sK0))
    | ~ spl8_54 ),
    inference(resolution,[],[f419,f71])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,k2_setfam_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_setfam_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k2_xboole_0(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t29_setfam_1.p',d4_setfam_1)).

fof(f419,plain,
    ( sP5(sK3(sK0,sK2(sK0,k2_setfam_1(sK0,sK0))),sK0,sK0)
    | ~ spl8_54 ),
    inference(avatar_component_clause,[],[f418])).

fof(f420,plain,
    ( spl8_54
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f306,f166,f418])).

fof(f166,plain,
    ( spl8_18
  <=> r2_hidden(sK3(sK0,sK2(sK0,k2_setfam_1(sK0,sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f306,plain,
    ( sP5(sK3(sK0,sK2(sK0,k2_setfam_1(sK0,sK0))),sK0,sK0)
    | ~ spl8_18 ),
    inference(forward_demodulation,[],[f300,f46])).

fof(f46,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t29_setfam_1.p',idempotence_k2_xboole_0)).

fof(f300,plain,
    ( sP5(k2_xboole_0(sK3(sK0,sK2(sK0,k2_setfam_1(sK0,sK0))),sK3(sK0,sK2(sK0,k2_setfam_1(sK0,sK0)))),sK0,sK0)
    | ~ spl8_18 ),
    inference(resolution,[],[f182,f167])).

fof(f167,plain,
    ( r2_hidden(sK3(sK0,sK2(sK0,k2_setfam_1(sK0,sK0))),sK0)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f166])).

fof(f182,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X3,X4)
        | sP5(k2_xboole_0(sK3(sK0,sK2(sK0,k2_setfam_1(sK0,sK0))),X3),X4,sK0) )
    | ~ spl8_18 ),
    inference(resolution,[],[f167,f72])).

fof(f72,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | sP5(k2_xboole_0(X4,X5),X1,X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k2_xboole_0(X4,X5) != X3
      | sP5(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f168,plain,
    ( spl8_18
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f128,f85,f166])).

fof(f128,plain,
    ( r2_hidden(sK3(sK0,sK2(sK0,k2_setfam_1(sK0,sK0))),sK0)
    | ~ spl8_2 ),
    inference(resolution,[],[f92,f45])).

fof(f92,plain,
    ( ! [X4] :
        ( ~ r1_setfam_1(sK0,X4)
        | r2_hidden(sK3(X4,sK2(sK0,k2_setfam_1(sK0,sK0))),X4) )
    | ~ spl8_2 ),
    inference(resolution,[],[f86,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(sK3(X1,X2),X1)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f87,plain,
    ( spl8_2
    | spl8_1 ),
    inference(avatar_split_clause,[],[f80,f77,f85])).

fof(f80,plain,
    ( r2_hidden(sK2(sK0,k2_setfam_1(sK0,sK0)),sK0)
    | ~ spl8_1 ),
    inference(resolution,[],[f78,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f79,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f40,f77])).

fof(f40,plain,(
    ~ r1_setfam_1(sK0,k2_setfam_1(sK0,sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0] : ~ r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t29_setfam_1.p',t29_setfam_1)).
%------------------------------------------------------------------------------
