%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t114_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:21 EDT 2019

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   40 (  69 expanded)
%              Number of leaves         :    8 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :   87 ( 178 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f148,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f132,f137,f142,f147])).

fof(f147,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f145,f15])).

fof(f15,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      & r1_xboole_0(X2,X3)
      & r1_xboole_0(X1,X3)
      & r1_xboole_0(X0,X3) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      & r1_xboole_0(X2,X3)
      & r1_xboole_0(X1,X3)
      & r1_xboole_0(X0,X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X3)
          & r1_xboole_0(X1,X3)
          & r1_xboole_0(X0,X3) )
       => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        & r1_xboole_0(X1,X3)
        & r1_xboole_0(X0,X3) )
     => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t114_xboole_1.p',t114_xboole_1)).

fof(f145,plain,
    ( ~ r1_xboole_0(sK2,sK3)
    | ~ spl4_3 ),
    inference(resolution,[],[f111,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t114_xboole_1.p',symmetry_r1_xboole_0)).

fof(f111,plain,
    ( ~ r1_xboole_0(sK3,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl4_3
  <=> ~ r1_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f142,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f140,f13])).

fof(f13,plain,(
    r1_xboole_0(sK0,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f140,plain,
    ( ~ r1_xboole_0(sK0,sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f131,f19])).

fof(f131,plain,
    ( ~ r1_xboole_0(sK3,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl4_7
  <=> ~ r1_xboole_0(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f137,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f135,f14])).

fof(f14,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f135,plain,
    ( ~ r1_xboole_0(sK1,sK3)
    | ~ spl4_5 ),
    inference(resolution,[],[f125,f19])).

fof(f125,plain,
    ( ~ r1_xboole_0(sK3,sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl4_5
  <=> ~ r1_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f132,plain,
    ( ~ spl4_5
    | ~ spl4_7
    | spl4_1 ),
    inference(avatar_split_clause,[],[f113,f104,f130,f124])).

fof(f104,plain,
    ( spl4_1
  <=> ~ r1_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f113,plain,
    ( ~ r1_xboole_0(sK3,sK0)
    | ~ r1_xboole_0(sK3,sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f105,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t114_xboole_1.p',t70_xboole_1)).

fof(f105,plain,
    ( ~ r1_xboole_0(sK3,k2_xboole_0(sK0,sK1))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f112,plain,
    ( ~ spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f89,f110,f104])).

fof(f89,plain,
    ( ~ r1_xboole_0(sK3,sK2)
    | ~ r1_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f22,f24])).

fof(f24,plain,(
    ~ r1_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f23,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t114_xboole_1.p',commutativity_k2_xboole_0)).

fof(f23,plain,(
    ~ r1_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK0,sK1),sK2)) ),
    inference(resolution,[],[f19,f16])).

fof(f16,plain,(
    ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
