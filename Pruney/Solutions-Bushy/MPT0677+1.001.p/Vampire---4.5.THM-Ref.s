%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0677+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:26 EST 2020

% Result     : Theorem 2.87s
% Output     : Refutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 280 expanded)
%              Number of leaves         :   16 (  77 expanded)
%              Depth                    :   13
%              Number of atoms          :  371 ( 973 expanded)
%              Number of equality atoms :   54 ( 179 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1991,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f92,f96,f100,f117,f129,f320,f398,f1848,f1990])).

fof(f1990,plain,
    ( ~ spl10_13
    | spl10_14 ),
    inference(avatar_contradiction_clause,[],[f1977])).

fof(f1977,plain,
    ( $false
    | ~ spl10_13
    | spl10_14 ),
    inference(unit_resulting_resolution,[],[f65,f314,f1855,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f1855,plain,
    ( ! [X0] : ~ r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k3_xboole_0(k9_relat_1(sK2,sK1),X0))
    | spl10_14 ),
    inference(unit_resulting_resolution,[],[f319,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f319,plain,
    ( ~ r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK1))
    | spl10_14 ),
    inference(avatar_component_clause,[],[f317])).

fof(f317,plain,
    ( spl10_14
  <=> r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f314,plain,
    ( r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f313])).

fof(f313,plain,
    ( spl10_13
  <=> r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X1,X0)),k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ),
    inference(superposition,[],[f53,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ),
    inference(unit_resulting_resolution,[],[f17,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) != k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) != k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( v2_funct_1(X2)
         => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

fof(f1848,plain,
    ( ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_9
    | ~ spl10_12
    | spl10_13 ),
    inference(avatar_contradiction_clause,[],[f1833])).

fof(f1833,plain,
    ( $false
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_9
    | ~ spl10_12
    | spl10_13 ),
    inference(unit_resulting_resolution,[],[f405,f458,f513,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f513,plain,
    ( ~ r2_hidden(sK5(sK2,sK0,sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k3_xboole_0(sK0,sK1))
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_12
    | spl10_13 ),
    inference(unit_resulting_resolution,[],[f315,f310,f404,f101])).

fof(f101,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X1,k9_relat_1(sK2,X2))
        | ~ r2_hidden(sK5(sK2,X0,X1),k1_relat_1(sK2))
        | ~ r2_hidden(sK5(sK2,X0,X1),X2)
        | ~ r2_hidden(X1,k9_relat_1(sK2,X0)) )
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(superposition,[],[f99,f95])).

fof(f95,plain,
    ( ! [X14,X13] :
        ( k1_funct_1(sK2,sK5(sK2,X13,X14)) = X14
        | ~ r2_hidden(X14,k9_relat_1(sK2,X13)) )
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl10_4
  <=> ! [X13,X14] :
        ( k1_funct_1(sK2,sK5(sK2,X13,X14)) = X14
        | ~ r2_hidden(X14,k9_relat_1(sK2,X13)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f99,plain,
    ( ! [X12,X11] :
        ( r2_hidden(k1_funct_1(sK2,X11),k9_relat_1(sK2,X12))
        | ~ r2_hidden(X11,k1_relat_1(sK2))
        | ~ r2_hidden(X11,X12) )
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl10_5
  <=> ! [X11,X12] :
        ( ~ r2_hidden(X11,k1_relat_1(sK2))
        | r2_hidden(k1_funct_1(sK2,X11),k9_relat_1(sK2,X12))
        | ~ r2_hidden(X11,X12) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f404,plain,
    ( r2_hidden(sK5(sK2,sK0,sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k1_relat_1(sK2))
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f18,f17,f310,f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK5(X0,X1,X3),k1_relat_1(X0))
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK5(X0,X1,X3),k1_relat_1(X0))
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(f18,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f310,plain,
    ( r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK0))
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f309])).

fof(f309,plain,
    ( spl10_12
  <=> r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f315,plain,
    ( ~ r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | spl10_13 ),
    inference(avatar_component_clause,[],[f313])).

fof(f458,plain,
    ( r2_hidden(sK5(sK2,sK0,sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))),sK1)
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_9
    | ~ spl10_12
    | spl10_13 ),
    inference(backward_demodulation,[],[f445,f442])).

fof(f442,plain,
    ( sK5(sK2,sK0,sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))) = sK5(sK2,sK1,sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_9
    | ~ spl10_12
    | spl10_13 ),
    inference(unit_resulting_resolution,[],[f310,f419,f177])).

fof(f177,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X1,k9_relat_1(sK2,X2))
        | sK5(sK2,X0,X1) = sK5(sK2,X2,X1)
        | ~ r2_hidden(X1,k9_relat_1(sK2,X0)) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_9 ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,
    ( ! [X2,X0,X1] :
        ( sK5(sK2,X0,X1) = sK5(sK2,X2,X1)
        | ~ r2_hidden(X1,k9_relat_1(sK2,X2))
        | ~ r2_hidden(X1,k9_relat_1(sK2,X0))
        | ~ r2_hidden(X1,k9_relat_1(sK2,X0)) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_9 ),
    inference(resolution,[],[f167,f91])).

fof(f91,plain,
    ( ! [X17,X18] :
        ( r2_hidden(sK5(sK2,X17,X18),k1_relat_1(sK2))
        | ~ r2_hidden(X18,k9_relat_1(sK2,X17)) )
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl10_3
  <=> ! [X18,X17] :
        ( r2_hidden(sK5(sK2,X17,X18),k1_relat_1(sK2))
        | ~ r2_hidden(X18,k9_relat_1(sK2,X17)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f167,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK5(sK2,X0,X1),k1_relat_1(sK2))
        | sK5(sK2,X0,X1) = sK5(sK2,X2,X1)
        | ~ r2_hidden(X1,k9_relat_1(sK2,X2))
        | ~ r2_hidden(X1,k9_relat_1(sK2,X0)) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_9 ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,
    ( ! [X2,X0,X1] :
        ( sK5(sK2,X0,X1) = sK5(sK2,X2,X1)
        | ~ r2_hidden(sK5(sK2,X0,X1),k1_relat_1(sK2))
        | ~ r2_hidden(X1,k9_relat_1(sK2,X2))
        | ~ r2_hidden(X1,k9_relat_1(sK2,X0))
        | ~ r2_hidden(X1,k9_relat_1(sK2,X2)) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_9 ),
    inference(resolution,[],[f145,f91])).

fof(f145,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK5(sK2,X2,X1),k1_relat_1(sK2))
        | sK5(sK2,X0,X1) = sK5(sK2,X2,X1)
        | ~ r2_hidden(sK5(sK2,X0,X1),k1_relat_1(sK2))
        | ~ r2_hidden(X1,k9_relat_1(sK2,X2))
        | ~ r2_hidden(X1,k9_relat_1(sK2,X0)) )
    | ~ spl10_4
    | ~ spl10_9 ),
    inference(superposition,[],[f144,f95])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( sK5(sK2,X0,k1_funct_1(sK2,X1)) = X1
        | ~ r2_hidden(sK5(sK2,X0,k1_funct_1(sK2,X1)),k1_relat_1(sK2))
        | ~ r2_hidden(X1,k1_relat_1(sK2))
        | ~ r2_hidden(k1_funct_1(sK2,X1),k9_relat_1(sK2,X0)) )
    | ~ spl10_4
    | ~ spl10_9 ),
    inference(equality_resolution,[],[f130])).

fof(f130,plain,
    ( ! [X2,X0,X1] :
        ( k1_funct_1(sK2,X2) != X1
        | sK5(sK2,X0,X1) = X2
        | ~ r2_hidden(sK5(sK2,X0,X1),k1_relat_1(sK2))
        | ~ r2_hidden(X2,k1_relat_1(sK2))
        | ~ r2_hidden(X1,k9_relat_1(sK2,X0)) )
    | ~ spl10_4
    | ~ spl10_9 ),
    inference(superposition,[],[f116,f95])).

fof(f116,plain,
    ( ! [X10,X9] :
        ( k1_funct_1(sK2,X9) != k1_funct_1(sK2,X10)
        | X9 = X10
        | ~ r2_hidden(X9,k1_relat_1(sK2))
        | ~ r2_hidden(X10,k1_relat_1(sK2)) )
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl10_9
  <=> ! [X9,X10] :
        ( ~ r2_hidden(X9,k1_relat_1(sK2))
        | X9 = X10
        | k1_funct_1(sK2,X9) != k1_funct_1(sK2,X10)
        | ~ r2_hidden(X10,k1_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f419,plain,
    ( r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK1))
    | spl10_13 ),
    inference(unit_resulting_resolution,[],[f20,f315,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f20,plain,(
    k9_relat_1(sK2,k3_xboole_0(sK0,sK1)) != k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f445,plain,
    ( r2_hidden(sK5(sK2,sK1,sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))),sK1)
    | spl10_13 ),
    inference(unit_resulting_resolution,[],[f18,f17,f419,f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f405,plain,
    ( r2_hidden(sK5(sK2,sK0,sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))),sK0)
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f18,f17,f310,f51])).

fof(f398,plain,(
    spl10_12 ),
    inference(avatar_contradiction_clause,[],[f386])).

fof(f386,plain,
    ( $false
    | spl10_12 ),
    inference(unit_resulting_resolution,[],[f53,f348,f355,f42])).

fof(f355,plain,
    ( ! [X0] : ~ r2_hidden(sK9(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0)),k3_xboole_0(k9_relat_1(sK2,sK0),X0))
    | spl10_12 ),
    inference(unit_resulting_resolution,[],[f349,f47])).

fof(f349,plain,
    ( ~ r2_hidden(sK9(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0)),k9_relat_1(sK2,sK0))
    | spl10_12 ),
    inference(unit_resulting_resolution,[],[f340,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK9(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f340,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0))
    | spl10_12 ),
    inference(unit_resulting_resolution,[],[f311,f321,f42])).

fof(f321,plain,
    ( r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | spl10_12 ),
    inference(unit_resulting_resolution,[],[f20,f311,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f311,plain,
    ( ~ r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK0))
    | spl10_12 ),
    inference(avatar_component_clause,[],[f309])).

fof(f348,plain,
    ( r2_hidden(sK9(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0)),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | spl10_12 ),
    inference(unit_resulting_resolution,[],[f340,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK9(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f320,plain,
    ( ~ spl10_12
    | ~ spl10_13
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f154,f317,f313,f309])).

fof(f154,plain,
    ( ~ r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK1))
    | ~ r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | ~ r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK0)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( k9_relat_1(sK2,k3_xboole_0(sK0,sK1)) != X0
      | ~ r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),X0),k9_relat_1(sK2,sK1))
      | ~ r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),X0),X0)
      | ~ r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),X0),k9_relat_1(sK2,sK0)) ) ),
    inference(superposition,[],[f20,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f129,plain,(
    spl10_8 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | spl10_8 ),
    inference(unit_resulting_resolution,[],[f19,f113])).

fof(f113,plain,
    ( ~ v2_funct_1(sK2)
    | spl10_8 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl10_8
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f19,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f117,plain,
    ( ~ spl10_8
    | spl10_9
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f59,f75,f115,f111])).

fof(f75,plain,
    ( spl10_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f59,plain,(
    ! [X10,X9] :
      ( ~ v1_relat_1(sK2)
      | ~ r2_hidden(X9,k1_relat_1(sK2))
      | ~ r2_hidden(X10,k1_relat_1(sK2))
      | k1_funct_1(sK2,X9) != k1_funct_1(sK2,X10)
      | X9 = X10
      | ~ v2_funct_1(sK2) ) ),
    inference(resolution,[],[f18,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
      | X1 = X2
      | ~ v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f100,plain,
    ( spl10_5
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f60,f75,f98])).

fof(f60,plain,(
    ! [X12,X11] :
      ( ~ v1_relat_1(sK2)
      | ~ r2_hidden(X11,k1_relat_1(sK2))
      | ~ r2_hidden(X11,X12)
      | r2_hidden(k1_funct_1(sK2,X11),k9_relat_1(sK2,X12)) ) ),
    inference(resolution,[],[f18,f49])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | r2_hidden(k1_funct_1(X0,X4),k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | r2_hidden(k1_funct_1(X0,X4),X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | k1_funct_1(X0,X4) != X3
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f96,plain,
    ( spl10_4
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f61,f75,f94])).

fof(f61,plain,(
    ! [X14,X13] :
      ( ~ v1_relat_1(sK2)
      | k1_funct_1(sK2,sK5(sK2,X13,X14)) = X14
      | ~ r2_hidden(X14,k9_relat_1(sK2,X13)) ) ),
    inference(resolution,[],[f18,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK5(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK5(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f92,plain,
    ( spl10_3
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f63,f75,f90])).

fof(f63,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(sK2)
      | r2_hidden(sK5(sK2,X17,X18),k1_relat_1(sK2))
      | ~ r2_hidden(X18,k9_relat_1(sK2,X17)) ) ),
    inference(resolution,[],[f18,f52])).

fof(f82,plain,(
    spl10_2 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | spl10_2 ),
    inference(unit_resulting_resolution,[],[f17,f77])).

fof(f77,plain,
    ( ~ v1_relat_1(sK2)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f75])).

%------------------------------------------------------------------------------
