%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:53 EST 2020

% Result     : Theorem 4.62s
% Output     : Refutation 4.62s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 379 expanded)
%              Number of leaves         :   39 ( 151 expanded)
%              Depth                    :   12
%              Number of atoms          :  325 ( 647 expanded)
%              Number of equality atoms :   76 ( 246 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12241,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f68,f73,f199,f204,f235,f240,f485,f489,f498,f503,f10488,f10493,f10588,f10705,f10986,f11046,f11153,f11334,f11451,f11571,f12240])).

fof(f12240,plain,
    ( spl5_146
    | ~ spl5_157 ),
    inference(avatar_contradiction_clause,[],[f12233])).

fof(f12233,plain,
    ( $false
    | spl5_146
    | ~ spl5_157 ),
    inference(unit_resulting_resolution,[],[f11152,f55,f11570])).

fof(f11570,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK2)
        | r1_tarski(X2,sK1) )
    | ~ spl5_157 ),
    inference(avatar_component_clause,[],[f11569])).

fof(f11569,plain,
    ( spl5_157
  <=> ! [X2] :
        ( ~ r1_tarski(X2,sK2)
        | r1_tarski(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_157])])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f40,f44])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f11152,plain,
    ( ~ r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)),sK1)
    | spl5_146 ),
    inference(avatar_component_clause,[],[f11150])).

fof(f11150,plain,
    ( spl5_146
  <=> r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_146])])).

fof(f11571,plain,
    ( spl5_157
    | ~ spl5_150 ),
    inference(avatar_split_clause,[],[f11480,f11448,f11569])).

fof(f11448,plain,
    ( spl5_150
  <=> sK2 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_150])])).

fof(f11480,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK2)
        | r1_tarski(X2,sK1) )
    | ~ spl5_150 ),
    inference(superposition,[],[f52,f11450])).

fof(f11450,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ spl5_150 ),
    inference(avatar_component_clause,[],[f11448])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f11451,plain,
    ( spl5_150
    | ~ spl5_149 ),
    inference(avatar_split_clause,[],[f11409,f11331,f11448])).

fof(f11331,plain,
    ( spl5_149
  <=> k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_149])])).

fof(f11409,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ spl5_149 ),
    inference(forward_demodulation,[],[f11356,f38])).

fof(f38,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f11356,plain,
    ( k5_xboole_0(sK2,k1_xboole_0) = k3_xboole_0(sK1,sK2)
    | ~ spl5_149 ),
    inference(superposition,[],[f1233,f11333])).

fof(f11333,plain,
    ( k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))
    | ~ spl5_149 ),
    inference(avatar_component_clause,[],[f11331])).

fof(f1233,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f1205,f74])).

fof(f74,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f41,f38])).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f1205,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f51,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f51,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f11334,plain,
    ( spl5_149
    | ~ spl5_122 ),
    inference(avatar_split_clause,[],[f11296,f10490,f11331])).

fof(f10490,plain,
    ( spl5_122
  <=> sK1 = k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_122])])).

fof(f11296,plain,
    ( k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))
    | ~ spl5_122 ),
    inference(forward_demodulation,[],[f11295,f1233])).

fof(f11295,plain,
    ( k1_xboole_0 = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))
    | ~ spl5_122 ),
    inference(forward_demodulation,[],[f11252,f41])).

fof(f11252,plain,
    ( k1_xboole_0 = k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1))
    | ~ spl5_122 ),
    inference(superposition,[],[f1211,f10492])).

fof(f10492,plain,
    ( sK1 = k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl5_122 ),
    inference(avatar_component_clause,[],[f10490])).

fof(f1211,plain,(
    ! [X4,X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    inference(superposition,[],[f51,f37])).

fof(f11153,plain,
    ( ~ spl5_146
    | spl5_3
    | ~ spl5_143 ),
    inference(avatar_split_clause,[],[f11081,f11044,f70,f11150])).

fof(f70,plain,
    ( spl5_3
  <=> r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f11044,plain,
    ( spl5_143
  <=> ! [X0] : r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_143])])).

fof(f11081,plain,
    ( ~ r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)),sK1)
    | spl5_3
    | ~ spl5_143 ),
    inference(unit_resulting_resolution,[],[f72,f11045,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)
      | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X2)
      | r1_tarski(k5_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f53,f44,f44])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,X1),X2)
      | ~ r1_tarski(k4_xboole_0(X1,X0),X2)
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X1),X2)
      | ~ r1_tarski(k4_xboole_0(X1,X0),X2)
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X1),X2)
      | ~ r1_tarski(k4_xboole_0(X1,X0),X2)
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k4_xboole_0(X1,X0),X2)
        & r1_tarski(k4_xboole_0(X0,X1),X2) )
     => r1_tarski(k5_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_xboole_1)).

fof(f11045,plain,
    ( ! [X0] : r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),sK1)
    | ~ spl5_143 ),
    inference(avatar_component_clause,[],[f11044])).

fof(f72,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f11046,plain,
    ( spl5_143
    | ~ spl5_138 ),
    inference(avatar_split_clause,[],[f10988,f10984,f11044])).

fof(f10984,plain,
    ( spl5_138
  <=> ! [X2] :
        ( ~ r1_tarski(X2,sK0)
        | r1_tarski(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_138])])).

fof(f10988,plain,
    ( ! [X0] : r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),sK1)
    | ~ spl5_138 ),
    inference(unit_resulting_resolution,[],[f55,f10985])).

fof(f10985,plain,
    ( ! [X2] :
        ( r1_tarski(X2,sK1)
        | ~ r1_tarski(X2,sK0) )
    | ~ spl5_138 ),
    inference(avatar_component_clause,[],[f10984])).

fof(f10986,plain,
    ( spl5_138
    | ~ spl5_125 ),
    inference(avatar_split_clause,[],[f10735,f10702,f10984])).

fof(f10702,plain,
    ( spl5_125
  <=> sK0 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_125])])).

fof(f10735,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK0)
        | r1_tarski(X2,sK1) )
    | ~ spl5_125 ),
    inference(superposition,[],[f52,f10704])).

fof(f10704,plain,
    ( sK0 = k3_xboole_0(sK1,sK0)
    | ~ spl5_125 ),
    inference(avatar_component_clause,[],[f10702])).

fof(f10705,plain,
    ( spl5_125
    | ~ spl5_124 ),
    inference(avatar_split_clause,[],[f10663,f10585,f10702])).

fof(f10585,plain,
    ( spl5_124
  <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_124])])).

fof(f10663,plain,
    ( sK0 = k3_xboole_0(sK1,sK0)
    | ~ spl5_124 ),
    inference(forward_demodulation,[],[f10610,f38])).

fof(f10610,plain,
    ( k5_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK1,sK0)
    | ~ spl5_124 ),
    inference(superposition,[],[f1233,f10587])).

fof(f10587,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK1,sK0))
    | ~ spl5_124 ),
    inference(avatar_component_clause,[],[f10585])).

fof(f10588,plain,
    ( spl5_124
    | ~ spl5_121 ),
    inference(avatar_split_clause,[],[f10550,f10485,f10585])).

fof(f10485,plain,
    ( spl5_121
  <=> sK1 = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_121])])).

fof(f10550,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK1,sK0))
    | ~ spl5_121 ),
    inference(forward_demodulation,[],[f10549,f1233])).

fof(f10549,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))
    | ~ spl5_121 ),
    inference(forward_demodulation,[],[f10506,f41])).

fof(f10506,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)),sK1))
    | ~ spl5_121 ),
    inference(superposition,[],[f1211,f10487])).

fof(f10487,plain,
    ( sK1 = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))
    | ~ spl5_121 ),
    inference(avatar_component_clause,[],[f10485])).

fof(f10493,plain,
    ( spl5_122
    | ~ spl5_6
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f10241,f500,f201,f10490])).

fof(f201,plain,
    ( spl5_6
  <=> sK2 = k3_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f500,plain,
    ( spl5_26
  <=> k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f10241,plain,
    ( sK1 = k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl5_6
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f10240,f38])).

fof(f10240,plain,
    ( k5_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl5_6
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f10239,f502])).

fof(f502,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f500])).

fof(f10239,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f10238,f41])).

fof(f10238,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,k3_xboole_0(sK2,k5_xboole_0(sK2,sK1)))
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f9735,f1404])).

fof(f1404,plain,(
    ! [X10,X11,X9] : k5_xboole_0(X10,X11) = k5_xboole_0(k5_xboole_0(X9,X10),k5_xboole_0(X9,X11)) ),
    inference(superposition,[],[f51,f1266])).

fof(f1266,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7 ),
    inference(superposition,[],[f1239,f1239])).

fof(f1239,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f1233,f41])).

fof(f9735,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK2,sK1))))
    | ~ spl5_6 ),
    inference(superposition,[],[f56,f203])).

fof(f203,plain,
    ( sK2 = k3_xboole_0(sK2,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f201])).

fof(f56,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f45,f54,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f10488,plain,
    ( spl5_121
    | ~ spl5_5
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f10237,f495,f196,f10485])).

fof(f196,plain,
    ( spl5_5
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f495,plain,
    ( spl5_25
  <=> k1_xboole_0 = k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f10237,plain,
    ( sK1 = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))
    | ~ spl5_5
    | ~ spl5_25 ),
    inference(forward_demodulation,[],[f10236,f1233])).

fof(f10236,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))
    | ~ spl5_5
    | ~ spl5_25 ),
    inference(forward_demodulation,[],[f10235,f41])).

fof(f10235,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,sK1),sK0) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))
    | ~ spl5_5
    | ~ spl5_25 ),
    inference(forward_demodulation,[],[f10234,f74])).

fof(f10234,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(sK0,sK1),sK0))
    | ~ spl5_5
    | ~ spl5_25 ),
    inference(forward_demodulation,[],[f10233,f1213])).

fof(f1213,plain,(
    ! [X8,X7,X9] : k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8)) ),
    inference(superposition,[],[f51,f41])).

fof(f10233,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,k1_xboole_0))
    | ~ spl5_5
    | ~ spl5_25 ),
    inference(forward_demodulation,[],[f9734,f497])).

fof(f497,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f495])).

fof(f9734,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)))) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))
    | ~ spl5_5 ),
    inference(superposition,[],[f56,f198])).

fof(f198,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f196])).

fof(f503,plain,
    ( spl5_26
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f492,f487,f500])).

fof(f487,plain,
    ( spl5_24
  <=> ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f492,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))
    | ~ spl5_24 ),
    inference(unit_resulting_resolution,[],[f488,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f488,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f487])).

fof(f498,plain,
    ( spl5_25
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f490,f483,f495])).

fof(f483,plain,
    ( spl5_23
  <=> ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f490,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))
    | ~ spl5_23 ),
    inference(unit_resulting_resolution,[],[f484,f39])).

fof(f484,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f483])).

fof(f489,plain,
    ( spl5_24
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f242,f237,f487])).

fof(f237,plain,
    ( spl5_10
  <=> r1_xboole_0(sK2,k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f242,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f239,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f239,plain,
    ( r1_xboole_0(sK2,k5_xboole_0(sK1,sK2))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f237])).

fof(f485,plain,
    ( spl5_23
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f241,f232,f483])).

fof(f232,plain,
    ( spl5_9
  <=> r1_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f241,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)))
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f234,f47])).

fof(f234,plain,
    ( r1_xboole_0(sK0,k5_xboole_0(sK0,sK1))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f232])).

fof(f240,plain,
    ( spl5_10
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f219,f201,f237])).

fof(f219,plain,
    ( r1_xboole_0(sK2,k5_xboole_0(sK1,sK2))
    | ~ spl5_6 ),
    inference(superposition,[],[f84,f203])).

fof(f84,plain,(
    ! [X2,X3] : r1_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X3,X2)) ),
    inference(superposition,[],[f42,f41])).

fof(f42,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f235,plain,
    ( spl5_9
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f209,f196,f232])).

fof(f209,plain,
    ( r1_xboole_0(sK0,k5_xboole_0(sK0,sK1))
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f206,f41])).

fof(f206,plain,
    ( r1_xboole_0(sK0,k5_xboole_0(sK1,sK0))
    | ~ spl5_5 ),
    inference(superposition,[],[f84,f198])).

fof(f204,plain,
    ( spl5_6
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f186,f65,f201])).

fof(f65,plain,
    ( spl5_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f186,plain,
    ( sK2 = k3_xboole_0(sK2,sK1)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f67,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f67,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f199,plain,
    ( spl5_5
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f185,f60,f196])).

fof(f60,plain,
    ( spl5_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f185,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f62,f48])).

fof(f62,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f73,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f36,f70])).

fof(f36,plain,(
    ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK2,sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
      & r1_tarski(sK2,sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X2,X1)
          & r1_tarski(X0,X1) )
       => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

fof(f68,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f35,f65])).

fof(f35,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f34,f60])).

fof(f34,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:15:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (10790)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.46  % (10784)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (10785)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (10793)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (10783)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (10794)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (10791)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (10798)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (10796)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (10788)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (10782)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (10787)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (10786)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (10792)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.51  % (10789)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.51  % (10797)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (10799)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.52  % (10795)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 4.62/0.98  % (10799)Refutation found. Thanks to Tanya!
% 4.62/0.98  % SZS status Theorem for theBenchmark
% 4.62/0.98  % SZS output start Proof for theBenchmark
% 4.62/0.98  fof(f12241,plain,(
% 4.62/0.98    $false),
% 4.62/0.98    inference(avatar_sat_refutation,[],[f63,f68,f73,f199,f204,f235,f240,f485,f489,f498,f503,f10488,f10493,f10588,f10705,f10986,f11046,f11153,f11334,f11451,f11571,f12240])).
% 4.62/0.98  fof(f12240,plain,(
% 4.62/0.98    spl5_146 | ~spl5_157),
% 4.62/0.98    inference(avatar_contradiction_clause,[],[f12233])).
% 4.62/0.98  fof(f12233,plain,(
% 4.62/0.98    $false | (spl5_146 | ~spl5_157)),
% 4.62/0.98    inference(unit_resulting_resolution,[],[f11152,f55,f11570])).
% 4.62/0.98  fof(f11570,plain,(
% 4.62/0.98    ( ! [X2] : (~r1_tarski(X2,sK2) | r1_tarski(X2,sK1)) ) | ~spl5_157),
% 4.62/0.98    inference(avatar_component_clause,[],[f11569])).
% 4.62/0.98  fof(f11569,plain,(
% 4.62/0.98    spl5_157 <=> ! [X2] : (~r1_tarski(X2,sK2) | r1_tarski(X2,sK1))),
% 4.62/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_157])])).
% 4.62/0.98  fof(f55,plain,(
% 4.62/0.98    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 4.62/0.98    inference(definition_unfolding,[],[f40,f44])).
% 4.62/0.98  fof(f44,plain,(
% 4.62/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.62/0.98    inference(cnf_transformation,[],[f5])).
% 4.62/0.98  fof(f5,axiom,(
% 4.62/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 4.62/0.98  fof(f40,plain,(
% 4.62/0.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 4.62/0.98    inference(cnf_transformation,[],[f9])).
% 4.62/0.98  fof(f9,axiom,(
% 4.62/0.98    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 4.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 4.62/0.98  fof(f11152,plain,(
% 4.62/0.98    ~r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)),sK1) | spl5_146),
% 4.62/0.98    inference(avatar_component_clause,[],[f11150])).
% 4.62/0.98  fof(f11150,plain,(
% 4.62/0.98    spl5_146 <=> r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)),sK1)),
% 4.62/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_146])])).
% 4.62/0.98  fof(f11571,plain,(
% 4.62/0.98    spl5_157 | ~spl5_150),
% 4.62/0.98    inference(avatar_split_clause,[],[f11480,f11448,f11569])).
% 4.62/0.98  fof(f11448,plain,(
% 4.62/0.98    spl5_150 <=> sK2 = k3_xboole_0(sK1,sK2)),
% 4.62/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_150])])).
% 4.62/0.98  fof(f11480,plain,(
% 4.62/0.98    ( ! [X2] : (~r1_tarski(X2,sK2) | r1_tarski(X2,sK1)) ) | ~spl5_150),
% 4.62/0.98    inference(superposition,[],[f52,f11450])).
% 4.62/0.98  fof(f11450,plain,(
% 4.62/0.98    sK2 = k3_xboole_0(sK1,sK2) | ~spl5_150),
% 4.62/0.98    inference(avatar_component_clause,[],[f11448])).
% 4.62/0.98  fof(f52,plain,(
% 4.62/0.98    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 4.62/0.98    inference(cnf_transformation,[],[f25])).
% 4.62/0.98  fof(f25,plain,(
% 4.62/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 4.62/0.98    inference(ennf_transformation,[],[f7])).
% 4.62/0.98  fof(f7,axiom,(
% 4.62/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 4.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 4.62/0.98  fof(f11451,plain,(
% 4.62/0.98    spl5_150 | ~spl5_149),
% 4.62/0.98    inference(avatar_split_clause,[],[f11409,f11331,f11448])).
% 4.62/0.98  fof(f11331,plain,(
% 4.62/0.98    spl5_149 <=> k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))),
% 4.62/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_149])])).
% 4.62/0.98  fof(f11409,plain,(
% 4.62/0.98    sK2 = k3_xboole_0(sK1,sK2) | ~spl5_149),
% 4.62/0.98    inference(forward_demodulation,[],[f11356,f38])).
% 4.62/0.98  fof(f38,plain,(
% 4.62/0.98    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.62/0.98    inference(cnf_transformation,[],[f11])).
% 4.62/0.98  fof(f11,axiom,(
% 4.62/0.98    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 4.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 4.62/0.98  fof(f11356,plain,(
% 4.62/0.98    k5_xboole_0(sK2,k1_xboole_0) = k3_xboole_0(sK1,sK2) | ~spl5_149),
% 4.62/0.98    inference(superposition,[],[f1233,f11333])).
% 4.62/0.98  fof(f11333,plain,(
% 4.62/0.98    k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)) | ~spl5_149),
% 4.62/0.98    inference(avatar_component_clause,[],[f11331])).
% 4.62/0.98  fof(f1233,plain,(
% 4.62/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 4.62/0.98    inference(forward_demodulation,[],[f1205,f74])).
% 4.62/0.98  fof(f74,plain,(
% 4.62/0.98    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 4.62/0.98    inference(superposition,[],[f41,f38])).
% 4.62/0.98  fof(f41,plain,(
% 4.62/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 4.62/0.98    inference(cnf_transformation,[],[f1])).
% 4.62/0.98  fof(f1,axiom,(
% 4.62/0.98    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 4.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 4.62/0.98  fof(f1205,plain,(
% 4.62/0.98    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 4.62/0.98    inference(superposition,[],[f51,f37])).
% 4.62/0.98  fof(f37,plain,(
% 4.62/0.98    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 4.62/0.98    inference(cnf_transformation,[],[f13])).
% 4.62/0.98  fof(f13,axiom,(
% 4.62/0.98    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 4.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 4.62/0.98  fof(f51,plain,(
% 4.62/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 4.62/0.98    inference(cnf_transformation,[],[f12])).
% 4.62/0.98  fof(f12,axiom,(
% 4.62/0.98    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 4.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 4.62/0.98  fof(f11334,plain,(
% 4.62/0.98    spl5_149 | ~spl5_122),
% 4.62/0.98    inference(avatar_split_clause,[],[f11296,f10490,f11331])).
% 4.62/0.98  fof(f10490,plain,(
% 4.62/0.98    spl5_122 <=> sK1 = k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 4.62/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_122])])).
% 4.62/0.98  fof(f11296,plain,(
% 4.62/0.98    k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)) | ~spl5_122),
% 4.62/0.98    inference(forward_demodulation,[],[f11295,f1233])).
% 4.62/0.98  fof(f11295,plain,(
% 4.62/0.98    k1_xboole_0 = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) | ~spl5_122),
% 4.62/0.98    inference(forward_demodulation,[],[f11252,f41])).
% 4.62/0.98  fof(f11252,plain,(
% 4.62/0.98    k1_xboole_0 = k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)) | ~spl5_122),
% 4.62/0.98    inference(superposition,[],[f1211,f10492])).
% 4.62/0.98  fof(f10492,plain,(
% 4.62/0.98    sK1 = k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl5_122),
% 4.62/0.98    inference(avatar_component_clause,[],[f10490])).
% 4.62/0.98  fof(f1211,plain,(
% 4.62/0.98    ( ! [X4,X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) )),
% 4.62/0.98    inference(superposition,[],[f51,f37])).
% 4.62/0.98  fof(f11153,plain,(
% 4.62/0.98    ~spl5_146 | spl5_3 | ~spl5_143),
% 4.62/0.98    inference(avatar_split_clause,[],[f11081,f11044,f70,f11150])).
% 4.62/0.98  fof(f70,plain,(
% 4.62/0.98    spl5_3 <=> r1_tarski(k5_xboole_0(sK0,sK2),sK1)),
% 4.62/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 4.62/0.98  fof(f11044,plain,(
% 4.62/0.98    spl5_143 <=> ! [X0] : r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),sK1)),
% 4.62/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_143])])).
% 4.62/0.98  fof(f11081,plain,(
% 4.62/0.98    ~r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)),sK1) | (spl5_3 | ~spl5_143)),
% 4.62/0.98    inference(unit_resulting_resolution,[],[f72,f11045,f58])).
% 4.62/0.98  fof(f58,plain,(
% 4.62/0.98    ( ! [X2,X0,X1] : (~r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) | ~r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X2) | r1_tarski(k5_xboole_0(X0,X1),X2)) )),
% 4.62/0.98    inference(definition_unfolding,[],[f53,f44,f44])).
% 4.62/0.98  fof(f53,plain,(
% 4.62/0.98    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,X1),X2) | ~r1_tarski(k4_xboole_0(X1,X0),X2) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 4.62/0.98    inference(cnf_transformation,[],[f27])).
% 4.62/0.98  fof(f27,plain,(
% 4.62/0.98    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X1),X2) | ~r1_tarski(k4_xboole_0(X1,X0),X2) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 4.62/0.98    inference(flattening,[],[f26])).
% 4.62/0.98  fof(f26,plain,(
% 4.62/0.98    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X1),X2) | (~r1_tarski(k4_xboole_0(X1,X0),X2) | ~r1_tarski(k4_xboole_0(X0,X1),X2)))),
% 4.62/0.98    inference(ennf_transformation,[],[f15])).
% 4.62/0.98  fof(f15,axiom,(
% 4.62/0.98    ! [X0,X1,X2] : ((r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2)) => r1_tarski(k5_xboole_0(X0,X1),X2))),
% 4.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_xboole_1)).
% 4.62/0.98  fof(f11045,plain,(
% 4.62/0.98    ( ! [X0] : (r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),sK1)) ) | ~spl5_143),
% 4.62/0.98    inference(avatar_component_clause,[],[f11044])).
% 4.62/0.98  fof(f72,plain,(
% 4.62/0.98    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1) | spl5_3),
% 4.62/0.98    inference(avatar_component_clause,[],[f70])).
% 4.62/0.98  fof(f11046,plain,(
% 4.62/0.98    spl5_143 | ~spl5_138),
% 4.62/0.98    inference(avatar_split_clause,[],[f10988,f10984,f11044])).
% 4.62/0.98  fof(f10984,plain,(
% 4.62/0.98    spl5_138 <=> ! [X2] : (~r1_tarski(X2,sK0) | r1_tarski(X2,sK1))),
% 4.62/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_138])])).
% 4.62/0.98  fof(f10988,plain,(
% 4.62/0.98    ( ! [X0] : (r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),sK1)) ) | ~spl5_138),
% 4.62/0.98    inference(unit_resulting_resolution,[],[f55,f10985])).
% 4.62/0.98  fof(f10985,plain,(
% 4.62/0.98    ( ! [X2] : (r1_tarski(X2,sK1) | ~r1_tarski(X2,sK0)) ) | ~spl5_138),
% 4.62/0.98    inference(avatar_component_clause,[],[f10984])).
% 4.62/0.98  fof(f10986,plain,(
% 4.62/0.98    spl5_138 | ~spl5_125),
% 4.62/0.98    inference(avatar_split_clause,[],[f10735,f10702,f10984])).
% 4.62/0.98  fof(f10702,plain,(
% 4.62/0.98    spl5_125 <=> sK0 = k3_xboole_0(sK1,sK0)),
% 4.62/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_125])])).
% 4.62/0.98  fof(f10735,plain,(
% 4.62/0.98    ( ! [X2] : (~r1_tarski(X2,sK0) | r1_tarski(X2,sK1)) ) | ~spl5_125),
% 4.62/0.98    inference(superposition,[],[f52,f10704])).
% 4.62/0.98  fof(f10704,plain,(
% 4.62/0.98    sK0 = k3_xboole_0(sK1,sK0) | ~spl5_125),
% 4.62/0.98    inference(avatar_component_clause,[],[f10702])).
% 4.62/0.98  fof(f10705,plain,(
% 4.62/0.98    spl5_125 | ~spl5_124),
% 4.62/0.98    inference(avatar_split_clause,[],[f10663,f10585,f10702])).
% 4.62/0.98  fof(f10585,plain,(
% 4.62/0.98    spl5_124 <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK1,sK0))),
% 4.62/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_124])])).
% 4.62/0.98  fof(f10663,plain,(
% 4.62/0.98    sK0 = k3_xboole_0(sK1,sK0) | ~spl5_124),
% 4.62/0.98    inference(forward_demodulation,[],[f10610,f38])).
% 4.62/0.98  fof(f10610,plain,(
% 4.62/0.98    k5_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK1,sK0) | ~spl5_124),
% 4.62/0.98    inference(superposition,[],[f1233,f10587])).
% 4.62/0.98  fof(f10587,plain,(
% 4.62/0.98    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)) | ~spl5_124),
% 4.62/0.98    inference(avatar_component_clause,[],[f10585])).
% 4.62/0.98  fof(f10588,plain,(
% 4.62/0.98    spl5_124 | ~spl5_121),
% 4.62/0.98    inference(avatar_split_clause,[],[f10550,f10485,f10585])).
% 4.62/0.98  fof(f10485,plain,(
% 4.62/0.98    spl5_121 <=> sK1 = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),
% 4.62/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_121])])).
% 4.62/0.98  fof(f10550,plain,(
% 4.62/0.98    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)) | ~spl5_121),
% 4.62/0.98    inference(forward_demodulation,[],[f10549,f1233])).
% 4.62/0.98  fof(f10549,plain,(
% 4.62/0.98    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))) | ~spl5_121),
% 4.62/0.98    inference(forward_demodulation,[],[f10506,f41])).
% 4.62/0.98  fof(f10506,plain,(
% 4.62/0.98    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)),sK1)) | ~spl5_121),
% 4.62/0.98    inference(superposition,[],[f1211,f10487])).
% 4.62/0.98  fof(f10487,plain,(
% 4.62/0.98    sK1 = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) | ~spl5_121),
% 4.62/0.98    inference(avatar_component_clause,[],[f10485])).
% 4.62/0.98  fof(f10493,plain,(
% 4.62/0.98    spl5_122 | ~spl5_6 | ~spl5_26),
% 4.62/0.98    inference(avatar_split_clause,[],[f10241,f500,f201,f10490])).
% 4.62/0.98  fof(f201,plain,(
% 4.62/0.98    spl5_6 <=> sK2 = k3_xboole_0(sK2,sK1)),
% 4.62/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 4.62/0.98  fof(f500,plain,(
% 4.62/0.98    spl5_26 <=> k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))),
% 4.62/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 4.62/0.98  fof(f10241,plain,(
% 4.62/0.98    sK1 = k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | (~spl5_6 | ~spl5_26)),
% 4.62/0.98    inference(forward_demodulation,[],[f10240,f38])).
% 4.62/0.98  fof(f10240,plain,(
% 4.62/0.98    k5_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | (~spl5_6 | ~spl5_26)),
% 4.62/0.98    inference(forward_demodulation,[],[f10239,f502])).
% 4.62/0.98  fof(f502,plain,(
% 4.62/0.98    k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) | ~spl5_26),
% 4.62/0.98    inference(avatar_component_clause,[],[f500])).
% 4.62/0.98  fof(f10239,plain,(
% 4.62/0.98    k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl5_6),
% 4.62/0.98    inference(forward_demodulation,[],[f10238,f41])).
% 4.62/0.98  fof(f10238,plain,(
% 4.62/0.98    k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,k3_xboole_0(sK2,k5_xboole_0(sK2,sK1))) | ~spl5_6),
% 4.62/0.98    inference(forward_demodulation,[],[f9735,f1404])).
% 4.62/0.98  fof(f1404,plain,(
% 4.62/0.98    ( ! [X10,X11,X9] : (k5_xboole_0(X10,X11) = k5_xboole_0(k5_xboole_0(X9,X10),k5_xboole_0(X9,X11))) )),
% 4.62/0.98    inference(superposition,[],[f51,f1266])).
% 4.62/0.98  fof(f1266,plain,(
% 4.62/0.98    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7) )),
% 4.62/0.98    inference(superposition,[],[f1239,f1239])).
% 4.62/0.98  fof(f1239,plain,(
% 4.62/0.98    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 4.62/0.98    inference(superposition,[],[f1233,f41])).
% 4.62/0.98  fof(f9735,plain,(
% 4.62/0.98    k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK2,sK1)))) | ~spl5_6),
% 4.62/0.98    inference(superposition,[],[f56,f203])).
% 4.62/0.98  fof(f203,plain,(
% 4.62/0.98    sK2 = k3_xboole_0(sK2,sK1) | ~spl5_6),
% 4.62/0.98    inference(avatar_component_clause,[],[f201])).
% 4.62/0.98  fof(f56,plain,(
% 4.62/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))))) )),
% 4.62/0.98    inference(definition_unfolding,[],[f45,f54,f54])).
% 4.62/0.98  fof(f54,plain,(
% 4.62/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 4.62/0.98    inference(definition_unfolding,[],[f43,f44])).
% 4.62/0.98  fof(f43,plain,(
% 4.62/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.62/0.98    inference(cnf_transformation,[],[f16])).
% 4.62/0.98  fof(f16,axiom,(
% 4.62/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 4.62/0.98  fof(f45,plain,(
% 4.62/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 4.62/0.98    inference(cnf_transformation,[],[f14])).
% 4.62/0.98  fof(f14,axiom,(
% 4.62/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 4.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 4.62/0.98  fof(f10488,plain,(
% 4.62/0.98    spl5_121 | ~spl5_5 | ~spl5_25),
% 4.62/0.98    inference(avatar_split_clause,[],[f10237,f495,f196,f10485])).
% 4.62/0.98  fof(f196,plain,(
% 4.62/0.98    spl5_5 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 4.62/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 4.62/0.98  fof(f495,plain,(
% 4.62/0.98    spl5_25 <=> k1_xboole_0 = k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 4.62/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 4.62/0.98  fof(f10237,plain,(
% 4.62/0.98    sK1 = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) | (~spl5_5 | ~spl5_25)),
% 4.62/0.98    inference(forward_demodulation,[],[f10236,f1233])).
% 4.62/0.98  fof(f10236,plain,(
% 4.62/0.98    k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) | (~spl5_5 | ~spl5_25)),
% 4.62/0.98    inference(forward_demodulation,[],[f10235,f41])).
% 4.62/0.98  fof(f10235,plain,(
% 4.62/0.98    k5_xboole_0(k5_xboole_0(sK0,sK1),sK0) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) | (~spl5_5 | ~spl5_25)),
% 4.62/0.98    inference(forward_demodulation,[],[f10234,f74])).
% 4.62/0.98  fof(f10234,plain,(
% 4.62/0.98    k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(sK0,sK1),sK0)) | (~spl5_5 | ~spl5_25)),
% 4.62/0.98    inference(forward_demodulation,[],[f10233,f1213])).
% 4.62/0.98  fof(f1213,plain,(
% 4.62/0.98    ( ! [X8,X7,X9] : (k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8))) )),
% 4.62/0.98    inference(superposition,[],[f51,f41])).
% 4.62/0.98  fof(f10233,plain,(
% 4.62/0.98    k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,k1_xboole_0)) | (~spl5_5 | ~spl5_25)),
% 4.62/0.98    inference(forward_demodulation,[],[f9734,f497])).
% 4.62/0.98  fof(f497,plain,(
% 4.62/0.98    k1_xboole_0 = k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)) | ~spl5_25),
% 4.62/0.98    inference(avatar_component_clause,[],[f495])).
% 4.62/0.98  fof(f9734,plain,(
% 4.62/0.98    k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)))) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) | ~spl5_5),
% 4.62/0.98    inference(superposition,[],[f56,f198])).
% 4.62/0.98  fof(f198,plain,(
% 4.62/0.98    sK0 = k3_xboole_0(sK0,sK1) | ~spl5_5),
% 4.62/0.98    inference(avatar_component_clause,[],[f196])).
% 4.62/0.98  fof(f503,plain,(
% 4.62/0.98    spl5_26 | ~spl5_24),
% 4.62/0.98    inference(avatar_split_clause,[],[f492,f487,f500])).
% 4.62/0.98  fof(f487,plain,(
% 4.62/0.98    spl5_24 <=> ! [X0] : ~r2_hidden(X0,k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),
% 4.62/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 4.62/0.98  fof(f492,plain,(
% 4.62/0.98    k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) | ~spl5_24),
% 4.62/0.98    inference(unit_resulting_resolution,[],[f488,f39])).
% 4.62/0.98  fof(f39,plain,(
% 4.62/0.98    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 4.62/0.98    inference(cnf_transformation,[],[f31])).
% 4.62/0.98  fof(f31,plain,(
% 4.62/0.98    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 4.62/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f30])).
% 4.62/0.98  fof(f30,plain,(
% 4.62/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 4.62/0.98    introduced(choice_axiom,[])).
% 4.62/0.98  fof(f22,plain,(
% 4.62/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 4.62/0.98    inference(ennf_transformation,[],[f3])).
% 4.62/0.98  fof(f3,axiom,(
% 4.62/0.98    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 4.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 4.62/0.98  fof(f488,plain,(
% 4.62/0.98    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) ) | ~spl5_24),
% 4.62/0.98    inference(avatar_component_clause,[],[f487])).
% 4.62/0.98  fof(f498,plain,(
% 4.62/0.98    spl5_25 | ~spl5_23),
% 4.62/0.98    inference(avatar_split_clause,[],[f490,f483,f495])).
% 4.62/0.98  fof(f483,plain,(
% 4.62/0.98    spl5_23 <=> ! [X0] : ~r2_hidden(X0,k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)))),
% 4.62/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 4.62/0.98  fof(f490,plain,(
% 4.62/0.98    k1_xboole_0 = k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)) | ~spl5_23),
% 4.62/0.98    inference(unit_resulting_resolution,[],[f484,f39])).
% 4.62/0.98  fof(f484,plain,(
% 4.62/0.98    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)))) ) | ~spl5_23),
% 4.62/0.98    inference(avatar_component_clause,[],[f483])).
% 4.62/0.98  fof(f489,plain,(
% 4.62/0.98    spl5_24 | ~spl5_10),
% 4.62/0.98    inference(avatar_split_clause,[],[f242,f237,f487])).
% 4.62/0.98  fof(f237,plain,(
% 4.62/0.98    spl5_10 <=> r1_xboole_0(sK2,k5_xboole_0(sK1,sK2))),
% 4.62/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 4.62/0.98  fof(f242,plain,(
% 4.62/0.98    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) ) | ~spl5_10),
% 4.62/0.98    inference(unit_resulting_resolution,[],[f239,f47])).
% 4.62/0.98  fof(f47,plain,(
% 4.62/0.98    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 4.62/0.98    inference(cnf_transformation,[],[f33])).
% 4.62/0.98  fof(f33,plain,(
% 4.62/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 4.62/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f32])).
% 4.62/0.98  fof(f32,plain,(
% 4.62/0.98    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 4.62/0.98    introduced(choice_axiom,[])).
% 4.62/0.98  fof(f23,plain,(
% 4.62/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 4.62/0.98    inference(ennf_transformation,[],[f19])).
% 4.62/0.98  fof(f19,plain,(
% 4.62/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 4.62/0.98    inference(rectify,[],[f2])).
% 4.62/0.98  fof(f2,axiom,(
% 4.62/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 4.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 4.62/0.98  fof(f239,plain,(
% 4.62/0.98    r1_xboole_0(sK2,k5_xboole_0(sK1,sK2)) | ~spl5_10),
% 4.62/0.98    inference(avatar_component_clause,[],[f237])).
% 4.62/0.98  fof(f485,plain,(
% 4.62/0.98    spl5_23 | ~spl5_9),
% 4.62/0.98    inference(avatar_split_clause,[],[f241,f232,f483])).
% 4.62/0.98  fof(f232,plain,(
% 4.62/0.98    spl5_9 <=> r1_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 4.62/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 4.62/0.98  fof(f241,plain,(
% 4.62/0.98    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)))) ) | ~spl5_9),
% 4.62/0.98    inference(unit_resulting_resolution,[],[f234,f47])).
% 4.62/0.98  fof(f234,plain,(
% 4.62/0.98    r1_xboole_0(sK0,k5_xboole_0(sK0,sK1)) | ~spl5_9),
% 4.62/0.98    inference(avatar_component_clause,[],[f232])).
% 4.62/0.98  fof(f240,plain,(
% 4.62/0.98    spl5_10 | ~spl5_6),
% 4.62/0.98    inference(avatar_split_clause,[],[f219,f201,f237])).
% 4.62/0.98  fof(f219,plain,(
% 4.62/0.98    r1_xboole_0(sK2,k5_xboole_0(sK1,sK2)) | ~spl5_6),
% 4.62/0.98    inference(superposition,[],[f84,f203])).
% 4.62/0.98  fof(f84,plain,(
% 4.62/0.98    ( ! [X2,X3] : (r1_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X3,X2))) )),
% 4.62/0.98    inference(superposition,[],[f42,f41])).
% 4.62/0.98  fof(f42,plain,(
% 4.62/0.98    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 4.62/0.98    inference(cnf_transformation,[],[f4])).
% 4.62/0.98  fof(f4,axiom,(
% 4.62/0.98    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 4.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
% 4.62/0.98  fof(f235,plain,(
% 4.62/0.98    spl5_9 | ~spl5_5),
% 4.62/0.98    inference(avatar_split_clause,[],[f209,f196,f232])).
% 4.62/0.98  fof(f209,plain,(
% 4.62/0.98    r1_xboole_0(sK0,k5_xboole_0(sK0,sK1)) | ~spl5_5),
% 4.62/0.98    inference(forward_demodulation,[],[f206,f41])).
% 4.62/0.98  fof(f206,plain,(
% 4.62/0.98    r1_xboole_0(sK0,k5_xboole_0(sK1,sK0)) | ~spl5_5),
% 4.62/0.98    inference(superposition,[],[f84,f198])).
% 4.62/0.98  fof(f204,plain,(
% 4.62/0.98    spl5_6 | ~spl5_2),
% 4.62/0.98    inference(avatar_split_clause,[],[f186,f65,f201])).
% 4.62/0.98  fof(f65,plain,(
% 4.62/0.98    spl5_2 <=> r1_tarski(sK2,sK1)),
% 4.62/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 4.62/0.98  fof(f186,plain,(
% 4.62/0.98    sK2 = k3_xboole_0(sK2,sK1) | ~spl5_2),
% 4.62/0.98    inference(unit_resulting_resolution,[],[f67,f48])).
% 4.62/0.98  fof(f48,plain,(
% 4.62/0.98    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 4.62/0.98    inference(cnf_transformation,[],[f24])).
% 4.62/0.98  fof(f24,plain,(
% 4.62/0.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 4.62/0.98    inference(ennf_transformation,[],[f8])).
% 4.62/0.98  fof(f8,axiom,(
% 4.62/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 4.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 4.62/0.98  fof(f67,plain,(
% 4.62/0.98    r1_tarski(sK2,sK1) | ~spl5_2),
% 4.62/0.98    inference(avatar_component_clause,[],[f65])).
% 4.62/0.98  fof(f199,plain,(
% 4.62/0.98    spl5_5 | ~spl5_1),
% 4.62/0.98    inference(avatar_split_clause,[],[f185,f60,f196])).
% 4.62/0.98  fof(f60,plain,(
% 4.62/0.98    spl5_1 <=> r1_tarski(sK0,sK1)),
% 4.62/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 4.62/0.98  fof(f185,plain,(
% 4.62/0.98    sK0 = k3_xboole_0(sK0,sK1) | ~spl5_1),
% 4.62/0.98    inference(unit_resulting_resolution,[],[f62,f48])).
% 4.62/0.98  fof(f62,plain,(
% 4.62/0.98    r1_tarski(sK0,sK1) | ~spl5_1),
% 4.62/0.98    inference(avatar_component_clause,[],[f60])).
% 4.62/0.98  fof(f73,plain,(
% 4.62/0.98    ~spl5_3),
% 4.62/0.98    inference(avatar_split_clause,[],[f36,f70])).
% 4.62/0.98  fof(f36,plain,(
% 4.62/0.98    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1)),
% 4.62/0.98    inference(cnf_transformation,[],[f29])).
% 4.62/0.98  fof(f29,plain,(
% 4.62/0.98    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK0,sK1)),
% 4.62/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f28])).
% 4.62/0.98  fof(f28,plain,(
% 4.62/0.98    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => (~r1_tarski(k5_xboole_0(sK0,sK2),sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK0,sK1))),
% 4.62/0.98    introduced(choice_axiom,[])).
% 4.62/0.98  fof(f21,plain,(
% 4.62/0.98    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & r1_tarski(X2,X1) & r1_tarski(X0,X1))),
% 4.62/0.98    inference(flattening,[],[f20])).
% 4.62/0.98  fof(f20,plain,(
% 4.62/0.98    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & (r1_tarski(X2,X1) & r1_tarski(X0,X1)))),
% 4.62/0.98    inference(ennf_transformation,[],[f18])).
% 4.62/0.98  fof(f18,negated_conjecture,(
% 4.62/0.98    ~! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 4.62/0.98    inference(negated_conjecture,[],[f17])).
% 4.62/0.98  fof(f17,conjecture,(
% 4.62/0.98    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 4.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).
% 4.62/0.98  fof(f68,plain,(
% 4.62/0.98    spl5_2),
% 4.62/0.98    inference(avatar_split_clause,[],[f35,f65])).
% 4.62/0.98  fof(f35,plain,(
% 4.62/0.98    r1_tarski(sK2,sK1)),
% 4.62/0.98    inference(cnf_transformation,[],[f29])).
% 4.62/0.98  fof(f63,plain,(
% 4.62/0.98    spl5_1),
% 4.62/0.98    inference(avatar_split_clause,[],[f34,f60])).
% 4.62/0.98  fof(f34,plain,(
% 4.62/0.98    r1_tarski(sK0,sK1)),
% 4.62/0.98    inference(cnf_transformation,[],[f29])).
% 4.62/0.98  % SZS output end Proof for theBenchmark
% 4.62/0.98  % (10799)------------------------------
% 4.62/0.98  % (10799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.62/0.98  % (10799)Termination reason: Refutation
% 4.62/0.98  
% 4.62/0.98  % (10799)Memory used [KB]: 18421
% 4.62/0.98  % (10799)Time elapsed: 0.550 s
% 4.62/0.98  % (10799)------------------------------
% 4.62/0.98  % (10799)------------------------------
% 4.62/0.99  % (10781)Success in time 0.633 s
%------------------------------------------------------------------------------
