%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:27 EST 2020

% Result     : Theorem 27.78s
% Output     : Refutation 27.78s
% Verified   : 
% Statistics : Number of formulae       :  392 ( 973 expanded)
%              Number of leaves         :   86 ( 504 expanded)
%              Depth                    :   10
%              Number of atoms          : 1137 (2306 expanded)
%              Number of equality atoms :  315 ( 896 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f57787,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f38,f45,f51,f55,f59,f63,f79,f87,f103,f119,f145,f169,f173,f267,f284,f311,f336,f340,f344,f432,f462,f488,f531,f535,f539,f716,f782,f786,f790,f794,f883,f1070,f1074,f1078,f1806,f1814,f1818,f1822,f1826,f1834,f1870,f1894,f4156,f4282,f4381,f4473,f4645,f10637,f10963,f17447,f19750,f19754,f19758,f19762,f23694,f23970,f26123,f26408,f27542,f28165,f28786,f28794,f30383,f30387,f30391,f31933,f35175,f43777,f43781,f54055,f54719,f55388,f56017,f56982,f57733])).

fof(f57733,plain,
    ( ~ spl2_27
    | ~ spl2_32
    | spl2_35
    | ~ spl2_131
    | ~ spl2_157
    | ~ spl2_181 ),
    inference(avatar_contradiction_clause,[],[f57732])).

fof(f57732,plain,
    ( $false
    | ~ spl2_27
    | ~ spl2_32
    | spl2_35
    | ~ spl2_131
    | ~ spl2_157
    | ~ spl2_181 ),
    inference(subsumption_resolution,[],[f882,f57731])).

fof(f57731,plain,
    ( ! [X210,X209] : k5_xboole_0(X209,X210) = k4_xboole_0(k5_xboole_0(X209,k4_xboole_0(X210,X209)),k4_xboole_0(X209,k4_xboole_0(X209,X210)))
    | ~ spl2_27
    | ~ spl2_32
    | ~ spl2_131
    | ~ spl2_157
    | ~ spl2_181 ),
    inference(forward_demodulation,[],[f57170,f57525])).

fof(f57525,plain,
    ( ! [X33,X32] : k4_xboole_0(X32,k4_xboole_0(X32,X33)) = k4_xboole_0(X32,k5_xboole_0(X32,X33))
    | ~ spl2_27
    | ~ spl2_32
    | ~ spl2_157
    | ~ spl2_181 ),
    inference(forward_demodulation,[],[f57524,f785])).

fof(f785,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f784])).

fof(f784,plain,
    ( spl2_32
  <=> ! [X5,X4] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f57524,plain,
    ( ! [X33,X32] : k5_xboole_0(X32,k4_xboole_0(X32,X33)) = k4_xboole_0(X32,k5_xboole_0(X32,X33))
    | ~ spl2_27
    | ~ spl2_157
    | ~ spl2_181 ),
    inference(forward_demodulation,[],[f57102,f43780])).

fof(f43780,plain,
    ( ! [X280,X279] : k4_xboole_0(X280,X279) = k4_xboole_0(k5_xboole_0(X280,X279),k4_xboole_0(X279,X280))
    | ~ spl2_157 ),
    inference(avatar_component_clause,[],[f43779])).

fof(f43779,plain,
    ( spl2_157
  <=> ! [X279,X280] : k4_xboole_0(X280,X279) = k4_xboole_0(k5_xboole_0(X280,X279),k4_xboole_0(X279,X280)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_157])])).

fof(f57102,plain,
    ( ! [X33,X32] : k4_xboole_0(X32,k5_xboole_0(X32,X33)) = k5_xboole_0(X32,k4_xboole_0(k5_xboole_0(X32,X33),k4_xboole_0(X33,X32)))
    | ~ spl2_27
    | ~ spl2_181 ),
    inference(superposition,[],[f530,f56981])).

fof(f56981,plain,
    ( ! [X50,X51] : k4_xboole_0(X51,X50) = k4_xboole_0(k5_xboole_0(X50,X51),X50)
    | ~ spl2_181 ),
    inference(avatar_component_clause,[],[f56980])).

fof(f56980,plain,
    ( spl2_181
  <=> ! [X51,X50] : k4_xboole_0(X51,X50) = k4_xboole_0(k5_xboole_0(X50,X51),X50) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_181])])).

fof(f530,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f529])).

fof(f529,plain,
    ( spl2_27
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f57170,plain,
    ( ! [X210,X209] : k5_xboole_0(X209,X210) = k4_xboole_0(k5_xboole_0(X209,k4_xboole_0(X210,X209)),k4_xboole_0(X209,k5_xboole_0(X209,X210)))
    | ~ spl2_131
    | ~ spl2_181 ),
    inference(superposition,[],[f30382,f56981])).

fof(f30382,plain,
    ( ! [X6,X5] : k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),k4_xboole_0(X5,X6)) = X6
    | ~ spl2_131 ),
    inference(avatar_component_clause,[],[f30381])).

fof(f30381,plain,
    ( spl2_131
  <=> ! [X5,X6] : k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),k4_xboole_0(X5,X6)) = X6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_131])])).

fof(f882,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_35 ),
    inference(avatar_component_clause,[],[f880])).

fof(f880,plain,
    ( spl2_35
  <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f56982,plain,
    ( spl2_181
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_65
    | ~ spl2_76
    | ~ spl2_149
    | ~ spl2_179 ),
    inference(avatar_split_clause,[],[f56600,f56015,f35173,f4379,f1868,f57,f32,f56980])).

fof(f32,plain,
    ( spl2_1
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f57,plain,
    ( spl2_6
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f1868,plain,
    ( spl2_65
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).

fof(f4379,plain,
    ( spl2_76
  <=> ! [X13,X14] : k4_xboole_0(X14,X13) = k4_xboole_0(k4_xboole_0(X14,X13),X13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).

fof(f35173,plain,
    ( spl2_149
  <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k5_xboole_0(X3,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_149])])).

fof(f56015,plain,
    ( spl2_179
  <=> ! [X170,X169] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X169,X170),X169),k4_xboole_0(X170,X169)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_179])])).

fof(f56600,plain,
    ( ! [X50,X51] : k4_xboole_0(X51,X50) = k4_xboole_0(k5_xboole_0(X50,X51),X50)
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_65
    | ~ spl2_76
    | ~ spl2_149
    | ~ spl2_179 ),
    inference(forward_demodulation,[],[f56599,f4380])).

fof(f4380,plain,
    ( ! [X14,X13] : k4_xboole_0(X14,X13) = k4_xboole_0(k4_xboole_0(X14,X13),X13)
    | ~ spl2_76 ),
    inference(avatar_component_clause,[],[f4379])).

fof(f56599,plain,
    ( ! [X50,X51] : k4_xboole_0(k5_xboole_0(X50,X51),X50) = k4_xboole_0(k4_xboole_0(X51,X50),X50)
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_65
    | ~ spl2_149
    | ~ spl2_179 ),
    inference(forward_demodulation,[],[f56598,f35983])).

fof(f35983,plain,
    ( ! [X92,X90,X91] : k4_xboole_0(k4_xboole_0(X90,X91),X92) = k4_xboole_0(k4_xboole_0(X90,X91),k4_xboole_0(k4_xboole_0(X90,X91),k4_xboole_0(k5_xboole_0(X91,X90),X92)))
    | ~ spl2_1
    | ~ spl2_65
    | ~ spl2_149 ),
    inference(forward_demodulation,[],[f35800,f33])).

fof(f33,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f35800,plain,
    ( ! [X92,X90,X91] : k4_xboole_0(k4_xboole_0(X90,X91),k4_xboole_0(k4_xboole_0(X90,X91),k4_xboole_0(k5_xboole_0(X91,X90),X92))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X90,X91),k1_xboole_0),X92)
    | ~ spl2_65
    | ~ spl2_149 ),
    inference(superposition,[],[f1869,f35174])).

fof(f35174,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k5_xboole_0(X3,X2))
    | ~ spl2_149 ),
    inference(avatar_component_clause,[],[f35173])).

fof(f1869,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
    | ~ spl2_65 ),
    inference(avatar_component_clause,[],[f1868])).

fof(f56598,plain,
    ( ! [X50,X51] : k4_xboole_0(k5_xboole_0(X50,X51),X50) = k4_xboole_0(k4_xboole_0(X51,X50),k4_xboole_0(k4_xboole_0(X51,X50),k4_xboole_0(k5_xboole_0(X50,X51),X50)))
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_179 ),
    inference(forward_demodulation,[],[f56229,f33])).

fof(f56229,plain,
    ( ! [X50,X51] : k4_xboole_0(k4_xboole_0(X51,X50),k4_xboole_0(k4_xboole_0(X51,X50),k4_xboole_0(k5_xboole_0(X50,X51),X50))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X50,X51),X50),k1_xboole_0)
    | ~ spl2_6
    | ~ spl2_179 ),
    inference(superposition,[],[f58,f56016])).

fof(f56016,plain,
    ( ! [X169,X170] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X169,X170),X169),k4_xboole_0(X170,X169))
    | ~ spl2_179 ),
    inference(avatar_component_clause,[],[f56015])).

fof(f58,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f56017,plain,
    ( spl2_179
    | ~ spl2_156
    | ~ spl2_178 ),
    inference(avatar_split_clause,[],[f55602,f55386,f43775,f56015])).

fof(f43775,plain,
    ( spl2_156
  <=> ! [X86,X87] : k4_xboole_0(X87,X86) = k4_xboole_0(k5_xboole_0(X86,X87),k4_xboole_0(X86,X87)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_156])])).

fof(f55386,plain,
    ( spl2_178
  <=> ! [X25,X24,X26] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X24,X25),k4_xboole_0(X24,k4_xboole_0(X25,X26))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_178])])).

fof(f55602,plain,
    ( ! [X169,X170] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X169,X170),X169),k4_xboole_0(X170,X169))
    | ~ spl2_156
    | ~ spl2_178 ),
    inference(superposition,[],[f55387,f43776])).

fof(f43776,plain,
    ( ! [X87,X86] : k4_xboole_0(X87,X86) = k4_xboole_0(k5_xboole_0(X86,X87),k4_xboole_0(X86,X87))
    | ~ spl2_156 ),
    inference(avatar_component_clause,[],[f43775])).

fof(f55387,plain,
    ( ! [X26,X24,X25] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X24,X25),k4_xboole_0(X24,k4_xboole_0(X25,X26)))
    | ~ spl2_178 ),
    inference(avatar_component_clause,[],[f55386])).

fof(f55388,plain,
    ( spl2_178
    | ~ spl2_81
    | ~ spl2_177 ),
    inference(avatar_split_clause,[],[f54808,f54717,f10635,f55386])).

fof(f10635,plain,
    ( spl2_81
  <=> ! [X20,X22,X21] : k4_xboole_0(X21,X20) = k4_xboole_0(k4_xboole_0(X21,X20),k4_xboole_0(X20,X22)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_81])])).

fof(f54717,plain,
    ( spl2_177
  <=> ! [X3,X2,X4] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(X2,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_177])])).

fof(f54808,plain,
    ( ! [X26,X24,X25] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X24,X25),k4_xboole_0(X24,k4_xboole_0(X25,X26)))
    | ~ spl2_81
    | ~ spl2_177 ),
    inference(superposition,[],[f54718,f10636])).

fof(f10636,plain,
    ( ! [X21,X22,X20] : k4_xboole_0(X21,X20) = k4_xboole_0(k4_xboole_0(X21,X20),k4_xboole_0(X20,X22))
    | ~ spl2_81 ),
    inference(avatar_component_clause,[],[f10635])).

fof(f54718,plain,
    ( ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(X2,X4))
    | ~ spl2_177 ),
    inference(avatar_component_clause,[],[f54717])).

fof(f54719,plain,
    ( spl2_177
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_18
    | ~ spl2_38
    | ~ spl2_117
    | ~ spl2_131
    | ~ spl2_139
    | ~ spl2_176 ),
    inference(avatar_split_clause,[],[f54403,f54053,f31931,f30381,f23968,f1068,f265,f57,f53,f49,f54717])).

fof(f49,plain,
    ( spl2_4
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f53,plain,
    ( spl2_5
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f265,plain,
    ( spl2_18
  <=> ! [X3] : k5_xboole_0(k1_xboole_0,X3) = X3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f1068,plain,
    ( spl2_38
  <=> ! [X3,X5,X4] : k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f23968,plain,
    ( spl2_117
  <=> ! [X120,X122,X121] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X120,X122),k5_xboole_0(X120,k4_xboole_0(X121,X120))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_117])])).

fof(f31931,plain,
    ( spl2_139
  <=> ! [X32,X33] : k5_xboole_0(X32,X33) = k5_xboole_0(k4_xboole_0(X33,X32),k4_xboole_0(X32,X33)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_139])])).

fof(f54053,plain,
    ( spl2_176
  <=> ! [X25,X24,X26] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X24,X26),k4_xboole_0(k5_xboole_0(X24,k4_xboole_0(X25,X24)),X26)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_176])])).

fof(f54403,plain,
    ( ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(X2,X4))
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_18
    | ~ spl2_38
    | ~ spl2_117
    | ~ spl2_131
    | ~ spl2_139
    | ~ spl2_176 ),
    inference(forward_demodulation,[],[f54402,f30382])).

fof(f54402,plain,
    ( ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X2,X3)),k4_xboole_0(X3,X2)),X4))
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_18
    | ~ spl2_38
    | ~ spl2_117
    | ~ spl2_139
    | ~ spl2_176 ),
    inference(forward_demodulation,[],[f54401,f35004])).

fof(f35004,plain,
    ( ! [X85,X86,X84] : k4_xboole_0(k5_xboole_0(X84,k4_xboole_0(X86,X84)),k4_xboole_0(X84,X85)) = k5_xboole_0(X84,k5_xboole_0(k4_xboole_0(X86,X84),k4_xboole_0(X84,X85)))
    | ~ spl2_4
    | ~ spl2_18
    | ~ spl2_117
    | ~ spl2_139 ),
    inference(forward_demodulation,[],[f35003,f266])).

fof(f266,plain,
    ( ! [X3] : k5_xboole_0(k1_xboole_0,X3) = X3
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f265])).

fof(f35003,plain,
    ( ! [X85,X86,X84] : k5_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(X84,k4_xboole_0(X86,X84)),k4_xboole_0(X84,X85))) = k5_xboole_0(X84,k5_xboole_0(k4_xboole_0(X86,X84),k4_xboole_0(X84,X85)))
    | ~ spl2_4
    | ~ spl2_117
    | ~ spl2_139 ),
    inference(forward_demodulation,[],[f34799,f50])).

fof(f50,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f34799,plain,
    ( ! [X85,X86,X84] : k5_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(X84,k4_xboole_0(X86,X84)),k4_xboole_0(X84,X85))) = k5_xboole_0(k5_xboole_0(X84,k4_xboole_0(X86,X84)),k4_xboole_0(X84,X85))
    | ~ spl2_117
    | ~ spl2_139 ),
    inference(superposition,[],[f31932,f23969])).

fof(f23969,plain,
    ( ! [X121,X122,X120] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X120,X122),k5_xboole_0(X120,k4_xboole_0(X121,X120)))
    | ~ spl2_117 ),
    inference(avatar_component_clause,[],[f23968])).

fof(f31932,plain,
    ( ! [X33,X32] : k5_xboole_0(X32,X33) = k5_xboole_0(k4_xboole_0(X33,X32),k4_xboole_0(X32,X33))
    | ~ spl2_139 ),
    inference(avatar_component_clause,[],[f31931])).

fof(f54401,plain,
    ( ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(k5_xboole_0(X3,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))),X4))
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_38
    | ~ spl2_176 ),
    inference(forward_demodulation,[],[f54134,f1190])).

fof(f1190,plain,
    ( ! [X10,X8,X9] : k5_xboole_0(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))) = k5_xboole_0(X8,k5_xboole_0(X10,k4_xboole_0(X8,X9)))
    | ~ spl2_5
    | ~ spl2_38 ),
    inference(superposition,[],[f1069,f54])).

fof(f54,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f1069,plain,
    ( ! [X4,X5,X3] : k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X5)))
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f1068])).

fof(f54134,plain,
    ( ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,k4_xboole_0(X3,X2))),X4))
    | ~ spl2_6
    | ~ spl2_176 ),
    inference(superposition,[],[f54054,f58])).

fof(f54054,plain,
    ( ! [X26,X24,X25] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X24,X26),k4_xboole_0(k5_xboole_0(X24,k4_xboole_0(X25,X24)),X26))
    | ~ spl2_176 ),
    inference(avatar_component_clause,[],[f54053])).

fof(f54055,plain,
    ( spl2_176
    | ~ spl2_26
    | ~ spl2_112 ),
    inference(avatar_split_clause,[],[f30042,f19756,f486,f54053])).

fof(f486,plain,
    ( spl2_26
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f19756,plain,
    ( spl2_112
  <=> ! [X20,X22,X21] : k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(k5_xboole_0(X20,k4_xboole_0(X21,X20)),X22))) = k4_xboole_0(X20,X22) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_112])])).

fof(f30042,plain,
    ( ! [X26,X24,X25] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X24,X26),k4_xboole_0(k5_xboole_0(X24,k4_xboole_0(X25,X24)),X26))
    | ~ spl2_26
    | ~ spl2_112 ),
    inference(superposition,[],[f487,f19757])).

fof(f19757,plain,
    ( ! [X21,X22,X20] : k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(k5_xboole_0(X20,k4_xboole_0(X21,X20)),X22))) = k4_xboole_0(X20,X22)
    | ~ spl2_112 ),
    inference(avatar_component_clause,[],[f19756])).

fof(f487,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f486])).

fof(f43781,plain,
    ( spl2_157
    | ~ spl2_18
    | ~ spl2_111
    | ~ spl2_132
    | ~ spl2_133
    | ~ spl2_139 ),
    inference(avatar_split_clause,[],[f35129,f31931,f30389,f30385,f19752,f265,f43779])).

fof(f19752,plain,
    ( spl2_111
  <=> ! [X20,X19,X21] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X20,X21),k5_xboole_0(k4_xboole_0(X20,X21),k4_xboole_0(X19,X20))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_111])])).

fof(f30385,plain,
    ( spl2_132
  <=> ! [X3,X4] : k4_xboole_0(X3,X4) = k5_xboole_0(k4_xboole_0(X4,X3),k5_xboole_0(X4,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_132])])).

fof(f30389,plain,
    ( spl2_133
  <=> ! [X9,X10] : k4_xboole_0(X9,X10) = k5_xboole_0(k4_xboole_0(X10,X9),k5_xboole_0(X9,X10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_133])])).

fof(f35129,plain,
    ( ! [X280,X279] : k4_xboole_0(X280,X279) = k4_xboole_0(k5_xboole_0(X280,X279),k4_xboole_0(X279,X280))
    | ~ spl2_18
    | ~ spl2_111
    | ~ spl2_132
    | ~ spl2_133
    | ~ spl2_139 ),
    inference(forward_demodulation,[],[f35127,f266])).

fof(f35127,plain,
    ( ! [X280,X279] : k4_xboole_0(k5_xboole_0(X280,X279),k4_xboole_0(X279,X280)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X280,X279))
    | ~ spl2_111
    | ~ spl2_132
    | ~ spl2_133
    | ~ spl2_139 ),
    inference(backward_demodulation,[],[f31647,f34867])).

fof(f34867,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k5_xboole_0(X3,X2))
    | ~ spl2_111
    | ~ spl2_139 ),
    inference(superposition,[],[f19753,f31932])).

fof(f19753,plain,
    ( ! [X21,X19,X20] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X20,X21),k5_xboole_0(k4_xboole_0(X20,X21),k4_xboole_0(X19,X20)))
    | ~ spl2_111 ),
    inference(avatar_component_clause,[],[f19752])).

fof(f31647,plain,
    ( ! [X280,X279] : k4_xboole_0(k5_xboole_0(X280,X279),k4_xboole_0(X279,X280)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X279,X280),k5_xboole_0(X280,X279)),k4_xboole_0(X280,X279))
    | ~ spl2_132
    | ~ spl2_133 ),
    inference(superposition,[],[f30386,f30390])).

fof(f30390,plain,
    ( ! [X10,X9] : k4_xboole_0(X9,X10) = k5_xboole_0(k4_xboole_0(X10,X9),k5_xboole_0(X9,X10))
    | ~ spl2_133 ),
    inference(avatar_component_clause,[],[f30389])).

fof(f30386,plain,
    ( ! [X4,X3] : k4_xboole_0(X3,X4) = k5_xboole_0(k4_xboole_0(X4,X3),k5_xboole_0(X4,X3))
    | ~ spl2_132 ),
    inference(avatar_component_clause,[],[f30385])).

fof(f43777,plain,
    ( spl2_156
    | ~ spl2_18
    | ~ spl2_113
    | ~ spl2_132
    | ~ spl2_139 ),
    inference(avatar_split_clause,[],[f35125,f31931,f30385,f19760,f265,f43775])).

fof(f19760,plain,
    ( spl2_113
  <=> ! [X63,X62,X61] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X61,X62),k5_xboole_0(k4_xboole_0(X62,X63),k4_xboole_0(X61,X62))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_113])])).

fof(f35125,plain,
    ( ! [X87,X86] : k4_xboole_0(X87,X86) = k4_xboole_0(k5_xboole_0(X86,X87),k4_xboole_0(X86,X87))
    | ~ spl2_18
    | ~ spl2_113
    | ~ spl2_132
    | ~ spl2_139 ),
    inference(forward_demodulation,[],[f35124,f266])).

fof(f35124,plain,
    ( ! [X87,X86] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X87,X86)) = k4_xboole_0(k5_xboole_0(X86,X87),k4_xboole_0(X86,X87))
    | ~ spl2_113
    | ~ spl2_132
    | ~ spl2_139 ),
    inference(backward_demodulation,[],[f30997,f34866])).

fof(f34866,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X0),k5_xboole_0(X1,X0))
    | ~ spl2_113
    | ~ spl2_139 ),
    inference(superposition,[],[f19761,f31932])).

fof(f19761,plain,
    ( ! [X61,X62,X63] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X61,X62),k5_xboole_0(k4_xboole_0(X62,X63),k4_xboole_0(X61,X62)))
    | ~ spl2_113 ),
    inference(avatar_component_clause,[],[f19760])).

fof(f30997,plain,
    ( ! [X87,X86] : k4_xboole_0(k5_xboole_0(X86,X87),k4_xboole_0(X86,X87)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X86,X87),k5_xboole_0(X86,X87)),k4_xboole_0(X87,X86))
    | ~ spl2_132 ),
    inference(superposition,[],[f30386,f30386])).

fof(f35175,plain,
    ( spl2_149
    | ~ spl2_111
    | ~ spl2_139 ),
    inference(avatar_split_clause,[],[f34867,f31931,f19752,f35173])).

fof(f31933,plain,
    ( spl2_139
    | ~ spl2_71
    | ~ spl2_127 ),
    inference(avatar_split_clause,[],[f28283,f28163,f1892,f31931])).

fof(f1892,plain,
    ( spl2_71
  <=> ! [X13,X12,X14] : k5_xboole_0(X12,X14) = k5_xboole_0(X13,k5_xboole_0(X13,k5_xboole_0(X14,X12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).

fof(f28163,plain,
    ( spl2_127
  <=> ! [X38,X39] : k5_xboole_0(X39,k5_xboole_0(k4_xboole_0(X39,X38),k4_xboole_0(X38,X39))) = X38 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_127])])).

fof(f28283,plain,
    ( ! [X33,X32] : k5_xboole_0(X32,X33) = k5_xboole_0(k4_xboole_0(X33,X32),k4_xboole_0(X32,X33))
    | ~ spl2_71
    | ~ spl2_127 ),
    inference(superposition,[],[f1893,f28164])).

fof(f28164,plain,
    ( ! [X39,X38] : k5_xboole_0(X39,k5_xboole_0(k4_xboole_0(X39,X38),k4_xboole_0(X38,X39))) = X38
    | ~ spl2_127 ),
    inference(avatar_component_clause,[],[f28163])).

fof(f1893,plain,
    ( ! [X14,X12,X13] : k5_xboole_0(X12,X14) = k5_xboole_0(X13,k5_xboole_0(X13,k5_xboole_0(X14,X12)))
    | ~ spl2_71 ),
    inference(avatar_component_clause,[],[f1892])).

fof(f30391,plain,
    ( spl2_133
    | ~ spl2_51
    | ~ spl2_130 ),
    inference(avatar_split_clause,[],[f29594,f28792,f1812,f30389])).

fof(f1812,plain,
    ( spl2_51
  <=> ! [X1,X3,X2] : k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(k5_xboole_0(X2,X1),X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).

fof(f28792,plain,
    ( spl2_130
  <=> ! [X22,X21] : k4_xboole_0(X22,X21) = k5_xboole_0(k5_xboole_0(X22,k4_xboole_0(X21,X22)),X21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_130])])).

fof(f29594,plain,
    ( ! [X10,X9] : k4_xboole_0(X9,X10) = k5_xboole_0(k4_xboole_0(X10,X9),k5_xboole_0(X9,X10))
    | ~ spl2_51
    | ~ spl2_130 ),
    inference(superposition,[],[f28793,f1813])).

fof(f1813,plain,
    ( ! [X2,X3,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(k5_xboole_0(X2,X1),X3)
    | ~ spl2_51 ),
    inference(avatar_component_clause,[],[f1812])).

fof(f28793,plain,
    ( ! [X21,X22] : k4_xboole_0(X22,X21) = k5_xboole_0(k5_xboole_0(X22,k4_xboole_0(X21,X22)),X21)
    | ~ spl2_130 ),
    inference(avatar_component_clause,[],[f28792])).

fof(f30387,plain,
    ( spl2_132
    | ~ spl2_88
    | ~ spl2_130 ),
    inference(avatar_split_clause,[],[f29591,f28792,f10961,f30385])).

fof(f10961,plain,
    ( spl2_88
  <=> ! [X25,X23,X24] : k5_xboole_0(X25,k5_xboole_0(X24,X23)) = k5_xboole_0(k5_xboole_0(X23,X25),X24) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_88])])).

fof(f29591,plain,
    ( ! [X4,X3] : k4_xboole_0(X3,X4) = k5_xboole_0(k4_xboole_0(X4,X3),k5_xboole_0(X4,X3))
    | ~ spl2_88
    | ~ spl2_130 ),
    inference(superposition,[],[f28793,f10962])).

fof(f10962,plain,
    ( ! [X24,X23,X25] : k5_xboole_0(X25,k5_xboole_0(X24,X23)) = k5_xboole_0(k5_xboole_0(X23,X25),X24)
    | ~ spl2_88 ),
    inference(avatar_component_clause,[],[f10961])).

fof(f30383,plain,
    ( spl2_131
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_121
    | ~ spl2_128 ),
    inference(avatar_split_clause,[],[f29036,f28784,f26406,f57,f32,f30381])).

fof(f26406,plain,
    ( spl2_121
  <=> ! [X84,X85] : k1_xboole_0 = k4_xboole_0(X85,k5_xboole_0(X84,k4_xboole_0(X85,X84))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_121])])).

fof(f28784,plain,
    ( spl2_128
  <=> ! [X55,X56] : k4_xboole_0(X56,X55) = k4_xboole_0(k5_xboole_0(X56,k4_xboole_0(X55,X56)),X55) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_128])])).

fof(f29036,plain,
    ( ! [X6,X5] : k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),k4_xboole_0(X5,X6)) = X6
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_121
    | ~ spl2_128 ),
    inference(forward_demodulation,[],[f29035,f33])).

fof(f29035,plain,
    ( ! [X6,X5] : k4_xboole_0(X6,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),k4_xboole_0(X5,X6))
    | ~ spl2_6
    | ~ spl2_121
    | ~ spl2_128 ),
    inference(forward_demodulation,[],[f28855,f26407])).

fof(f26407,plain,
    ( ! [X85,X84] : k1_xboole_0 = k4_xboole_0(X85,k5_xboole_0(X84,k4_xboole_0(X85,X84)))
    | ~ spl2_121 ),
    inference(avatar_component_clause,[],[f26406])).

fof(f28855,plain,
    ( ! [X6,X5] : k4_xboole_0(X6,k4_xboole_0(X6,k5_xboole_0(X5,k4_xboole_0(X6,X5)))) = k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),k4_xboole_0(X5,X6))
    | ~ spl2_6
    | ~ spl2_128 ),
    inference(superposition,[],[f58,f28785])).

fof(f28785,plain,
    ( ! [X56,X55] : k4_xboole_0(X56,X55) = k4_xboole_0(k5_xboole_0(X56,k4_xboole_0(X55,X56)),X55)
    | ~ spl2_128 ),
    inference(avatar_component_clause,[],[f28784])).

fof(f28794,plain,
    ( spl2_130
    | ~ spl2_1
    | ~ spl2_27
    | ~ spl2_54
    | ~ spl2_56
    | ~ spl2_121
    | ~ spl2_127 ),
    inference(avatar_split_clause,[],[f28627,f28163,f26406,f1832,f1824,f529,f32,f28792])).

fof(f1824,plain,
    ( spl2_54
  <=> ! [X13,X14] : k4_xboole_0(X13,X14) = k5_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X13)),X13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f1832,plain,
    ( spl2_56
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X0,X1)),k5_xboole_0(X2,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).

fof(f28627,plain,
    ( ! [X21,X22] : k4_xboole_0(X22,X21) = k5_xboole_0(k5_xboole_0(X22,k4_xboole_0(X21,X22)),X21)
    | ~ spl2_1
    | ~ spl2_27
    | ~ spl2_54
    | ~ spl2_56
    | ~ spl2_121
    | ~ spl2_127 ),
    inference(backward_demodulation,[],[f26608,f28623])).

fof(f28623,plain,
    ( ! [X56,X55] : k4_xboole_0(X56,X55) = k4_xboole_0(k5_xboole_0(X56,k4_xboole_0(X55,X56)),X55)
    | ~ spl2_1
    | ~ spl2_54
    | ~ spl2_56
    | ~ spl2_121
    | ~ spl2_127 ),
    inference(backward_demodulation,[],[f26627,f28277])).

fof(f28277,plain,
    ( ! [X17,X16] : k4_xboole_0(X16,X17) = k5_xboole_0(X17,k5_xboole_0(X16,k4_xboole_0(X17,X16)))
    | ~ spl2_56
    | ~ spl2_127 ),
    inference(superposition,[],[f1833,f28164])).

fof(f1833,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X0,X1)),k5_xboole_0(X2,X1)) = X0
    | ~ spl2_56 ),
    inference(avatar_component_clause,[],[f1832])).

fof(f26627,plain,
    ( ! [X56,X55] : k4_xboole_0(k5_xboole_0(X56,k4_xboole_0(X55,X56)),X55) = k5_xboole_0(X55,k5_xboole_0(X56,k4_xboole_0(X55,X56)))
    | ~ spl2_1
    | ~ spl2_54
    | ~ spl2_121 ),
    inference(forward_demodulation,[],[f26485,f33])).

fof(f26485,plain,
    ( ! [X56,X55] : k4_xboole_0(k5_xboole_0(X56,k4_xboole_0(X55,X56)),X55) = k5_xboole_0(k4_xboole_0(X55,k1_xboole_0),k5_xboole_0(X56,k4_xboole_0(X55,X56)))
    | ~ spl2_54
    | ~ spl2_121 ),
    inference(superposition,[],[f1825,f26407])).

fof(f1825,plain,
    ( ! [X14,X13] : k4_xboole_0(X13,X14) = k5_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X13)),X13)
    | ~ spl2_54 ),
    inference(avatar_component_clause,[],[f1824])).

fof(f26608,plain,
    ( ! [X21,X22] : k4_xboole_0(k5_xboole_0(X22,k4_xboole_0(X21,X22)),X21) = k5_xboole_0(k5_xboole_0(X22,k4_xboole_0(X21,X22)),X21)
    | ~ spl2_1
    | ~ spl2_27
    | ~ spl2_121 ),
    inference(forward_demodulation,[],[f26472,f33])).

fof(f26472,plain,
    ( ! [X21,X22] : k4_xboole_0(k5_xboole_0(X22,k4_xboole_0(X21,X22)),X21) = k5_xboole_0(k5_xboole_0(X22,k4_xboole_0(X21,X22)),k4_xboole_0(X21,k1_xboole_0))
    | ~ spl2_27
    | ~ spl2_121 ),
    inference(superposition,[],[f530,f26407])).

fof(f28786,plain,
    ( spl2_128
    | ~ spl2_1
    | ~ spl2_54
    | ~ spl2_56
    | ~ spl2_121
    | ~ spl2_127 ),
    inference(avatar_split_clause,[],[f28623,f28163,f26406,f1832,f1824,f32,f28784])).

fof(f28165,plain,
    ( spl2_127
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_27
    | ~ spl2_32
    | ~ spl2_39
    | ~ spl2_40
    | ~ spl2_124 ),
    inference(avatar_split_clause,[],[f28075,f27540,f1076,f1072,f784,f529,f101,f77,f49,f32,f28163])).

fof(f77,plain,
    ( spl2_8
  <=> ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f101,plain,
    ( spl2_10
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f1072,plain,
    ( spl2_39
  <=> ! [X7,X6] : k5_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7)) = X6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f1076,plain,
    ( spl2_40
  <=> ! [X34,X36,X35] : k5_xboole_0(X35,X34) = k5_xboole_0(k5_xboole_0(X36,X34),k5_xboole_0(X36,X35)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f27540,plain,
    ( spl2_124
  <=> ! [X81,X80] : k1_xboole_0 = k4_xboole_0(X80,k5_xboole_0(X81,k5_xboole_0(k4_xboole_0(X81,X80),k4_xboole_0(X80,X81)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_124])])).

fof(f28075,plain,
    ( ! [X39,X38] : k5_xboole_0(X39,k5_xboole_0(k4_xboole_0(X39,X38),k4_xboole_0(X38,X39))) = X38
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_27
    | ~ spl2_32
    | ~ spl2_39
    | ~ spl2_40
    | ~ spl2_124 ),
    inference(forward_demodulation,[],[f28074,f33])).

fof(f28074,plain,
    ( ! [X39,X38] : k4_xboole_0(X38,k1_xboole_0) = k5_xboole_0(X39,k5_xboole_0(k4_xboole_0(X39,X38),k4_xboole_0(X38,X39)))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_27
    | ~ spl2_32
    | ~ spl2_39
    | ~ spl2_40
    | ~ spl2_124 ),
    inference(forward_demodulation,[],[f28073,f102])).

fof(f102,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f101])).

fof(f28073,plain,
    ( ! [X39,X38] : k5_xboole_0(X39,k5_xboole_0(k4_xboole_0(X39,X38),k4_xboole_0(X38,X39))) = k5_xboole_0(k4_xboole_0(X38,k1_xboole_0),k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_27
    | ~ spl2_32
    | ~ spl2_39
    | ~ spl2_40
    | ~ spl2_124 ),
    inference(forward_demodulation,[],[f27674,f28061])).

fof(f28061,plain,
    ( ! [X19,X18] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X19,k5_xboole_0(k4_xboole_0(X19,X18),k4_xboole_0(X18,X19))),X18)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_27
    | ~ spl2_32
    | ~ spl2_39
    | ~ spl2_40
    | ~ spl2_124 ),
    inference(forward_demodulation,[],[f28060,f78])).

fof(f78,plain,
    ( ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f28060,plain,
    ( ! [X19,X18] : k4_xboole_0(k5_xboole_0(X19,k5_xboole_0(k4_xboole_0(X19,X18),k4_xboole_0(X18,X19))),X18) = k5_xboole_0(k4_xboole_0(X18,X19),k4_xboole_0(X18,X19))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_27
    | ~ spl2_32
    | ~ spl2_39
    | ~ spl2_40
    | ~ spl2_124 ),
    inference(forward_demodulation,[],[f28059,f1447])).

fof(f1447,plain,
    ( ! [X39,X41,X40] : k5_xboole_0(k4_xboole_0(X40,X39),X41) = k5_xboole_0(k5_xboole_0(X39,k5_xboole_0(k4_xboole_0(X39,X40),X41)),X40)
    | ~ spl2_4
    | ~ spl2_32
    | ~ spl2_39
    | ~ spl2_40 ),
    inference(forward_demodulation,[],[f1394,f907])).

fof(f907,plain,
    ( ! [X8,X7,X9] : k5_xboole_0(X7,k5_xboole_0(k4_xboole_0(X7,X8),X9)) = k5_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),X9)
    | ~ spl2_4
    | ~ spl2_32 ),
    inference(superposition,[],[f50,f785])).

fof(f1394,plain,
    ( ! [X39,X41,X40] : k5_xboole_0(k4_xboole_0(X40,X39),X41) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X39,k4_xboole_0(X39,X40)),X41),X40)
    | ~ spl2_39
    | ~ spl2_40 ),
    inference(superposition,[],[f1077,f1073])).

fof(f1073,plain,
    ( ! [X6,X7] : k5_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7)) = X6
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f1072])).

fof(f1077,plain,
    ( ! [X35,X36,X34] : k5_xboole_0(X35,X34) = k5_xboole_0(k5_xboole_0(X36,X34),k5_xboole_0(X36,X35))
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f1076])).

fof(f28059,plain,
    ( ! [X19,X18] : k4_xboole_0(k5_xboole_0(X19,k5_xboole_0(k4_xboole_0(X19,X18),k4_xboole_0(X18,X19))),X18) = k5_xboole_0(k5_xboole_0(X19,k5_xboole_0(k4_xboole_0(X19,X18),k4_xboole_0(X18,X19))),X18)
    | ~ spl2_1
    | ~ spl2_27
    | ~ spl2_124 ),
    inference(forward_demodulation,[],[f27666,f33])).

fof(f27666,plain,
    ( ! [X19,X18] : k4_xboole_0(k5_xboole_0(X19,k5_xboole_0(k4_xboole_0(X19,X18),k4_xboole_0(X18,X19))),X18) = k5_xboole_0(k5_xboole_0(X19,k5_xboole_0(k4_xboole_0(X19,X18),k4_xboole_0(X18,X19))),k4_xboole_0(X18,k1_xboole_0))
    | ~ spl2_27
    | ~ spl2_124 ),
    inference(superposition,[],[f530,f27541])).

fof(f27541,plain,
    ( ! [X80,X81] : k1_xboole_0 = k4_xboole_0(X80,k5_xboole_0(X81,k5_xboole_0(k4_xboole_0(X81,X80),k4_xboole_0(X80,X81))))
    | ~ spl2_124 ),
    inference(avatar_component_clause,[],[f27540])).

fof(f27674,plain,
    ( ! [X39,X38] : k5_xboole_0(X39,k5_xboole_0(k4_xboole_0(X39,X38),k4_xboole_0(X38,X39))) = k5_xboole_0(k4_xboole_0(X38,k1_xboole_0),k4_xboole_0(k5_xboole_0(X39,k5_xboole_0(k4_xboole_0(X39,X38),k4_xboole_0(X38,X39))),X38))
    | ~ spl2_39
    | ~ spl2_124 ),
    inference(superposition,[],[f1073,f27541])).

fof(f27542,plain,
    ( spl2_124
    | ~ spl2_4
    | ~ spl2_28
    | ~ spl2_32
    | ~ spl2_52
    | ~ spl2_120 ),
    inference(avatar_split_clause,[],[f26319,f26121,f1816,f784,f533,f49,f27540])).

fof(f533,plain,
    ( spl2_28
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f1816,plain,
    ( spl2_52
  <=> ! [X9,X8] : k5_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,k4_xboole_0(X9,X8))) = X8 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).

fof(f26121,plain,
    ( spl2_120
  <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X3,X2),X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_120])])).

fof(f26319,plain,
    ( ! [X80,X81] : k1_xboole_0 = k4_xboole_0(X80,k5_xboole_0(X81,k5_xboole_0(k4_xboole_0(X81,X80),k4_xboole_0(X80,X81))))
    | ~ spl2_4
    | ~ spl2_28
    | ~ spl2_32
    | ~ spl2_52
    | ~ spl2_120 ),
    inference(forward_demodulation,[],[f26318,f534])).

fof(f534,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f533])).

fof(f26318,plain,
    ( ! [X80,X81] : k1_xboole_0 = k4_xboole_0(X80,k5_xboole_0(X81,k5_xboole_0(k4_xboole_0(X81,X80),k4_xboole_0(X80,k4_xboole_0(X81,k4_xboole_0(X81,X80))))))
    | ~ spl2_4
    | ~ spl2_32
    | ~ spl2_52
    | ~ spl2_120 ),
    inference(forward_demodulation,[],[f26158,f907])).

fof(f26158,plain,
    ( ! [X80,X81] : k1_xboole_0 = k4_xboole_0(X80,k5_xboole_0(k4_xboole_0(X81,k4_xboole_0(X81,X80)),k4_xboole_0(X80,k4_xboole_0(X81,k4_xboole_0(X81,X80)))))
    | ~ spl2_52
    | ~ spl2_120 ),
    inference(superposition,[],[f26122,f1817])).

fof(f1817,plain,
    ( ! [X8,X9] : k5_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,k4_xboole_0(X9,X8))) = X8
    | ~ spl2_52 ),
    inference(avatar_component_clause,[],[f1816])).

fof(f26122,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X3,X2),X2)))
    | ~ spl2_120 ),
    inference(avatar_component_clause,[],[f26121])).

fof(f26408,plain,
    ( spl2_121
    | ~ spl2_22
    | ~ spl2_120 ),
    inference(avatar_split_clause,[],[f26160,f26121,f338,f26406])).

fof(f338,plain,
    ( spl2_22
  <=> ! [X9,X8] : k5_xboole_0(k5_xboole_0(X9,X8),X9) = X8 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f26160,plain,
    ( ! [X85,X84] : k1_xboole_0 = k4_xboole_0(X85,k5_xboole_0(X84,k4_xboole_0(X85,X84)))
    | ~ spl2_22
    | ~ spl2_120 ),
    inference(superposition,[],[f26122,f339])).

fof(f339,plain,
    ( ! [X8,X9] : k5_xboole_0(k5_xboole_0(X9,X8),X9) = X8
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f338])).

fof(f26123,plain,
    ( spl2_120
    | ~ spl2_23
    | ~ spl2_32
    | ~ spl2_38
    | ~ spl2_53
    | ~ spl2_97 ),
    inference(avatar_split_clause,[],[f26016,f17445,f1820,f1068,f784,f342,f26121])).

fof(f342,plain,
    ( spl2_23
  <=> ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f1820,plain,
    ( spl2_53
  <=> ! [X11,X10] : k4_xboole_0(X11,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,X11),X10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).

fof(f17445,plain,
    ( spl2_97
  <=> ! [X1,X0,X2] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,k5_xboole_0(X0,X1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_97])])).

fof(f26016,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X3,X2),X2)))
    | ~ spl2_23
    | ~ spl2_32
    | ~ spl2_38
    | ~ spl2_53
    | ~ spl2_97 ),
    inference(forward_demodulation,[],[f26015,f343])).

fof(f343,plain,
    ( ! [X2,X1] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f342])).

fof(f26015,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(k4_xboole_0(k5_xboole_0(X3,X2),X2),X2))
    | ~ spl2_32
    | ~ spl2_38
    | ~ spl2_53
    | ~ spl2_97 ),
    inference(forward_demodulation,[],[f25730,f3435])).

fof(f3435,plain,
    ( ! [X80,X81,X79] : k5_xboole_0(k4_xboole_0(k5_xboole_0(X79,X80),X81),X80) = k5_xboole_0(X79,k4_xboole_0(X81,k4_xboole_0(X81,k5_xboole_0(X79,X80))))
    | ~ spl2_38
    | ~ spl2_53 ),
    inference(superposition,[],[f1069,f1821])).

fof(f1821,plain,
    ( ! [X10,X11] : k4_xboole_0(X11,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,X11),X10)
    | ~ spl2_53 ),
    inference(avatar_component_clause,[],[f1820])).

fof(f25730,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X3,X2)))))
    | ~ spl2_32
    | ~ spl2_97 ),
    inference(superposition,[],[f17446,f785])).

fof(f17446,plain,
    ( ! [X2,X0,X1] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,k5_xboole_0(X0,X1)))))
    | ~ spl2_97 ),
    inference(avatar_component_clause,[],[f17445])).

fof(f23970,plain,
    ( spl2_117
    | ~ spl2_34
    | ~ spl2_116 ),
    inference(avatar_split_clause,[],[f23730,f23692,f792,f23968])).

fof(f792,plain,
    ( spl2_34
  <=> ! [X5,X4] : k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,X4)) = X4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f23692,plain,
    ( spl2_116
  <=> ! [X11,X10,X12] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),X10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_116])])).

fof(f23730,plain,
    ( ! [X121,X122,X120] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X120,X122),k5_xboole_0(X120,k4_xboole_0(X121,X120)))
    | ~ spl2_34
    | ~ spl2_116 ),
    inference(superposition,[],[f23693,f793])).

fof(f793,plain,
    ( ! [X4,X5] : k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,X4)) = X4
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f792])).

fof(f23693,plain,
    ( ! [X12,X10,X11] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),X10)
    | ~ spl2_116 ),
    inference(avatar_component_clause,[],[f23692])).

fof(f23694,plain,
    ( spl2_116
    | ~ spl2_25
    | ~ spl2_110 ),
    inference(avatar_split_clause,[],[f23366,f19748,f460,f23692])).

fof(f460,plain,
    ( spl2_25
  <=> ! [X1,X2] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f19748,plain,
    ( spl2_110
  <=> ! [X53,X55,X52,X54] : k4_xboole_0(X52,X53) = k4_xboole_0(k4_xboole_0(X52,X53),k4_xboole_0(k4_xboole_0(X53,X54),X55)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_110])])).

fof(f23366,plain,
    ( ! [X12,X10,X11] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),X10)
    | ~ spl2_25
    | ~ spl2_110 ),
    inference(superposition,[],[f19749,f461])).

fof(f461,plain,
    ( ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1)
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f460])).

fof(f19749,plain,
    ( ! [X54,X52,X55,X53] : k4_xboole_0(X52,X53) = k4_xboole_0(k4_xboole_0(X52,X53),k4_xboole_0(k4_xboole_0(X53,X54),X55))
    | ~ spl2_110 ),
    inference(avatar_component_clause,[],[f19748])).

fof(f19762,plain,
    ( spl2_113
    | ~ spl2_33
    | ~ spl2_81 ),
    inference(avatar_split_clause,[],[f10710,f10635,f788,f19760])).

fof(f788,plain,
    ( spl2_33
  <=> ! [X13,X12] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X13,X12),k5_xboole_0(X12,k4_xboole_0(X13,X12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f10710,plain,
    ( ! [X61,X62,X63] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X61,X62),k5_xboole_0(k4_xboole_0(X62,X63),k4_xboole_0(X61,X62)))
    | ~ spl2_33
    | ~ spl2_81 ),
    inference(superposition,[],[f789,f10636])).

fof(f789,plain,
    ( ! [X12,X13] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X13,X12),k5_xboole_0(X12,k4_xboole_0(X13,X12)))
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f788])).

fof(f19758,plain,
    ( spl2_112
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_65 ),
    inference(avatar_split_clause,[],[f4074,f1868,f36,f32,f19756])).

fof(f36,plain,
    ( spl2_2
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f4074,plain,
    ( ! [X21,X22,X20] : k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(k5_xboole_0(X20,k4_xboole_0(X21,X20)),X22))) = k4_xboole_0(X20,X22)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_65 ),
    inference(forward_demodulation,[],[f3983,f33])).

fof(f3983,plain,
    ( ! [X21,X22,X20] : k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(k5_xboole_0(X20,k4_xboole_0(X21,X20)),X22))) = k4_xboole_0(k4_xboole_0(X20,k1_xboole_0),X22)
    | ~ spl2_2
    | ~ spl2_65 ),
    inference(superposition,[],[f1869,f37])).

fof(f37,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f19754,plain,
    ( spl2_111
    | ~ spl2_2
    | ~ spl2_81 ),
    inference(avatar_split_clause,[],[f10696,f10635,f36,f19752])).

fof(f10696,plain,
    ( ! [X21,X19,X20] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X20,X21),k5_xboole_0(k4_xboole_0(X20,X21),k4_xboole_0(X19,X20)))
    | ~ spl2_2
    | ~ spl2_81 ),
    inference(superposition,[],[f37,f10636])).

fof(f19750,plain,
    ( spl2_110
    | ~ spl2_81 ),
    inference(avatar_split_clause,[],[f10659,f10635,f19748])).

fof(f10659,plain,
    ( ! [X54,X52,X55,X53] : k4_xboole_0(X52,X53) = k4_xboole_0(k4_xboole_0(X52,X53),k4_xboole_0(k4_xboole_0(X53,X54),X55))
    | ~ spl2_81 ),
    inference(superposition,[],[f10636,f10636])).

fof(f17447,plain,
    ( spl2_97
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f65,f49,f36,f17445])).

fof(f65,plain,
    ( ! [X2,X0,X1] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,k5_xboole_0(X0,X1)))))
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(superposition,[],[f37,f50])).

fof(f10963,plain,
    ( spl2_88
    | ~ spl2_20
    | ~ spl2_49 ),
    inference(avatar_split_clause,[],[f2555,f1804,f309,f10961])).

fof(f309,plain,
    ( spl2_20
  <=> ! [X7,X6] : k5_xboole_0(X7,k5_xboole_0(X6,X7)) = X6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f1804,plain,
    ( spl2_49
  <=> ! [X9,X11,X10] : k5_xboole_0(X10,X11) = k5_xboole_0(k5_xboole_0(X9,X10),k5_xboole_0(X9,X11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).

fof(f2555,plain,
    ( ! [X24,X23,X25] : k5_xboole_0(X25,k5_xboole_0(X24,X23)) = k5_xboole_0(k5_xboole_0(X23,X25),X24)
    | ~ spl2_20
    | ~ spl2_49 ),
    inference(superposition,[],[f1805,f310])).

fof(f310,plain,
    ( ! [X6,X7] : k5_xboole_0(X7,k5_xboole_0(X6,X7)) = X6
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f309])).

fof(f1805,plain,
    ( ! [X10,X11,X9] : k5_xboole_0(X10,X11) = k5_xboole_0(k5_xboole_0(X9,X10),k5_xboole_0(X9,X11))
    | ~ spl2_49 ),
    inference(avatar_component_clause,[],[f1804])).

fof(f10637,plain,
    ( spl2_81
    | ~ spl2_75
    | ~ spl2_78 ),
    inference(avatar_split_clause,[],[f4653,f4643,f4280,f10635])).

fof(f4280,plain,
    ( spl2_75
  <=> ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_75])])).

fof(f4643,plain,
    ( spl2_78
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).

fof(f4653,plain,
    ( ! [X21,X22,X20] : k4_xboole_0(X21,X20) = k4_xboole_0(k4_xboole_0(X21,X20),k4_xboole_0(X20,X22))
    | ~ spl2_75
    | ~ spl2_78 ),
    inference(superposition,[],[f4644,f4281])).

fof(f4281,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1
    | ~ spl2_75 ),
    inference(avatar_component_clause,[],[f4280])).

fof(f4644,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = X0
    | ~ spl2_78 ),
    inference(avatar_component_clause,[],[f4643])).

fof(f4645,plain,
    ( spl2_78
    | ~ spl2_5
    | ~ spl2_10
    | ~ spl2_77 ),
    inference(avatar_split_clause,[],[f4596,f4471,f101,f53,f4643])).

fof(f4471,plain,
    ( spl2_77
  <=> ! [X32,X31,X33] : k1_xboole_0 = k4_xboole_0(X31,k4_xboole_0(X31,k4_xboole_0(k4_xboole_0(X32,X31),X33))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).

fof(f4596,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = X0
    | ~ spl2_5
    | ~ spl2_10
    | ~ spl2_77 ),
    inference(forward_demodulation,[],[f4516,f102])).

fof(f4516,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2))
    | ~ spl2_5
    | ~ spl2_77 ),
    inference(superposition,[],[f54,f4472])).

fof(f4472,plain,
    ( ! [X33,X31,X32] : k1_xboole_0 = k4_xboole_0(X31,k4_xboole_0(X31,k4_xboole_0(k4_xboole_0(X32,X31),X33)))
    | ~ spl2_77 ),
    inference(avatar_component_clause,[],[f4471])).

fof(f4473,plain,
    ( spl2_77
    | ~ spl2_13
    | ~ spl2_65
    | ~ spl2_74 ),
    inference(avatar_split_clause,[],[f4243,f4154,f1868,f143,f4471])).

fof(f143,plain,
    ( spl2_13
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f4154,plain,
    ( spl2_74
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_74])])).

fof(f4243,plain,
    ( ! [X33,X31,X32] : k1_xboole_0 = k4_xboole_0(X31,k4_xboole_0(X31,k4_xboole_0(k4_xboole_0(X32,X31),X33)))
    | ~ spl2_13
    | ~ spl2_65
    | ~ spl2_74 ),
    inference(forward_demodulation,[],[f4192,f144])).

fof(f144,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f143])).

fof(f4192,plain,
    ( ! [X33,X31,X32] : k4_xboole_0(k1_xboole_0,X33) = k4_xboole_0(X31,k4_xboole_0(X31,k4_xboole_0(k4_xboole_0(X32,X31),X33)))
    | ~ spl2_65
    | ~ spl2_74 ),
    inference(superposition,[],[f1869,f4155])).

fof(f4155,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))
    | ~ spl2_74 ),
    inference(avatar_component_clause,[],[f4154])).

fof(f4381,plain,
    ( spl2_76
    | ~ spl2_10
    | ~ spl2_27
    | ~ spl2_74 ),
    inference(avatar_split_clause,[],[f4235,f4154,f529,f101,f4379])).

fof(f4235,plain,
    ( ! [X14,X13] : k4_xboole_0(X14,X13) = k4_xboole_0(k4_xboole_0(X14,X13),X13)
    | ~ spl2_10
    | ~ spl2_27
    | ~ spl2_74 ),
    inference(forward_demodulation,[],[f4185,f102])).

fof(f4185,plain,
    ( ! [X14,X13] : k4_xboole_0(k4_xboole_0(X14,X13),X13) = k5_xboole_0(k4_xboole_0(X14,X13),k1_xboole_0)
    | ~ spl2_27
    | ~ spl2_74 ),
    inference(superposition,[],[f530,f4155])).

fof(f4282,plain,
    ( spl2_75
    | ~ spl2_5
    | ~ spl2_10
    | ~ spl2_74 ),
    inference(avatar_split_clause,[],[f4231,f4154,f101,f53,f4280])).

fof(f4231,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1
    | ~ spl2_5
    | ~ spl2_10
    | ~ spl2_74 ),
    inference(forward_demodulation,[],[f4181,f102])).

fof(f4181,plain,
    ( ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ spl2_5
    | ~ spl2_74 ),
    inference(superposition,[],[f54,f4155])).

fof(f4156,plain,
    ( spl2_74
    | ~ spl2_24
    | ~ spl2_65 ),
    inference(avatar_split_clause,[],[f4001,f1868,f430,f4154])).

fof(f430,plain,
    ( spl2_24
  <=> ! [X13,X12] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X13)),X12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f4001,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))
    | ~ spl2_24
    | ~ spl2_65 ),
    inference(superposition,[],[f1869,f431])).

fof(f431,plain,
    ( ! [X12,X13] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X13)),X12)
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f430])).

fof(f1894,plain,
    ( spl2_71
    | ~ spl2_4
    | ~ spl2_23
    | ~ spl2_38 ),
    inference(avatar_split_clause,[],[f1236,f1068,f342,f49,f1892])).

fof(f1236,plain,
    ( ! [X14,X12,X13] : k5_xboole_0(X12,X14) = k5_xboole_0(X13,k5_xboole_0(X13,k5_xboole_0(X14,X12)))
    | ~ spl2_4
    | ~ spl2_23
    | ~ spl2_38 ),
    inference(forward_demodulation,[],[f1209,f50])).

fof(f1209,plain,
    ( ! [X14,X12,X13] : k5_xboole_0(X12,X14) = k5_xboole_0(X13,k5_xboole_0(k5_xboole_0(X13,X14),X12))
    | ~ spl2_23
    | ~ spl2_38 ),
    inference(superposition,[],[f1069,f343])).

fof(f1870,plain,(
    spl2_65 ),
    inference(avatar_split_clause,[],[f30,f1868])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f24,f20,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f1834,plain,
    ( spl2_56
    | ~ spl2_22
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f809,f780,f338,f1832])).

fof(f780,plain,
    ( spl2_31
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f809,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X0,X1)),k5_xboole_0(X2,X1)) = X0
    | ~ spl2_22
    | ~ spl2_31 ),
    inference(superposition,[],[f781,f339])).

fof(f781,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f780])).

fof(f1826,plain,
    ( spl2_54
    | ~ spl2_22
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f670,f537,f338,f1824])).

fof(f537,plain,
    ( spl2_29
  <=> ! [X3,X2] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f670,plain,
    ( ! [X14,X13] : k4_xboole_0(X13,X14) = k5_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X13)),X13)
    | ~ spl2_22
    | ~ spl2_29 ),
    inference(superposition,[],[f339,f538])).

fof(f538,plain,
    ( ! [X2,X3] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,X3))
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f537])).

fof(f1822,plain,
    ( spl2_53
    | ~ spl2_22
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f560,f529,f338,f1820])).

fof(f560,plain,
    ( ! [X10,X11] : k4_xboole_0(X11,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,X11),X10)
    | ~ spl2_22
    | ~ spl2_27 ),
    inference(superposition,[],[f339,f530])).

fof(f1818,plain,
    ( spl2_52
    | ~ spl2_21
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f559,f529,f334,f1816])).

fof(f334,plain,
    ( spl2_21
  <=> ! [X7,X6] : k5_xboole_0(k5_xboole_0(X6,X7),X7) = X6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f559,plain,
    ( ! [X8,X9] : k5_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,k4_xboole_0(X9,X8))) = X8
    | ~ spl2_21
    | ~ spl2_27 ),
    inference(superposition,[],[f335,f530])).

fof(f335,plain,
    ( ! [X6,X7] : k5_xboole_0(k5_xboole_0(X6,X7),X7) = X6
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f334])).

fof(f1814,plain,
    ( spl2_51
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f409,f342,f49,f1812])).

fof(f409,plain,
    ( ! [X2,X3,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(k5_xboole_0(X2,X1),X3)
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(superposition,[],[f50,f343])).

fof(f1806,plain,
    ( spl2_49
    | ~ spl2_4
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f374,f338,f49,f1804])).

fof(f374,plain,
    ( ! [X10,X11,X9] : k5_xboole_0(X10,X11) = k5_xboole_0(k5_xboole_0(X9,X10),k5_xboole_0(X9,X11))
    | ~ spl2_4
    | ~ spl2_22 ),
    inference(superposition,[],[f50,f339])).

fof(f1078,plain,
    ( spl2_40
    | ~ spl2_20
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f820,f780,f309,f1076])).

fof(f820,plain,
    ( ! [X35,X36,X34] : k5_xboole_0(X35,X34) = k5_xboole_0(k5_xboole_0(X36,X34),k5_xboole_0(X36,X35))
    | ~ spl2_20
    | ~ spl2_31 ),
    inference(superposition,[],[f781,f310])).

fof(f1074,plain,
    ( spl2_39
    | ~ spl2_20
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f558,f529,f309,f1072])).

fof(f558,plain,
    ( ! [X6,X7] : k5_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7)) = X6
    | ~ spl2_20
    | ~ spl2_27 ),
    inference(superposition,[],[f310,f530])).

fof(f1070,plain,
    ( spl2_38
    | ~ spl2_4
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f330,f309,f49,f1068])).

fof(f330,plain,
    ( ! [X4,X5,X3] : k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X5)))
    | ~ spl2_4
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f322,f50])).

fof(f322,plain,
    ( ! [X4,X5,X3] : k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X4,X3),X5))
    | ~ spl2_4
    | ~ spl2_20 ),
    inference(superposition,[],[f50,f310])).

fof(f883,plain,(
    ~ spl2_35 ),
    inference(avatar_split_clause,[],[f26,f880])).

fof(f26,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f15,f19,f20])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f15,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).

fof(f794,plain,
    ( spl2_34
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f765,f714,f57,f36,f32,f792])).

fof(f714,plain,
    ( spl2_30
  <=> ! [X7,X8] : k4_xboole_0(X8,X7) = k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X8,X7)),X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f765,plain,
    ( ! [X4,X5] : k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,X4)) = X4
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_30 ),
    inference(forward_demodulation,[],[f764,f33])).

fof(f764,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,X4))
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_30 ),
    inference(forward_demodulation,[],[f736,f37])).

fof(f736,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,k5_xboole_0(X4,k4_xboole_0(X5,X4)))) = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,X4))
    | ~ spl2_6
    | ~ spl2_30 ),
    inference(superposition,[],[f58,f715])).

fof(f715,plain,
    ( ! [X8,X7] : k4_xboole_0(X8,X7) = k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X8,X7)),X7)
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f714])).

fof(f790,plain,
    ( spl2_33
    | ~ spl2_25
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f740,f714,f460,f788])).

fof(f740,plain,
    ( ! [X12,X13] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X13,X12),k5_xboole_0(X12,k4_xboole_0(X13,X12)))
    | ~ spl2_25
    | ~ spl2_30 ),
    inference(superposition,[],[f461,f715])).

fof(f786,plain,
    ( spl2_32
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f246,f171,f101,f77,f53,f784])).

fof(f171,plain,
    ( spl2_15
  <=> ! [X1,X0] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f246,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f222,f238])).

fof(f238,plain,
    ( ! [X3] : k5_xboole_0(k1_xboole_0,X3) = X3
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f221,f102])).

fof(f221,plain,
    ( ! [X3] : k5_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X3,k1_xboole_0)
    | ~ spl2_8
    | ~ spl2_15 ),
    inference(superposition,[],[f172,f78])).

fof(f172,plain,
    ( ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f171])).

fof(f222,plain,
    ( ! [X4,X5] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X4,k4_xboole_0(X4,X5))) = k5_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl2_5
    | ~ spl2_15 ),
    inference(superposition,[],[f172,f54])).

fof(f782,plain,
    ( spl2_31
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f244,f171,f101,f77,f49,f780])).

fof(f244,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_15 ),
    inference(backward_demodulation,[],[f220,f238])).

fof(f220,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2)))
    | ~ spl2_4
    | ~ spl2_15 ),
    inference(superposition,[],[f172,f50])).

fof(f716,plain,
    ( spl2_30
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_22
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f570,f529,f338,f36,f32,f714])).

fof(f570,plain,
    ( ! [X8,X7] : k4_xboole_0(X8,X7) = k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X8,X7)),X7)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_22
    | ~ spl2_27 ),
    inference(forward_demodulation,[],[f569,f339])).

fof(f569,plain,
    ( ! [X8,X7] : k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X8,X7)),X7) = k5_xboole_0(k5_xboole_0(X7,k4_xboole_0(X8,X7)),X7)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_27 ),
    inference(forward_demodulation,[],[f544,f33])).

fof(f544,plain,
    ( ! [X8,X7] : k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X8,X7)),X7) = k5_xboole_0(k5_xboole_0(X7,k4_xboole_0(X8,X7)),k4_xboole_0(X7,k1_xboole_0))
    | ~ spl2_2
    | ~ spl2_27 ),
    inference(superposition,[],[f530,f37])).

fof(f539,plain,
    ( spl2_29
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f395,f61,f57,f53,f537])).

fof(f61,plain,
    ( spl2_7
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f395,plain,
    ( ! [X2,X3] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,X3))
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(backward_demodulation,[],[f135,f383])).

fof(f383,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(superposition,[],[f62,f58])).

fof(f62,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f135,plain,
    ( ! [X2,X3] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))))
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(superposition,[],[f54,f58])).

fof(f535,plain,
    ( spl2_28
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f383,f61,f57,f533])).

fof(f531,plain,
    ( spl2_27
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f134,f57,f53,f529])).

fof(f134,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(superposition,[],[f54,f58])).

fof(f488,plain,
    ( spl2_26
    | ~ spl2_6
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f441,f430,f57,f486])).

fof(f441,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)
    | ~ spl2_6
    | ~ spl2_24 ),
    inference(superposition,[],[f431,f58])).

fof(f462,plain,
    ( spl2_25
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f453,f430,f61,f57,f460])).

fof(f453,plain,
    ( ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1)
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_24 ),
    inference(forward_demodulation,[],[f434,f383])).

fof(f434,plain,
    ( ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))),X1)
    | ~ spl2_6
    | ~ spl2_24 ),
    inference(superposition,[],[f431,f58])).

fof(f432,plain,
    ( spl2_24
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_21
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f398,f342,f334,f61,f53,f36,f430])).

fof(f398,plain,
    ( ! [X12,X13] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X13)),X12)
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_21
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f397,f347])).

fof(f347,plain,
    ( ! [X6,X7] : k5_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X6,k4_xboole_0(X6,X7))) = X6
    | ~ spl2_5
    | ~ spl2_21 ),
    inference(superposition,[],[f335,f54])).

fof(f397,plain,
    ( ! [X12,X13] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X13)),k5_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X12,k4_xboole_0(X12,X13))))
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f389,f343])).

fof(f389,plain,
    ( ! [X12,X13] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X13)),k5_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X13)),k4_xboole_0(X12,X13)))
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(superposition,[],[f37,f62])).

fof(f344,plain,
    ( spl2_23
    | ~ spl2_19
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f321,f309,f282,f342])).

fof(f282,plain,
    ( spl2_19
  <=> ! [X1,X0] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f321,plain,
    ( ! [X2,X1] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)
    | ~ spl2_19
    | ~ spl2_20 ),
    inference(superposition,[],[f283,f310])).

fof(f283,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f282])).

fof(f340,plain,
    ( spl2_22
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f316,f309,f338])).

fof(f316,plain,
    ( ! [X8,X9] : k5_xboole_0(k5_xboole_0(X9,X8),X9) = X8
    | ~ spl2_20 ),
    inference(superposition,[],[f310,f310])).

fof(f336,plain,
    ( spl2_21
    | ~ spl2_19
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f315,f309,f282,f334])).

fof(f315,plain,
    ( ! [X6,X7] : k5_xboole_0(k5_xboole_0(X6,X7),X7) = X6
    | ~ spl2_19
    | ~ spl2_20 ),
    inference(superposition,[],[f310,f283])).

fof(f311,plain,
    ( spl2_20
    | ~ spl2_10
    | ~ spl2_14
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f300,f282,f167,f101,f309])).

fof(f167,plain,
    ( spl2_14
  <=> ! [X1,X0] : k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f300,plain,
    ( ! [X6,X7] : k5_xboole_0(X7,k5_xboole_0(X6,X7)) = X6
    | ~ spl2_10
    | ~ spl2_14
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f288,f102])).

fof(f288,plain,
    ( ! [X6,X7] : k5_xboole_0(X7,k5_xboole_0(X6,X7)) = k5_xboole_0(X6,k1_xboole_0)
    | ~ spl2_14
    | ~ spl2_19 ),
    inference(superposition,[],[f283,f168])).

fof(f168,plain,
    ( ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f167])).

fof(f284,plain,
    ( spl2_19
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f240,f171,f101,f77,f282])).

fof(f240,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_15 ),
    inference(backward_demodulation,[],[f172,f238])).

fof(f267,plain,
    ( spl2_18
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f238,f171,f101,f77,f265])).

fof(f173,plain,
    ( spl2_15
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f81,f77,f49,f171])).

fof(f81,plain,
    ( ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(superposition,[],[f50,f78])).

fof(f169,plain,
    ( spl2_14
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f80,f77,f49,f167])).

fof(f80,plain,
    ( ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(superposition,[],[f78,f50])).

fof(f145,plain,
    ( spl2_13
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f128,f117,f77,f53,f143])).

fof(f117,plain,
    ( spl2_12
  <=> ! [X3] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f128,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f125,f78])).

fof(f125,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_5
    | ~ spl2_12 ),
    inference(superposition,[],[f54,f118])).

fof(f118,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f117])).

fof(f119,plain,
    ( spl2_12
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f73,f53,f43,f117])).

fof(f43,plain,
    ( spl2_3
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f73,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3))
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(superposition,[],[f44,f54])).

fof(f44,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f103,plain,
    ( spl2_10
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f94,f85,f36,f101])).

fof(f85,plain,
    ( spl2_9
  <=> ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f94,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(backward_demodulation,[],[f86,f90])).

fof(f90,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(superposition,[],[f37,f86])).

fof(f86,plain,
    ( ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f85])).

fof(f87,plain,
    ( spl2_9
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f68,f53,f32,f85])).

fof(f68,plain,
    ( ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(superposition,[],[f54,f33])).

fof(f79,plain,
    ( spl2_8
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f75,f53,f36,f32,f77])).

fof(f75,plain,
    ( ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f69,f33])).

fof(f69,plain,
    ( ! [X1] : k1_xboole_0 = k5_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(superposition,[],[f54,f37])).

fof(f63,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f29,f61])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f59,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f28,f57])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f18,f20,f20])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f55,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f25,f53])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f21,f20])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f51,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f23,f49])).

fof(f23,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f45,plain,
    ( spl2_3
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f39,f36,f32,f43])).

fof(f39,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(superposition,[],[f37,f33])).

fof(f38,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f27,f36])).

fof(f27,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f17,f19])).

fof(f17,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f34,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f16,f32])).

fof(f16,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:47:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.45  % (17414)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % (17406)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (17420)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (17415)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.47  % (17409)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (17412)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (17411)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (17422)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.48  % (17416)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (17408)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (17418)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.49  % (17413)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.50  % (17421)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.50  % (17410)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.51  % (17419)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.51  % (17407)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.52  % (17423)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.32/0.54  % (17417)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 1.32/0.54  % (17417)Refutation not found, incomplete strategy% (17417)------------------------------
% 1.32/0.54  % (17417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (17417)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (17417)Memory used [KB]: 10490
% 1.32/0.54  % (17417)Time elapsed: 0.110 s
% 1.32/0.54  % (17417)------------------------------
% 1.32/0.54  % (17417)------------------------------
% 5.02/1.01  % (17410)Time limit reached!
% 5.02/1.01  % (17410)------------------------------
% 5.02/1.01  % (17410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.02/1.01  % (17410)Termination reason: Time limit
% 5.02/1.01  % (17410)Termination phase: Saturation
% 5.02/1.01  
% 5.02/1.01  % (17410)Memory used [KB]: 14839
% 5.02/1.01  % (17410)Time elapsed: 0.600 s
% 5.02/1.01  % (17410)------------------------------
% 5.02/1.01  % (17410)------------------------------
% 12.63/1.96  % (17412)Time limit reached!
% 12.63/1.96  % (17412)------------------------------
% 12.63/1.96  % (17412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.63/1.97  % (17411)Time limit reached!
% 12.63/1.97  % (17411)------------------------------
% 12.63/1.97  % (17411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.63/1.97  % (17411)Termination reason: Time limit
% 12.63/1.97  % (17411)Termination phase: Saturation
% 12.63/1.97  
% 12.63/1.97  % (17411)Memory used [KB]: 36459
% 12.63/1.97  % (17411)Time elapsed: 1.553 s
% 12.63/1.97  % (17411)------------------------------
% 12.63/1.97  % (17411)------------------------------
% 12.63/1.98  % (17412)Termination reason: Time limit
% 12.63/1.98  % (17412)Termination phase: Saturation
% 12.63/1.98  
% 12.63/1.98  % (17412)Memory used [KB]: 42344
% 12.63/1.98  % (17412)Time elapsed: 1.500 s
% 12.63/1.98  % (17412)------------------------------
% 12.63/1.98  % (17412)------------------------------
% 14.47/2.22  % (17408)Time limit reached!
% 14.47/2.22  % (17408)------------------------------
% 14.47/2.22  % (17408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.47/2.23  % (17408)Termination reason: Time limit
% 14.47/2.23  
% 14.47/2.23  % (17408)Memory used [KB]: 45287
% 14.47/2.23  % (17408)Time elapsed: 1.804 s
% 14.47/2.23  % (17408)------------------------------
% 14.47/2.23  % (17408)------------------------------
% 17.82/2.62  % (17418)Time limit reached!
% 17.82/2.62  % (17418)------------------------------
% 17.82/2.62  % (17418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.82/2.62  % (17418)Termination reason: Time limit
% 17.82/2.62  % (17418)Termination phase: Saturation
% 17.82/2.62  
% 17.82/2.62  % (17418)Memory used [KB]: 44647
% 17.82/2.62  % (17418)Time elapsed: 2.200 s
% 17.82/2.62  % (17418)------------------------------
% 17.82/2.62  % (17418)------------------------------
% 27.78/3.87  % (17413)Refutation found. Thanks to Tanya!
% 27.78/3.87  % SZS status Theorem for theBenchmark
% 27.78/3.87  % SZS output start Proof for theBenchmark
% 27.78/3.87  fof(f57787,plain,(
% 27.78/3.87    $false),
% 27.78/3.87    inference(avatar_sat_refutation,[],[f34,f38,f45,f51,f55,f59,f63,f79,f87,f103,f119,f145,f169,f173,f267,f284,f311,f336,f340,f344,f432,f462,f488,f531,f535,f539,f716,f782,f786,f790,f794,f883,f1070,f1074,f1078,f1806,f1814,f1818,f1822,f1826,f1834,f1870,f1894,f4156,f4282,f4381,f4473,f4645,f10637,f10963,f17447,f19750,f19754,f19758,f19762,f23694,f23970,f26123,f26408,f27542,f28165,f28786,f28794,f30383,f30387,f30391,f31933,f35175,f43777,f43781,f54055,f54719,f55388,f56017,f56982,f57733])).
% 27.78/3.87  fof(f57733,plain,(
% 27.78/3.87    ~spl2_27 | ~spl2_32 | spl2_35 | ~spl2_131 | ~spl2_157 | ~spl2_181),
% 27.78/3.87    inference(avatar_contradiction_clause,[],[f57732])).
% 27.78/3.87  fof(f57732,plain,(
% 27.78/3.87    $false | (~spl2_27 | ~spl2_32 | spl2_35 | ~spl2_131 | ~spl2_157 | ~spl2_181)),
% 27.78/3.87    inference(subsumption_resolution,[],[f882,f57731])).
% 27.78/3.87  fof(f57731,plain,(
% 27.78/3.87    ( ! [X210,X209] : (k5_xboole_0(X209,X210) = k4_xboole_0(k5_xboole_0(X209,k4_xboole_0(X210,X209)),k4_xboole_0(X209,k4_xboole_0(X209,X210)))) ) | (~spl2_27 | ~spl2_32 | ~spl2_131 | ~spl2_157 | ~spl2_181)),
% 27.78/3.87    inference(forward_demodulation,[],[f57170,f57525])).
% 27.78/3.87  fof(f57525,plain,(
% 27.78/3.87    ( ! [X33,X32] : (k4_xboole_0(X32,k4_xboole_0(X32,X33)) = k4_xboole_0(X32,k5_xboole_0(X32,X33))) ) | (~spl2_27 | ~spl2_32 | ~spl2_157 | ~spl2_181)),
% 27.78/3.87    inference(forward_demodulation,[],[f57524,f785])).
% 27.78/3.87  fof(f785,plain,(
% 27.78/3.87    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))) ) | ~spl2_32),
% 27.78/3.87    inference(avatar_component_clause,[],[f784])).
% 27.78/3.87  fof(f784,plain,(
% 27.78/3.87    spl2_32 <=> ! [X5,X4] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 27.78/3.87  fof(f57524,plain,(
% 27.78/3.87    ( ! [X33,X32] : (k5_xboole_0(X32,k4_xboole_0(X32,X33)) = k4_xboole_0(X32,k5_xboole_0(X32,X33))) ) | (~spl2_27 | ~spl2_157 | ~spl2_181)),
% 27.78/3.87    inference(forward_demodulation,[],[f57102,f43780])).
% 27.78/3.87  fof(f43780,plain,(
% 27.78/3.87    ( ! [X280,X279] : (k4_xboole_0(X280,X279) = k4_xboole_0(k5_xboole_0(X280,X279),k4_xboole_0(X279,X280))) ) | ~spl2_157),
% 27.78/3.87    inference(avatar_component_clause,[],[f43779])).
% 27.78/3.87  fof(f43779,plain,(
% 27.78/3.87    spl2_157 <=> ! [X279,X280] : k4_xboole_0(X280,X279) = k4_xboole_0(k5_xboole_0(X280,X279),k4_xboole_0(X279,X280))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_157])])).
% 27.78/3.87  fof(f57102,plain,(
% 27.78/3.87    ( ! [X33,X32] : (k4_xboole_0(X32,k5_xboole_0(X32,X33)) = k5_xboole_0(X32,k4_xboole_0(k5_xboole_0(X32,X33),k4_xboole_0(X33,X32)))) ) | (~spl2_27 | ~spl2_181)),
% 27.78/3.87    inference(superposition,[],[f530,f56981])).
% 27.78/3.87  fof(f56981,plain,(
% 27.78/3.87    ( ! [X50,X51] : (k4_xboole_0(X51,X50) = k4_xboole_0(k5_xboole_0(X50,X51),X50)) ) | ~spl2_181),
% 27.78/3.87    inference(avatar_component_clause,[],[f56980])).
% 27.78/3.87  fof(f56980,plain,(
% 27.78/3.87    spl2_181 <=> ! [X51,X50] : k4_xboole_0(X51,X50) = k4_xboole_0(k5_xboole_0(X50,X51),X50)),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_181])])).
% 27.78/3.87  fof(f530,plain,(
% 27.78/3.87    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | ~spl2_27),
% 27.78/3.87    inference(avatar_component_clause,[],[f529])).
% 27.78/3.87  fof(f529,plain,(
% 27.78/3.87    spl2_27 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 27.78/3.87  fof(f57170,plain,(
% 27.78/3.87    ( ! [X210,X209] : (k5_xboole_0(X209,X210) = k4_xboole_0(k5_xboole_0(X209,k4_xboole_0(X210,X209)),k4_xboole_0(X209,k5_xboole_0(X209,X210)))) ) | (~spl2_131 | ~spl2_181)),
% 27.78/3.87    inference(superposition,[],[f30382,f56981])).
% 27.78/3.87  fof(f30382,plain,(
% 27.78/3.87    ( ! [X6,X5] : (k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),k4_xboole_0(X5,X6)) = X6) ) | ~spl2_131),
% 27.78/3.87    inference(avatar_component_clause,[],[f30381])).
% 27.78/3.87  fof(f30381,plain,(
% 27.78/3.87    spl2_131 <=> ! [X5,X6] : k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),k4_xboole_0(X5,X6)) = X6),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_131])])).
% 27.78/3.87  fof(f882,plain,(
% 27.78/3.87    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_35),
% 27.78/3.87    inference(avatar_component_clause,[],[f880])).
% 27.78/3.87  fof(f880,plain,(
% 27.78/3.87    spl2_35 <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 27.78/3.87  fof(f56982,plain,(
% 27.78/3.87    spl2_181 | ~spl2_1 | ~spl2_6 | ~spl2_65 | ~spl2_76 | ~spl2_149 | ~spl2_179),
% 27.78/3.87    inference(avatar_split_clause,[],[f56600,f56015,f35173,f4379,f1868,f57,f32,f56980])).
% 27.78/3.87  fof(f32,plain,(
% 27.78/3.87    spl2_1 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 27.78/3.87  fof(f57,plain,(
% 27.78/3.87    spl2_6 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 27.78/3.87  fof(f1868,plain,(
% 27.78/3.87    spl2_65 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).
% 27.78/3.87  fof(f4379,plain,(
% 27.78/3.87    spl2_76 <=> ! [X13,X14] : k4_xboole_0(X14,X13) = k4_xboole_0(k4_xboole_0(X14,X13),X13)),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).
% 27.78/3.87  fof(f35173,plain,(
% 27.78/3.87    spl2_149 <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k5_xboole_0(X3,X2))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_149])])).
% 27.78/3.87  fof(f56015,plain,(
% 27.78/3.87    spl2_179 <=> ! [X170,X169] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X169,X170),X169),k4_xboole_0(X170,X169))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_179])])).
% 27.78/3.87  fof(f56600,plain,(
% 27.78/3.87    ( ! [X50,X51] : (k4_xboole_0(X51,X50) = k4_xboole_0(k5_xboole_0(X50,X51),X50)) ) | (~spl2_1 | ~spl2_6 | ~spl2_65 | ~spl2_76 | ~spl2_149 | ~spl2_179)),
% 27.78/3.87    inference(forward_demodulation,[],[f56599,f4380])).
% 27.78/3.87  fof(f4380,plain,(
% 27.78/3.87    ( ! [X14,X13] : (k4_xboole_0(X14,X13) = k4_xboole_0(k4_xboole_0(X14,X13),X13)) ) | ~spl2_76),
% 27.78/3.87    inference(avatar_component_clause,[],[f4379])).
% 27.78/3.87  fof(f56599,plain,(
% 27.78/3.87    ( ! [X50,X51] : (k4_xboole_0(k5_xboole_0(X50,X51),X50) = k4_xboole_0(k4_xboole_0(X51,X50),X50)) ) | (~spl2_1 | ~spl2_6 | ~spl2_65 | ~spl2_149 | ~spl2_179)),
% 27.78/3.87    inference(forward_demodulation,[],[f56598,f35983])).
% 27.78/3.87  fof(f35983,plain,(
% 27.78/3.87    ( ! [X92,X90,X91] : (k4_xboole_0(k4_xboole_0(X90,X91),X92) = k4_xboole_0(k4_xboole_0(X90,X91),k4_xboole_0(k4_xboole_0(X90,X91),k4_xboole_0(k5_xboole_0(X91,X90),X92)))) ) | (~spl2_1 | ~spl2_65 | ~spl2_149)),
% 27.78/3.87    inference(forward_demodulation,[],[f35800,f33])).
% 27.78/3.87  fof(f33,plain,(
% 27.78/3.87    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_1),
% 27.78/3.87    inference(avatar_component_clause,[],[f32])).
% 27.78/3.87  fof(f35800,plain,(
% 27.78/3.87    ( ! [X92,X90,X91] : (k4_xboole_0(k4_xboole_0(X90,X91),k4_xboole_0(k4_xboole_0(X90,X91),k4_xboole_0(k5_xboole_0(X91,X90),X92))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X90,X91),k1_xboole_0),X92)) ) | (~spl2_65 | ~spl2_149)),
% 27.78/3.87    inference(superposition,[],[f1869,f35174])).
% 27.78/3.87  fof(f35174,plain,(
% 27.78/3.87    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k5_xboole_0(X3,X2))) ) | ~spl2_149),
% 27.78/3.87    inference(avatar_component_clause,[],[f35173])).
% 27.78/3.87  fof(f1869,plain,(
% 27.78/3.87    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ) | ~spl2_65),
% 27.78/3.87    inference(avatar_component_clause,[],[f1868])).
% 27.78/3.87  fof(f56598,plain,(
% 27.78/3.87    ( ! [X50,X51] : (k4_xboole_0(k5_xboole_0(X50,X51),X50) = k4_xboole_0(k4_xboole_0(X51,X50),k4_xboole_0(k4_xboole_0(X51,X50),k4_xboole_0(k5_xboole_0(X50,X51),X50)))) ) | (~spl2_1 | ~spl2_6 | ~spl2_179)),
% 27.78/3.87    inference(forward_demodulation,[],[f56229,f33])).
% 27.78/3.87  fof(f56229,plain,(
% 27.78/3.87    ( ! [X50,X51] : (k4_xboole_0(k4_xboole_0(X51,X50),k4_xboole_0(k4_xboole_0(X51,X50),k4_xboole_0(k5_xboole_0(X50,X51),X50))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X50,X51),X50),k1_xboole_0)) ) | (~spl2_6 | ~spl2_179)),
% 27.78/3.87    inference(superposition,[],[f58,f56016])).
% 27.78/3.87  fof(f56016,plain,(
% 27.78/3.87    ( ! [X169,X170] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X169,X170),X169),k4_xboole_0(X170,X169))) ) | ~spl2_179),
% 27.78/3.87    inference(avatar_component_clause,[],[f56015])).
% 27.78/3.87  fof(f58,plain,(
% 27.78/3.87    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) ) | ~spl2_6),
% 27.78/3.87    inference(avatar_component_clause,[],[f57])).
% 27.78/3.87  fof(f56017,plain,(
% 27.78/3.87    spl2_179 | ~spl2_156 | ~spl2_178),
% 27.78/3.87    inference(avatar_split_clause,[],[f55602,f55386,f43775,f56015])).
% 27.78/3.87  fof(f43775,plain,(
% 27.78/3.87    spl2_156 <=> ! [X86,X87] : k4_xboole_0(X87,X86) = k4_xboole_0(k5_xboole_0(X86,X87),k4_xboole_0(X86,X87))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_156])])).
% 27.78/3.87  fof(f55386,plain,(
% 27.78/3.87    spl2_178 <=> ! [X25,X24,X26] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X24,X25),k4_xboole_0(X24,k4_xboole_0(X25,X26)))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_178])])).
% 27.78/3.87  fof(f55602,plain,(
% 27.78/3.87    ( ! [X169,X170] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X169,X170),X169),k4_xboole_0(X170,X169))) ) | (~spl2_156 | ~spl2_178)),
% 27.78/3.87    inference(superposition,[],[f55387,f43776])).
% 27.78/3.87  fof(f43776,plain,(
% 27.78/3.87    ( ! [X87,X86] : (k4_xboole_0(X87,X86) = k4_xboole_0(k5_xboole_0(X86,X87),k4_xboole_0(X86,X87))) ) | ~spl2_156),
% 27.78/3.87    inference(avatar_component_clause,[],[f43775])).
% 27.78/3.87  fof(f55387,plain,(
% 27.78/3.87    ( ! [X26,X24,X25] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X24,X25),k4_xboole_0(X24,k4_xboole_0(X25,X26)))) ) | ~spl2_178),
% 27.78/3.87    inference(avatar_component_clause,[],[f55386])).
% 27.78/3.87  fof(f55388,plain,(
% 27.78/3.87    spl2_178 | ~spl2_81 | ~spl2_177),
% 27.78/3.87    inference(avatar_split_clause,[],[f54808,f54717,f10635,f55386])).
% 27.78/3.87  fof(f10635,plain,(
% 27.78/3.87    spl2_81 <=> ! [X20,X22,X21] : k4_xboole_0(X21,X20) = k4_xboole_0(k4_xboole_0(X21,X20),k4_xboole_0(X20,X22))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_81])])).
% 27.78/3.87  fof(f54717,plain,(
% 27.78/3.87    spl2_177 <=> ! [X3,X2,X4] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(X2,X4))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_177])])).
% 27.78/3.87  fof(f54808,plain,(
% 27.78/3.87    ( ! [X26,X24,X25] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X24,X25),k4_xboole_0(X24,k4_xboole_0(X25,X26)))) ) | (~spl2_81 | ~spl2_177)),
% 27.78/3.87    inference(superposition,[],[f54718,f10636])).
% 27.78/3.87  fof(f10636,plain,(
% 27.78/3.87    ( ! [X21,X22,X20] : (k4_xboole_0(X21,X20) = k4_xboole_0(k4_xboole_0(X21,X20),k4_xboole_0(X20,X22))) ) | ~spl2_81),
% 27.78/3.87    inference(avatar_component_clause,[],[f10635])).
% 27.78/3.87  fof(f54718,plain,(
% 27.78/3.87    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(X2,X4))) ) | ~spl2_177),
% 27.78/3.87    inference(avatar_component_clause,[],[f54717])).
% 27.78/3.87  fof(f54719,plain,(
% 27.78/3.87    spl2_177 | ~spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_18 | ~spl2_38 | ~spl2_117 | ~spl2_131 | ~spl2_139 | ~spl2_176),
% 27.78/3.87    inference(avatar_split_clause,[],[f54403,f54053,f31931,f30381,f23968,f1068,f265,f57,f53,f49,f54717])).
% 27.78/3.87  fof(f49,plain,(
% 27.78/3.87    spl2_4 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 27.78/3.87  fof(f53,plain,(
% 27.78/3.87    spl2_5 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 27.78/3.87  fof(f265,plain,(
% 27.78/3.87    spl2_18 <=> ! [X3] : k5_xboole_0(k1_xboole_0,X3) = X3),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 27.78/3.87  fof(f1068,plain,(
% 27.78/3.87    spl2_38 <=> ! [X3,X5,X4] : k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X5)))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 27.78/3.87  fof(f23968,plain,(
% 27.78/3.87    spl2_117 <=> ! [X120,X122,X121] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X120,X122),k5_xboole_0(X120,k4_xboole_0(X121,X120)))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_117])])).
% 27.78/3.87  fof(f31931,plain,(
% 27.78/3.87    spl2_139 <=> ! [X32,X33] : k5_xboole_0(X32,X33) = k5_xboole_0(k4_xboole_0(X33,X32),k4_xboole_0(X32,X33))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_139])])).
% 27.78/3.87  fof(f54053,plain,(
% 27.78/3.87    spl2_176 <=> ! [X25,X24,X26] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X24,X26),k4_xboole_0(k5_xboole_0(X24,k4_xboole_0(X25,X24)),X26))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_176])])).
% 27.78/3.87  fof(f54403,plain,(
% 27.78/3.87    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(X2,X4))) ) | (~spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_18 | ~spl2_38 | ~spl2_117 | ~spl2_131 | ~spl2_139 | ~spl2_176)),
% 27.78/3.87    inference(forward_demodulation,[],[f54402,f30382])).
% 27.78/3.87  fof(f54402,plain,(
% 27.78/3.87    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X2,X3)),k4_xboole_0(X3,X2)),X4))) ) | (~spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_18 | ~spl2_38 | ~spl2_117 | ~spl2_139 | ~spl2_176)),
% 27.78/3.87    inference(forward_demodulation,[],[f54401,f35004])).
% 27.78/3.87  fof(f35004,plain,(
% 27.78/3.87    ( ! [X85,X86,X84] : (k4_xboole_0(k5_xboole_0(X84,k4_xboole_0(X86,X84)),k4_xboole_0(X84,X85)) = k5_xboole_0(X84,k5_xboole_0(k4_xboole_0(X86,X84),k4_xboole_0(X84,X85)))) ) | (~spl2_4 | ~spl2_18 | ~spl2_117 | ~spl2_139)),
% 27.78/3.87    inference(forward_demodulation,[],[f35003,f266])).
% 27.78/3.87  fof(f266,plain,(
% 27.78/3.87    ( ! [X3] : (k5_xboole_0(k1_xboole_0,X3) = X3) ) | ~spl2_18),
% 27.78/3.87    inference(avatar_component_clause,[],[f265])).
% 27.78/3.87  fof(f35003,plain,(
% 27.78/3.87    ( ! [X85,X86,X84] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(X84,k4_xboole_0(X86,X84)),k4_xboole_0(X84,X85))) = k5_xboole_0(X84,k5_xboole_0(k4_xboole_0(X86,X84),k4_xboole_0(X84,X85)))) ) | (~spl2_4 | ~spl2_117 | ~spl2_139)),
% 27.78/3.87    inference(forward_demodulation,[],[f34799,f50])).
% 27.78/3.87  fof(f50,plain,(
% 27.78/3.87    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) ) | ~spl2_4),
% 27.78/3.87    inference(avatar_component_clause,[],[f49])).
% 27.78/3.87  fof(f34799,plain,(
% 27.78/3.87    ( ! [X85,X86,X84] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(X84,k4_xboole_0(X86,X84)),k4_xboole_0(X84,X85))) = k5_xboole_0(k5_xboole_0(X84,k4_xboole_0(X86,X84)),k4_xboole_0(X84,X85))) ) | (~spl2_117 | ~spl2_139)),
% 27.78/3.87    inference(superposition,[],[f31932,f23969])).
% 27.78/3.87  fof(f23969,plain,(
% 27.78/3.87    ( ! [X121,X122,X120] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X120,X122),k5_xboole_0(X120,k4_xboole_0(X121,X120)))) ) | ~spl2_117),
% 27.78/3.87    inference(avatar_component_clause,[],[f23968])).
% 27.78/3.87  fof(f31932,plain,(
% 27.78/3.87    ( ! [X33,X32] : (k5_xboole_0(X32,X33) = k5_xboole_0(k4_xboole_0(X33,X32),k4_xboole_0(X32,X33))) ) | ~spl2_139),
% 27.78/3.87    inference(avatar_component_clause,[],[f31931])).
% 27.78/3.87  fof(f54401,plain,(
% 27.78/3.87    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(k5_xboole_0(X3,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))),X4))) ) | (~spl2_5 | ~spl2_6 | ~spl2_38 | ~spl2_176)),
% 27.78/3.87    inference(forward_demodulation,[],[f54134,f1190])).
% 27.78/3.87  fof(f1190,plain,(
% 27.78/3.87    ( ! [X10,X8,X9] : (k5_xboole_0(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))) = k5_xboole_0(X8,k5_xboole_0(X10,k4_xboole_0(X8,X9)))) ) | (~spl2_5 | ~spl2_38)),
% 27.78/3.87    inference(superposition,[],[f1069,f54])).
% 27.78/3.87  fof(f54,plain,(
% 27.78/3.87    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl2_5),
% 27.78/3.87    inference(avatar_component_clause,[],[f53])).
% 27.78/3.87  fof(f1069,plain,(
% 27.78/3.87    ( ! [X4,X5,X3] : (k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X5)))) ) | ~spl2_38),
% 27.78/3.87    inference(avatar_component_clause,[],[f1068])).
% 27.78/3.87  fof(f54134,plain,(
% 27.78/3.87    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,k4_xboole_0(X3,X2))),X4))) ) | (~spl2_6 | ~spl2_176)),
% 27.78/3.87    inference(superposition,[],[f54054,f58])).
% 27.78/3.87  fof(f54054,plain,(
% 27.78/3.87    ( ! [X26,X24,X25] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X24,X26),k4_xboole_0(k5_xboole_0(X24,k4_xboole_0(X25,X24)),X26))) ) | ~spl2_176),
% 27.78/3.87    inference(avatar_component_clause,[],[f54053])).
% 27.78/3.87  fof(f54055,plain,(
% 27.78/3.87    spl2_176 | ~spl2_26 | ~spl2_112),
% 27.78/3.87    inference(avatar_split_clause,[],[f30042,f19756,f486,f54053])).
% 27.78/3.87  fof(f486,plain,(
% 27.78/3.87    spl2_26 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 27.78/3.87  fof(f19756,plain,(
% 27.78/3.87    spl2_112 <=> ! [X20,X22,X21] : k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(k5_xboole_0(X20,k4_xboole_0(X21,X20)),X22))) = k4_xboole_0(X20,X22)),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_112])])).
% 27.78/3.87  fof(f30042,plain,(
% 27.78/3.87    ( ! [X26,X24,X25] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X24,X26),k4_xboole_0(k5_xboole_0(X24,k4_xboole_0(X25,X24)),X26))) ) | (~spl2_26 | ~spl2_112)),
% 27.78/3.87    inference(superposition,[],[f487,f19757])).
% 27.78/3.87  fof(f19757,plain,(
% 27.78/3.87    ( ! [X21,X22,X20] : (k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(k5_xboole_0(X20,k4_xboole_0(X21,X20)),X22))) = k4_xboole_0(X20,X22)) ) | ~spl2_112),
% 27.78/3.87    inference(avatar_component_clause,[],[f19756])).
% 27.78/3.87  fof(f487,plain,(
% 27.78/3.87    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) ) | ~spl2_26),
% 27.78/3.87    inference(avatar_component_clause,[],[f486])).
% 27.78/3.87  fof(f43781,plain,(
% 27.78/3.87    spl2_157 | ~spl2_18 | ~spl2_111 | ~spl2_132 | ~spl2_133 | ~spl2_139),
% 27.78/3.87    inference(avatar_split_clause,[],[f35129,f31931,f30389,f30385,f19752,f265,f43779])).
% 27.78/3.87  fof(f19752,plain,(
% 27.78/3.87    spl2_111 <=> ! [X20,X19,X21] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X20,X21),k5_xboole_0(k4_xboole_0(X20,X21),k4_xboole_0(X19,X20)))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_111])])).
% 27.78/3.87  fof(f30385,plain,(
% 27.78/3.87    spl2_132 <=> ! [X3,X4] : k4_xboole_0(X3,X4) = k5_xboole_0(k4_xboole_0(X4,X3),k5_xboole_0(X4,X3))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_132])])).
% 27.78/3.87  fof(f30389,plain,(
% 27.78/3.87    spl2_133 <=> ! [X9,X10] : k4_xboole_0(X9,X10) = k5_xboole_0(k4_xboole_0(X10,X9),k5_xboole_0(X9,X10))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_133])])).
% 27.78/3.87  fof(f35129,plain,(
% 27.78/3.87    ( ! [X280,X279] : (k4_xboole_0(X280,X279) = k4_xboole_0(k5_xboole_0(X280,X279),k4_xboole_0(X279,X280))) ) | (~spl2_18 | ~spl2_111 | ~spl2_132 | ~spl2_133 | ~spl2_139)),
% 27.78/3.87    inference(forward_demodulation,[],[f35127,f266])).
% 27.78/3.87  fof(f35127,plain,(
% 27.78/3.87    ( ! [X280,X279] : (k4_xboole_0(k5_xboole_0(X280,X279),k4_xboole_0(X279,X280)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X280,X279))) ) | (~spl2_111 | ~spl2_132 | ~spl2_133 | ~spl2_139)),
% 27.78/3.87    inference(backward_demodulation,[],[f31647,f34867])).
% 27.78/3.87  fof(f34867,plain,(
% 27.78/3.87    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k5_xboole_0(X3,X2))) ) | (~spl2_111 | ~spl2_139)),
% 27.78/3.87    inference(superposition,[],[f19753,f31932])).
% 27.78/3.87  fof(f19753,plain,(
% 27.78/3.87    ( ! [X21,X19,X20] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X20,X21),k5_xboole_0(k4_xboole_0(X20,X21),k4_xboole_0(X19,X20)))) ) | ~spl2_111),
% 27.78/3.87    inference(avatar_component_clause,[],[f19752])).
% 27.78/3.87  fof(f31647,plain,(
% 27.78/3.87    ( ! [X280,X279] : (k4_xboole_0(k5_xboole_0(X280,X279),k4_xboole_0(X279,X280)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X279,X280),k5_xboole_0(X280,X279)),k4_xboole_0(X280,X279))) ) | (~spl2_132 | ~spl2_133)),
% 27.78/3.87    inference(superposition,[],[f30386,f30390])).
% 27.78/3.87  fof(f30390,plain,(
% 27.78/3.87    ( ! [X10,X9] : (k4_xboole_0(X9,X10) = k5_xboole_0(k4_xboole_0(X10,X9),k5_xboole_0(X9,X10))) ) | ~spl2_133),
% 27.78/3.87    inference(avatar_component_clause,[],[f30389])).
% 27.78/3.87  fof(f30386,plain,(
% 27.78/3.87    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k5_xboole_0(k4_xboole_0(X4,X3),k5_xboole_0(X4,X3))) ) | ~spl2_132),
% 27.78/3.87    inference(avatar_component_clause,[],[f30385])).
% 27.78/3.87  fof(f43777,plain,(
% 27.78/3.87    spl2_156 | ~spl2_18 | ~spl2_113 | ~spl2_132 | ~spl2_139),
% 27.78/3.87    inference(avatar_split_clause,[],[f35125,f31931,f30385,f19760,f265,f43775])).
% 27.78/3.87  fof(f19760,plain,(
% 27.78/3.87    spl2_113 <=> ! [X63,X62,X61] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X61,X62),k5_xboole_0(k4_xboole_0(X62,X63),k4_xboole_0(X61,X62)))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_113])])).
% 27.78/3.87  fof(f35125,plain,(
% 27.78/3.87    ( ! [X87,X86] : (k4_xboole_0(X87,X86) = k4_xboole_0(k5_xboole_0(X86,X87),k4_xboole_0(X86,X87))) ) | (~spl2_18 | ~spl2_113 | ~spl2_132 | ~spl2_139)),
% 27.78/3.87    inference(forward_demodulation,[],[f35124,f266])).
% 27.78/3.87  fof(f35124,plain,(
% 27.78/3.87    ( ! [X87,X86] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X87,X86)) = k4_xboole_0(k5_xboole_0(X86,X87),k4_xboole_0(X86,X87))) ) | (~spl2_113 | ~spl2_132 | ~spl2_139)),
% 27.78/3.87    inference(backward_demodulation,[],[f30997,f34866])).
% 27.78/3.87  fof(f34866,plain,(
% 27.78/3.87    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X0),k5_xboole_0(X1,X0))) ) | (~spl2_113 | ~spl2_139)),
% 27.78/3.87    inference(superposition,[],[f19761,f31932])).
% 27.78/3.87  fof(f19761,plain,(
% 27.78/3.87    ( ! [X61,X62,X63] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X61,X62),k5_xboole_0(k4_xboole_0(X62,X63),k4_xboole_0(X61,X62)))) ) | ~spl2_113),
% 27.78/3.87    inference(avatar_component_clause,[],[f19760])).
% 27.78/3.87  fof(f30997,plain,(
% 27.78/3.87    ( ! [X87,X86] : (k4_xboole_0(k5_xboole_0(X86,X87),k4_xboole_0(X86,X87)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X86,X87),k5_xboole_0(X86,X87)),k4_xboole_0(X87,X86))) ) | ~spl2_132),
% 27.78/3.87    inference(superposition,[],[f30386,f30386])).
% 27.78/3.87  fof(f35175,plain,(
% 27.78/3.87    spl2_149 | ~spl2_111 | ~spl2_139),
% 27.78/3.87    inference(avatar_split_clause,[],[f34867,f31931,f19752,f35173])).
% 27.78/3.87  fof(f31933,plain,(
% 27.78/3.87    spl2_139 | ~spl2_71 | ~spl2_127),
% 27.78/3.87    inference(avatar_split_clause,[],[f28283,f28163,f1892,f31931])).
% 27.78/3.87  fof(f1892,plain,(
% 27.78/3.87    spl2_71 <=> ! [X13,X12,X14] : k5_xboole_0(X12,X14) = k5_xboole_0(X13,k5_xboole_0(X13,k5_xboole_0(X14,X12)))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).
% 27.78/3.87  fof(f28163,plain,(
% 27.78/3.87    spl2_127 <=> ! [X38,X39] : k5_xboole_0(X39,k5_xboole_0(k4_xboole_0(X39,X38),k4_xboole_0(X38,X39))) = X38),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_127])])).
% 27.78/3.87  fof(f28283,plain,(
% 27.78/3.87    ( ! [X33,X32] : (k5_xboole_0(X32,X33) = k5_xboole_0(k4_xboole_0(X33,X32),k4_xboole_0(X32,X33))) ) | (~spl2_71 | ~spl2_127)),
% 27.78/3.87    inference(superposition,[],[f1893,f28164])).
% 27.78/3.87  fof(f28164,plain,(
% 27.78/3.87    ( ! [X39,X38] : (k5_xboole_0(X39,k5_xboole_0(k4_xboole_0(X39,X38),k4_xboole_0(X38,X39))) = X38) ) | ~spl2_127),
% 27.78/3.87    inference(avatar_component_clause,[],[f28163])).
% 27.78/3.87  fof(f1893,plain,(
% 27.78/3.87    ( ! [X14,X12,X13] : (k5_xboole_0(X12,X14) = k5_xboole_0(X13,k5_xboole_0(X13,k5_xboole_0(X14,X12)))) ) | ~spl2_71),
% 27.78/3.87    inference(avatar_component_clause,[],[f1892])).
% 27.78/3.87  fof(f30391,plain,(
% 27.78/3.87    spl2_133 | ~spl2_51 | ~spl2_130),
% 27.78/3.87    inference(avatar_split_clause,[],[f29594,f28792,f1812,f30389])).
% 27.78/3.87  fof(f1812,plain,(
% 27.78/3.87    spl2_51 <=> ! [X1,X3,X2] : k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(k5_xboole_0(X2,X1),X3)),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).
% 27.78/3.87  fof(f28792,plain,(
% 27.78/3.87    spl2_130 <=> ! [X22,X21] : k4_xboole_0(X22,X21) = k5_xboole_0(k5_xboole_0(X22,k4_xboole_0(X21,X22)),X21)),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_130])])).
% 27.78/3.87  fof(f29594,plain,(
% 27.78/3.87    ( ! [X10,X9] : (k4_xboole_0(X9,X10) = k5_xboole_0(k4_xboole_0(X10,X9),k5_xboole_0(X9,X10))) ) | (~spl2_51 | ~spl2_130)),
% 27.78/3.87    inference(superposition,[],[f28793,f1813])).
% 27.78/3.87  fof(f1813,plain,(
% 27.78/3.87    ( ! [X2,X3,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(k5_xboole_0(X2,X1),X3)) ) | ~spl2_51),
% 27.78/3.87    inference(avatar_component_clause,[],[f1812])).
% 27.78/3.87  fof(f28793,plain,(
% 27.78/3.87    ( ! [X21,X22] : (k4_xboole_0(X22,X21) = k5_xboole_0(k5_xboole_0(X22,k4_xboole_0(X21,X22)),X21)) ) | ~spl2_130),
% 27.78/3.87    inference(avatar_component_clause,[],[f28792])).
% 27.78/3.87  fof(f30387,plain,(
% 27.78/3.87    spl2_132 | ~spl2_88 | ~spl2_130),
% 27.78/3.87    inference(avatar_split_clause,[],[f29591,f28792,f10961,f30385])).
% 27.78/3.87  fof(f10961,plain,(
% 27.78/3.87    spl2_88 <=> ! [X25,X23,X24] : k5_xboole_0(X25,k5_xboole_0(X24,X23)) = k5_xboole_0(k5_xboole_0(X23,X25),X24)),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_88])])).
% 27.78/3.87  fof(f29591,plain,(
% 27.78/3.87    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k5_xboole_0(k4_xboole_0(X4,X3),k5_xboole_0(X4,X3))) ) | (~spl2_88 | ~spl2_130)),
% 27.78/3.87    inference(superposition,[],[f28793,f10962])).
% 27.78/3.87  fof(f10962,plain,(
% 27.78/3.87    ( ! [X24,X23,X25] : (k5_xboole_0(X25,k5_xboole_0(X24,X23)) = k5_xboole_0(k5_xboole_0(X23,X25),X24)) ) | ~spl2_88),
% 27.78/3.87    inference(avatar_component_clause,[],[f10961])).
% 27.78/3.87  fof(f30383,plain,(
% 27.78/3.87    spl2_131 | ~spl2_1 | ~spl2_6 | ~spl2_121 | ~spl2_128),
% 27.78/3.87    inference(avatar_split_clause,[],[f29036,f28784,f26406,f57,f32,f30381])).
% 27.78/3.87  fof(f26406,plain,(
% 27.78/3.87    spl2_121 <=> ! [X84,X85] : k1_xboole_0 = k4_xboole_0(X85,k5_xboole_0(X84,k4_xboole_0(X85,X84)))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_121])])).
% 27.78/3.87  fof(f28784,plain,(
% 27.78/3.87    spl2_128 <=> ! [X55,X56] : k4_xboole_0(X56,X55) = k4_xboole_0(k5_xboole_0(X56,k4_xboole_0(X55,X56)),X55)),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_128])])).
% 27.78/3.87  fof(f29036,plain,(
% 27.78/3.87    ( ! [X6,X5] : (k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),k4_xboole_0(X5,X6)) = X6) ) | (~spl2_1 | ~spl2_6 | ~spl2_121 | ~spl2_128)),
% 27.78/3.87    inference(forward_demodulation,[],[f29035,f33])).
% 27.78/3.87  fof(f29035,plain,(
% 27.78/3.87    ( ! [X6,X5] : (k4_xboole_0(X6,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),k4_xboole_0(X5,X6))) ) | (~spl2_6 | ~spl2_121 | ~spl2_128)),
% 27.78/3.87    inference(forward_demodulation,[],[f28855,f26407])).
% 27.78/3.87  fof(f26407,plain,(
% 27.78/3.87    ( ! [X85,X84] : (k1_xboole_0 = k4_xboole_0(X85,k5_xboole_0(X84,k4_xboole_0(X85,X84)))) ) | ~spl2_121),
% 27.78/3.87    inference(avatar_component_clause,[],[f26406])).
% 27.78/3.87  fof(f28855,plain,(
% 27.78/3.87    ( ! [X6,X5] : (k4_xboole_0(X6,k4_xboole_0(X6,k5_xboole_0(X5,k4_xboole_0(X6,X5)))) = k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),k4_xboole_0(X5,X6))) ) | (~spl2_6 | ~spl2_128)),
% 27.78/3.87    inference(superposition,[],[f58,f28785])).
% 27.78/3.87  fof(f28785,plain,(
% 27.78/3.87    ( ! [X56,X55] : (k4_xboole_0(X56,X55) = k4_xboole_0(k5_xboole_0(X56,k4_xboole_0(X55,X56)),X55)) ) | ~spl2_128),
% 27.78/3.87    inference(avatar_component_clause,[],[f28784])).
% 27.78/3.87  fof(f28794,plain,(
% 27.78/3.87    spl2_130 | ~spl2_1 | ~spl2_27 | ~spl2_54 | ~spl2_56 | ~spl2_121 | ~spl2_127),
% 27.78/3.87    inference(avatar_split_clause,[],[f28627,f28163,f26406,f1832,f1824,f529,f32,f28792])).
% 27.78/3.87  fof(f1824,plain,(
% 27.78/3.87    spl2_54 <=> ! [X13,X14] : k4_xboole_0(X13,X14) = k5_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X13)),X13)),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 27.78/3.87  fof(f1832,plain,(
% 27.78/3.87    spl2_56 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X0,X1)),k5_xboole_0(X2,X1)) = X0),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).
% 27.78/3.87  fof(f28627,plain,(
% 27.78/3.87    ( ! [X21,X22] : (k4_xboole_0(X22,X21) = k5_xboole_0(k5_xboole_0(X22,k4_xboole_0(X21,X22)),X21)) ) | (~spl2_1 | ~spl2_27 | ~spl2_54 | ~spl2_56 | ~spl2_121 | ~spl2_127)),
% 27.78/3.87    inference(backward_demodulation,[],[f26608,f28623])).
% 27.78/3.87  fof(f28623,plain,(
% 27.78/3.87    ( ! [X56,X55] : (k4_xboole_0(X56,X55) = k4_xboole_0(k5_xboole_0(X56,k4_xboole_0(X55,X56)),X55)) ) | (~spl2_1 | ~spl2_54 | ~spl2_56 | ~spl2_121 | ~spl2_127)),
% 27.78/3.87    inference(backward_demodulation,[],[f26627,f28277])).
% 27.78/3.87  fof(f28277,plain,(
% 27.78/3.87    ( ! [X17,X16] : (k4_xboole_0(X16,X17) = k5_xboole_0(X17,k5_xboole_0(X16,k4_xboole_0(X17,X16)))) ) | (~spl2_56 | ~spl2_127)),
% 27.78/3.87    inference(superposition,[],[f1833,f28164])).
% 27.78/3.87  fof(f1833,plain,(
% 27.78/3.87    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X0,X1)),k5_xboole_0(X2,X1)) = X0) ) | ~spl2_56),
% 27.78/3.87    inference(avatar_component_clause,[],[f1832])).
% 27.78/3.87  fof(f26627,plain,(
% 27.78/3.87    ( ! [X56,X55] : (k4_xboole_0(k5_xboole_0(X56,k4_xboole_0(X55,X56)),X55) = k5_xboole_0(X55,k5_xboole_0(X56,k4_xboole_0(X55,X56)))) ) | (~spl2_1 | ~spl2_54 | ~spl2_121)),
% 27.78/3.87    inference(forward_demodulation,[],[f26485,f33])).
% 27.78/3.87  fof(f26485,plain,(
% 27.78/3.87    ( ! [X56,X55] : (k4_xboole_0(k5_xboole_0(X56,k4_xboole_0(X55,X56)),X55) = k5_xboole_0(k4_xboole_0(X55,k1_xboole_0),k5_xboole_0(X56,k4_xboole_0(X55,X56)))) ) | (~spl2_54 | ~spl2_121)),
% 27.78/3.87    inference(superposition,[],[f1825,f26407])).
% 27.78/3.87  fof(f1825,plain,(
% 27.78/3.87    ( ! [X14,X13] : (k4_xboole_0(X13,X14) = k5_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X13)),X13)) ) | ~spl2_54),
% 27.78/3.87    inference(avatar_component_clause,[],[f1824])).
% 27.78/3.87  fof(f26608,plain,(
% 27.78/3.87    ( ! [X21,X22] : (k4_xboole_0(k5_xboole_0(X22,k4_xboole_0(X21,X22)),X21) = k5_xboole_0(k5_xboole_0(X22,k4_xboole_0(X21,X22)),X21)) ) | (~spl2_1 | ~spl2_27 | ~spl2_121)),
% 27.78/3.87    inference(forward_demodulation,[],[f26472,f33])).
% 27.78/3.87  fof(f26472,plain,(
% 27.78/3.87    ( ! [X21,X22] : (k4_xboole_0(k5_xboole_0(X22,k4_xboole_0(X21,X22)),X21) = k5_xboole_0(k5_xboole_0(X22,k4_xboole_0(X21,X22)),k4_xboole_0(X21,k1_xboole_0))) ) | (~spl2_27 | ~spl2_121)),
% 27.78/3.87    inference(superposition,[],[f530,f26407])).
% 27.78/3.87  fof(f28786,plain,(
% 27.78/3.87    spl2_128 | ~spl2_1 | ~spl2_54 | ~spl2_56 | ~spl2_121 | ~spl2_127),
% 27.78/3.87    inference(avatar_split_clause,[],[f28623,f28163,f26406,f1832,f1824,f32,f28784])).
% 27.78/3.87  fof(f28165,plain,(
% 27.78/3.87    spl2_127 | ~spl2_1 | ~spl2_4 | ~spl2_8 | ~spl2_10 | ~spl2_27 | ~spl2_32 | ~spl2_39 | ~spl2_40 | ~spl2_124),
% 27.78/3.87    inference(avatar_split_clause,[],[f28075,f27540,f1076,f1072,f784,f529,f101,f77,f49,f32,f28163])).
% 27.78/3.87  fof(f77,plain,(
% 27.78/3.87    spl2_8 <=> ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1)),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 27.78/3.87  fof(f101,plain,(
% 27.78/3.87    spl2_10 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 27.78/3.87  fof(f1072,plain,(
% 27.78/3.87    spl2_39 <=> ! [X7,X6] : k5_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7)) = X6),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 27.78/3.87  fof(f1076,plain,(
% 27.78/3.87    spl2_40 <=> ! [X34,X36,X35] : k5_xboole_0(X35,X34) = k5_xboole_0(k5_xboole_0(X36,X34),k5_xboole_0(X36,X35))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 27.78/3.87  fof(f27540,plain,(
% 27.78/3.87    spl2_124 <=> ! [X81,X80] : k1_xboole_0 = k4_xboole_0(X80,k5_xboole_0(X81,k5_xboole_0(k4_xboole_0(X81,X80),k4_xboole_0(X80,X81))))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_124])])).
% 27.78/3.87  fof(f28075,plain,(
% 27.78/3.87    ( ! [X39,X38] : (k5_xboole_0(X39,k5_xboole_0(k4_xboole_0(X39,X38),k4_xboole_0(X38,X39))) = X38) ) | (~spl2_1 | ~spl2_4 | ~spl2_8 | ~spl2_10 | ~spl2_27 | ~spl2_32 | ~spl2_39 | ~spl2_40 | ~spl2_124)),
% 27.78/3.87    inference(forward_demodulation,[],[f28074,f33])).
% 27.78/3.87  fof(f28074,plain,(
% 27.78/3.87    ( ! [X39,X38] : (k4_xboole_0(X38,k1_xboole_0) = k5_xboole_0(X39,k5_xboole_0(k4_xboole_0(X39,X38),k4_xboole_0(X38,X39)))) ) | (~spl2_1 | ~spl2_4 | ~spl2_8 | ~spl2_10 | ~spl2_27 | ~spl2_32 | ~spl2_39 | ~spl2_40 | ~spl2_124)),
% 27.78/3.87    inference(forward_demodulation,[],[f28073,f102])).
% 27.78/3.87  fof(f102,plain,(
% 27.78/3.87    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_10),
% 27.78/3.87    inference(avatar_component_clause,[],[f101])).
% 27.78/3.87  fof(f28073,plain,(
% 27.78/3.87    ( ! [X39,X38] : (k5_xboole_0(X39,k5_xboole_0(k4_xboole_0(X39,X38),k4_xboole_0(X38,X39))) = k5_xboole_0(k4_xboole_0(X38,k1_xboole_0),k1_xboole_0)) ) | (~spl2_1 | ~spl2_4 | ~spl2_8 | ~spl2_27 | ~spl2_32 | ~spl2_39 | ~spl2_40 | ~spl2_124)),
% 27.78/3.87    inference(forward_demodulation,[],[f27674,f28061])).
% 27.78/3.87  fof(f28061,plain,(
% 27.78/3.87    ( ! [X19,X18] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X19,k5_xboole_0(k4_xboole_0(X19,X18),k4_xboole_0(X18,X19))),X18)) ) | (~spl2_1 | ~spl2_4 | ~spl2_8 | ~spl2_27 | ~spl2_32 | ~spl2_39 | ~spl2_40 | ~spl2_124)),
% 27.78/3.87    inference(forward_demodulation,[],[f28060,f78])).
% 27.78/3.87  fof(f78,plain,(
% 27.78/3.87    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) ) | ~spl2_8),
% 27.78/3.87    inference(avatar_component_clause,[],[f77])).
% 27.78/3.87  fof(f28060,plain,(
% 27.78/3.87    ( ! [X19,X18] : (k4_xboole_0(k5_xboole_0(X19,k5_xboole_0(k4_xboole_0(X19,X18),k4_xboole_0(X18,X19))),X18) = k5_xboole_0(k4_xboole_0(X18,X19),k4_xboole_0(X18,X19))) ) | (~spl2_1 | ~spl2_4 | ~spl2_27 | ~spl2_32 | ~spl2_39 | ~spl2_40 | ~spl2_124)),
% 27.78/3.87    inference(forward_demodulation,[],[f28059,f1447])).
% 27.78/3.87  fof(f1447,plain,(
% 27.78/3.87    ( ! [X39,X41,X40] : (k5_xboole_0(k4_xboole_0(X40,X39),X41) = k5_xboole_0(k5_xboole_0(X39,k5_xboole_0(k4_xboole_0(X39,X40),X41)),X40)) ) | (~spl2_4 | ~spl2_32 | ~spl2_39 | ~spl2_40)),
% 27.78/3.87    inference(forward_demodulation,[],[f1394,f907])).
% 27.78/3.87  fof(f907,plain,(
% 27.78/3.87    ( ! [X8,X7,X9] : (k5_xboole_0(X7,k5_xboole_0(k4_xboole_0(X7,X8),X9)) = k5_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),X9)) ) | (~spl2_4 | ~spl2_32)),
% 27.78/3.87    inference(superposition,[],[f50,f785])).
% 27.78/3.87  fof(f1394,plain,(
% 27.78/3.87    ( ! [X39,X41,X40] : (k5_xboole_0(k4_xboole_0(X40,X39),X41) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X39,k4_xboole_0(X39,X40)),X41),X40)) ) | (~spl2_39 | ~spl2_40)),
% 27.78/3.87    inference(superposition,[],[f1077,f1073])).
% 27.78/3.87  fof(f1073,plain,(
% 27.78/3.87    ( ! [X6,X7] : (k5_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7)) = X6) ) | ~spl2_39),
% 27.78/3.87    inference(avatar_component_clause,[],[f1072])).
% 27.78/3.87  fof(f1077,plain,(
% 27.78/3.87    ( ! [X35,X36,X34] : (k5_xboole_0(X35,X34) = k5_xboole_0(k5_xboole_0(X36,X34),k5_xboole_0(X36,X35))) ) | ~spl2_40),
% 27.78/3.87    inference(avatar_component_clause,[],[f1076])).
% 27.78/3.87  fof(f28059,plain,(
% 27.78/3.87    ( ! [X19,X18] : (k4_xboole_0(k5_xboole_0(X19,k5_xboole_0(k4_xboole_0(X19,X18),k4_xboole_0(X18,X19))),X18) = k5_xboole_0(k5_xboole_0(X19,k5_xboole_0(k4_xboole_0(X19,X18),k4_xboole_0(X18,X19))),X18)) ) | (~spl2_1 | ~spl2_27 | ~spl2_124)),
% 27.78/3.87    inference(forward_demodulation,[],[f27666,f33])).
% 27.78/3.87  fof(f27666,plain,(
% 27.78/3.87    ( ! [X19,X18] : (k4_xboole_0(k5_xboole_0(X19,k5_xboole_0(k4_xboole_0(X19,X18),k4_xboole_0(X18,X19))),X18) = k5_xboole_0(k5_xboole_0(X19,k5_xboole_0(k4_xboole_0(X19,X18),k4_xboole_0(X18,X19))),k4_xboole_0(X18,k1_xboole_0))) ) | (~spl2_27 | ~spl2_124)),
% 27.78/3.87    inference(superposition,[],[f530,f27541])).
% 27.78/3.87  fof(f27541,plain,(
% 27.78/3.87    ( ! [X80,X81] : (k1_xboole_0 = k4_xboole_0(X80,k5_xboole_0(X81,k5_xboole_0(k4_xboole_0(X81,X80),k4_xboole_0(X80,X81))))) ) | ~spl2_124),
% 27.78/3.87    inference(avatar_component_clause,[],[f27540])).
% 27.78/3.87  fof(f27674,plain,(
% 27.78/3.87    ( ! [X39,X38] : (k5_xboole_0(X39,k5_xboole_0(k4_xboole_0(X39,X38),k4_xboole_0(X38,X39))) = k5_xboole_0(k4_xboole_0(X38,k1_xboole_0),k4_xboole_0(k5_xboole_0(X39,k5_xboole_0(k4_xboole_0(X39,X38),k4_xboole_0(X38,X39))),X38))) ) | (~spl2_39 | ~spl2_124)),
% 27.78/3.87    inference(superposition,[],[f1073,f27541])).
% 27.78/3.87  fof(f27542,plain,(
% 27.78/3.87    spl2_124 | ~spl2_4 | ~spl2_28 | ~spl2_32 | ~spl2_52 | ~spl2_120),
% 27.78/3.87    inference(avatar_split_clause,[],[f26319,f26121,f1816,f784,f533,f49,f27540])).
% 27.78/3.87  fof(f533,plain,(
% 27.78/3.87    spl2_28 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 27.78/3.87  fof(f1816,plain,(
% 27.78/3.87    spl2_52 <=> ! [X9,X8] : k5_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,k4_xboole_0(X9,X8))) = X8),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).
% 27.78/3.87  fof(f26121,plain,(
% 27.78/3.87    spl2_120 <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X3,X2),X2)))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_120])])).
% 27.78/3.87  fof(f26319,plain,(
% 27.78/3.87    ( ! [X80,X81] : (k1_xboole_0 = k4_xboole_0(X80,k5_xboole_0(X81,k5_xboole_0(k4_xboole_0(X81,X80),k4_xboole_0(X80,X81))))) ) | (~spl2_4 | ~spl2_28 | ~spl2_32 | ~spl2_52 | ~spl2_120)),
% 27.78/3.87    inference(forward_demodulation,[],[f26318,f534])).
% 27.78/3.87  fof(f534,plain,(
% 27.78/3.87    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | ~spl2_28),
% 27.78/3.87    inference(avatar_component_clause,[],[f533])).
% 27.78/3.87  fof(f26318,plain,(
% 27.78/3.87    ( ! [X80,X81] : (k1_xboole_0 = k4_xboole_0(X80,k5_xboole_0(X81,k5_xboole_0(k4_xboole_0(X81,X80),k4_xboole_0(X80,k4_xboole_0(X81,k4_xboole_0(X81,X80))))))) ) | (~spl2_4 | ~spl2_32 | ~spl2_52 | ~spl2_120)),
% 27.78/3.87    inference(forward_demodulation,[],[f26158,f907])).
% 27.78/3.87  fof(f26158,plain,(
% 27.78/3.87    ( ! [X80,X81] : (k1_xboole_0 = k4_xboole_0(X80,k5_xboole_0(k4_xboole_0(X81,k4_xboole_0(X81,X80)),k4_xboole_0(X80,k4_xboole_0(X81,k4_xboole_0(X81,X80)))))) ) | (~spl2_52 | ~spl2_120)),
% 27.78/3.87    inference(superposition,[],[f26122,f1817])).
% 27.78/3.87  fof(f1817,plain,(
% 27.78/3.87    ( ! [X8,X9] : (k5_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,k4_xboole_0(X9,X8))) = X8) ) | ~spl2_52),
% 27.78/3.87    inference(avatar_component_clause,[],[f1816])).
% 27.78/3.87  fof(f26122,plain,(
% 27.78/3.87    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X3,X2),X2)))) ) | ~spl2_120),
% 27.78/3.87    inference(avatar_component_clause,[],[f26121])).
% 27.78/3.87  fof(f26408,plain,(
% 27.78/3.87    spl2_121 | ~spl2_22 | ~spl2_120),
% 27.78/3.87    inference(avatar_split_clause,[],[f26160,f26121,f338,f26406])).
% 27.78/3.87  fof(f338,plain,(
% 27.78/3.87    spl2_22 <=> ! [X9,X8] : k5_xboole_0(k5_xboole_0(X9,X8),X9) = X8),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 27.78/3.87  fof(f26160,plain,(
% 27.78/3.87    ( ! [X85,X84] : (k1_xboole_0 = k4_xboole_0(X85,k5_xboole_0(X84,k4_xboole_0(X85,X84)))) ) | (~spl2_22 | ~spl2_120)),
% 27.78/3.87    inference(superposition,[],[f26122,f339])).
% 27.78/3.87  fof(f339,plain,(
% 27.78/3.87    ( ! [X8,X9] : (k5_xboole_0(k5_xboole_0(X9,X8),X9) = X8) ) | ~spl2_22),
% 27.78/3.87    inference(avatar_component_clause,[],[f338])).
% 27.78/3.87  fof(f26123,plain,(
% 27.78/3.87    spl2_120 | ~spl2_23 | ~spl2_32 | ~spl2_38 | ~spl2_53 | ~spl2_97),
% 27.78/3.87    inference(avatar_split_clause,[],[f26016,f17445,f1820,f1068,f784,f342,f26121])).
% 27.78/3.87  fof(f342,plain,(
% 27.78/3.87    spl2_23 <=> ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 27.78/3.87  fof(f1820,plain,(
% 27.78/3.87    spl2_53 <=> ! [X11,X10] : k4_xboole_0(X11,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,X11),X10)),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).
% 27.78/3.87  fof(f17445,plain,(
% 27.78/3.87    spl2_97 <=> ! [X1,X0,X2] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,k5_xboole_0(X0,X1)))))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_97])])).
% 27.78/3.87  fof(f26016,plain,(
% 27.78/3.87    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X3,X2),X2)))) ) | (~spl2_23 | ~spl2_32 | ~spl2_38 | ~spl2_53 | ~spl2_97)),
% 27.78/3.87    inference(forward_demodulation,[],[f26015,f343])).
% 27.78/3.87  fof(f343,plain,(
% 27.78/3.87    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)) ) | ~spl2_23),
% 27.78/3.87    inference(avatar_component_clause,[],[f342])).
% 27.78/3.87  fof(f26015,plain,(
% 27.78/3.87    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(k4_xboole_0(k5_xboole_0(X3,X2),X2),X2))) ) | (~spl2_32 | ~spl2_38 | ~spl2_53 | ~spl2_97)),
% 27.78/3.87    inference(forward_demodulation,[],[f25730,f3435])).
% 27.78/3.87  fof(f3435,plain,(
% 27.78/3.87    ( ! [X80,X81,X79] : (k5_xboole_0(k4_xboole_0(k5_xboole_0(X79,X80),X81),X80) = k5_xboole_0(X79,k4_xboole_0(X81,k4_xboole_0(X81,k5_xboole_0(X79,X80))))) ) | (~spl2_38 | ~spl2_53)),
% 27.78/3.87    inference(superposition,[],[f1069,f1821])).
% 27.78/3.87  fof(f1821,plain,(
% 27.78/3.87    ( ! [X10,X11] : (k4_xboole_0(X11,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,X11),X10)) ) | ~spl2_53),
% 27.78/3.87    inference(avatar_component_clause,[],[f1820])).
% 27.78/3.87  fof(f25730,plain,(
% 27.78/3.87    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X3,X2)))))) ) | (~spl2_32 | ~spl2_97)),
% 27.78/3.87    inference(superposition,[],[f17446,f785])).
% 27.78/3.87  fof(f17446,plain,(
% 27.78/3.87    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,k5_xboole_0(X0,X1)))))) ) | ~spl2_97),
% 27.78/3.87    inference(avatar_component_clause,[],[f17445])).
% 27.78/3.87  fof(f23970,plain,(
% 27.78/3.87    spl2_117 | ~spl2_34 | ~spl2_116),
% 27.78/3.87    inference(avatar_split_clause,[],[f23730,f23692,f792,f23968])).
% 27.78/3.87  fof(f792,plain,(
% 27.78/3.87    spl2_34 <=> ! [X5,X4] : k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,X4)) = X4),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 27.78/3.87  fof(f23692,plain,(
% 27.78/3.87    spl2_116 <=> ! [X11,X10,X12] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),X10)),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_116])])).
% 27.78/3.87  fof(f23730,plain,(
% 27.78/3.87    ( ! [X121,X122,X120] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X120,X122),k5_xboole_0(X120,k4_xboole_0(X121,X120)))) ) | (~spl2_34 | ~spl2_116)),
% 27.78/3.87    inference(superposition,[],[f23693,f793])).
% 27.78/3.87  fof(f793,plain,(
% 27.78/3.87    ( ! [X4,X5] : (k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,X4)) = X4) ) | ~spl2_34),
% 27.78/3.87    inference(avatar_component_clause,[],[f792])).
% 27.78/3.87  fof(f23693,plain,(
% 27.78/3.87    ( ! [X12,X10,X11] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),X10)) ) | ~spl2_116),
% 27.78/3.87    inference(avatar_component_clause,[],[f23692])).
% 27.78/3.87  fof(f23694,plain,(
% 27.78/3.87    spl2_116 | ~spl2_25 | ~spl2_110),
% 27.78/3.87    inference(avatar_split_clause,[],[f23366,f19748,f460,f23692])).
% 27.78/3.87  fof(f460,plain,(
% 27.78/3.87    spl2_25 <=> ! [X1,X2] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1)),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 27.78/3.87  fof(f19748,plain,(
% 27.78/3.87    spl2_110 <=> ! [X53,X55,X52,X54] : k4_xboole_0(X52,X53) = k4_xboole_0(k4_xboole_0(X52,X53),k4_xboole_0(k4_xboole_0(X53,X54),X55))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_110])])).
% 27.78/3.87  fof(f23366,plain,(
% 27.78/3.87    ( ! [X12,X10,X11] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),X10)) ) | (~spl2_25 | ~spl2_110)),
% 27.78/3.87    inference(superposition,[],[f19749,f461])).
% 27.78/3.87  fof(f461,plain,(
% 27.78/3.87    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1)) ) | ~spl2_25),
% 27.78/3.87    inference(avatar_component_clause,[],[f460])).
% 27.78/3.87  fof(f19749,plain,(
% 27.78/3.87    ( ! [X54,X52,X55,X53] : (k4_xboole_0(X52,X53) = k4_xboole_0(k4_xboole_0(X52,X53),k4_xboole_0(k4_xboole_0(X53,X54),X55))) ) | ~spl2_110),
% 27.78/3.87    inference(avatar_component_clause,[],[f19748])).
% 27.78/3.87  fof(f19762,plain,(
% 27.78/3.87    spl2_113 | ~spl2_33 | ~spl2_81),
% 27.78/3.87    inference(avatar_split_clause,[],[f10710,f10635,f788,f19760])).
% 27.78/3.87  fof(f788,plain,(
% 27.78/3.87    spl2_33 <=> ! [X13,X12] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X13,X12),k5_xboole_0(X12,k4_xboole_0(X13,X12)))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 27.78/3.87  fof(f10710,plain,(
% 27.78/3.87    ( ! [X61,X62,X63] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X61,X62),k5_xboole_0(k4_xboole_0(X62,X63),k4_xboole_0(X61,X62)))) ) | (~spl2_33 | ~spl2_81)),
% 27.78/3.87    inference(superposition,[],[f789,f10636])).
% 27.78/3.87  fof(f789,plain,(
% 27.78/3.87    ( ! [X12,X13] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X13,X12),k5_xboole_0(X12,k4_xboole_0(X13,X12)))) ) | ~spl2_33),
% 27.78/3.87    inference(avatar_component_clause,[],[f788])).
% 27.78/3.87  fof(f19758,plain,(
% 27.78/3.87    spl2_112 | ~spl2_1 | ~spl2_2 | ~spl2_65),
% 27.78/3.87    inference(avatar_split_clause,[],[f4074,f1868,f36,f32,f19756])).
% 27.78/3.87  fof(f36,plain,(
% 27.78/3.87    spl2_2 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 27.78/3.87  fof(f4074,plain,(
% 27.78/3.87    ( ! [X21,X22,X20] : (k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(k5_xboole_0(X20,k4_xboole_0(X21,X20)),X22))) = k4_xboole_0(X20,X22)) ) | (~spl2_1 | ~spl2_2 | ~spl2_65)),
% 27.78/3.87    inference(forward_demodulation,[],[f3983,f33])).
% 27.78/3.87  fof(f3983,plain,(
% 27.78/3.87    ( ! [X21,X22,X20] : (k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(k5_xboole_0(X20,k4_xboole_0(X21,X20)),X22))) = k4_xboole_0(k4_xboole_0(X20,k1_xboole_0),X22)) ) | (~spl2_2 | ~spl2_65)),
% 27.78/3.87    inference(superposition,[],[f1869,f37])).
% 27.78/3.87  fof(f37,plain,(
% 27.78/3.87    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) ) | ~spl2_2),
% 27.78/3.87    inference(avatar_component_clause,[],[f36])).
% 27.78/3.87  fof(f19754,plain,(
% 27.78/3.87    spl2_111 | ~spl2_2 | ~spl2_81),
% 27.78/3.87    inference(avatar_split_clause,[],[f10696,f10635,f36,f19752])).
% 27.78/3.87  fof(f10696,plain,(
% 27.78/3.87    ( ! [X21,X19,X20] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X20,X21),k5_xboole_0(k4_xboole_0(X20,X21),k4_xboole_0(X19,X20)))) ) | (~spl2_2 | ~spl2_81)),
% 27.78/3.87    inference(superposition,[],[f37,f10636])).
% 27.78/3.87  fof(f19750,plain,(
% 27.78/3.87    spl2_110 | ~spl2_81),
% 27.78/3.87    inference(avatar_split_clause,[],[f10659,f10635,f19748])).
% 27.78/3.87  fof(f10659,plain,(
% 27.78/3.87    ( ! [X54,X52,X55,X53] : (k4_xboole_0(X52,X53) = k4_xboole_0(k4_xboole_0(X52,X53),k4_xboole_0(k4_xboole_0(X53,X54),X55))) ) | ~spl2_81),
% 27.78/3.87    inference(superposition,[],[f10636,f10636])).
% 27.78/3.87  fof(f17447,plain,(
% 27.78/3.87    spl2_97 | ~spl2_2 | ~spl2_4),
% 27.78/3.87    inference(avatar_split_clause,[],[f65,f49,f36,f17445])).
% 27.78/3.87  fof(f65,plain,(
% 27.78/3.87    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,k5_xboole_0(X0,X1)))))) ) | (~spl2_2 | ~spl2_4)),
% 27.78/3.87    inference(superposition,[],[f37,f50])).
% 27.78/3.87  fof(f10963,plain,(
% 27.78/3.87    spl2_88 | ~spl2_20 | ~spl2_49),
% 27.78/3.87    inference(avatar_split_clause,[],[f2555,f1804,f309,f10961])).
% 27.78/3.87  fof(f309,plain,(
% 27.78/3.87    spl2_20 <=> ! [X7,X6] : k5_xboole_0(X7,k5_xboole_0(X6,X7)) = X6),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 27.78/3.87  fof(f1804,plain,(
% 27.78/3.87    spl2_49 <=> ! [X9,X11,X10] : k5_xboole_0(X10,X11) = k5_xboole_0(k5_xboole_0(X9,X10),k5_xboole_0(X9,X11))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).
% 27.78/3.87  fof(f2555,plain,(
% 27.78/3.87    ( ! [X24,X23,X25] : (k5_xboole_0(X25,k5_xboole_0(X24,X23)) = k5_xboole_0(k5_xboole_0(X23,X25),X24)) ) | (~spl2_20 | ~spl2_49)),
% 27.78/3.87    inference(superposition,[],[f1805,f310])).
% 27.78/3.87  fof(f310,plain,(
% 27.78/3.87    ( ! [X6,X7] : (k5_xboole_0(X7,k5_xboole_0(X6,X7)) = X6) ) | ~spl2_20),
% 27.78/3.87    inference(avatar_component_clause,[],[f309])).
% 27.78/3.87  fof(f1805,plain,(
% 27.78/3.87    ( ! [X10,X11,X9] : (k5_xboole_0(X10,X11) = k5_xboole_0(k5_xboole_0(X9,X10),k5_xboole_0(X9,X11))) ) | ~spl2_49),
% 27.78/3.87    inference(avatar_component_clause,[],[f1804])).
% 27.78/3.87  fof(f10637,plain,(
% 27.78/3.87    spl2_81 | ~spl2_75 | ~spl2_78),
% 27.78/3.87    inference(avatar_split_clause,[],[f4653,f4643,f4280,f10635])).
% 27.78/3.87  fof(f4280,plain,(
% 27.78/3.87    spl2_75 <=> ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_75])])).
% 27.78/3.87  fof(f4643,plain,(
% 27.78/3.87    spl2_78 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = X0),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).
% 27.78/3.87  fof(f4653,plain,(
% 27.78/3.87    ( ! [X21,X22,X20] : (k4_xboole_0(X21,X20) = k4_xboole_0(k4_xboole_0(X21,X20),k4_xboole_0(X20,X22))) ) | (~spl2_75 | ~spl2_78)),
% 27.78/3.87    inference(superposition,[],[f4644,f4281])).
% 27.78/3.87  fof(f4281,plain,(
% 27.78/3.87    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1) ) | ~spl2_75),
% 27.78/3.87    inference(avatar_component_clause,[],[f4280])).
% 27.78/3.87  fof(f4644,plain,(
% 27.78/3.87    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = X0) ) | ~spl2_78),
% 27.78/3.87    inference(avatar_component_clause,[],[f4643])).
% 27.78/3.87  fof(f4645,plain,(
% 27.78/3.87    spl2_78 | ~spl2_5 | ~spl2_10 | ~spl2_77),
% 27.78/3.87    inference(avatar_split_clause,[],[f4596,f4471,f101,f53,f4643])).
% 27.78/3.87  fof(f4471,plain,(
% 27.78/3.87    spl2_77 <=> ! [X32,X31,X33] : k1_xboole_0 = k4_xboole_0(X31,k4_xboole_0(X31,k4_xboole_0(k4_xboole_0(X32,X31),X33)))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).
% 27.78/3.87  fof(f4596,plain,(
% 27.78/3.87    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = X0) ) | (~spl2_5 | ~spl2_10 | ~spl2_77)),
% 27.78/3.87    inference(forward_demodulation,[],[f4516,f102])).
% 27.78/3.87  fof(f4516,plain,(
% 27.78/3.87    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2))) ) | (~spl2_5 | ~spl2_77)),
% 27.78/3.87    inference(superposition,[],[f54,f4472])).
% 27.78/3.87  fof(f4472,plain,(
% 27.78/3.87    ( ! [X33,X31,X32] : (k1_xboole_0 = k4_xboole_0(X31,k4_xboole_0(X31,k4_xboole_0(k4_xboole_0(X32,X31),X33)))) ) | ~spl2_77),
% 27.78/3.87    inference(avatar_component_clause,[],[f4471])).
% 27.78/3.87  fof(f4473,plain,(
% 27.78/3.87    spl2_77 | ~spl2_13 | ~spl2_65 | ~spl2_74),
% 27.78/3.87    inference(avatar_split_clause,[],[f4243,f4154,f1868,f143,f4471])).
% 27.78/3.87  fof(f143,plain,(
% 27.78/3.87    spl2_13 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 27.78/3.87  fof(f4154,plain,(
% 27.78/3.87    spl2_74 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_74])])).
% 27.78/3.87  fof(f4243,plain,(
% 27.78/3.87    ( ! [X33,X31,X32] : (k1_xboole_0 = k4_xboole_0(X31,k4_xboole_0(X31,k4_xboole_0(k4_xboole_0(X32,X31),X33)))) ) | (~spl2_13 | ~spl2_65 | ~spl2_74)),
% 27.78/3.87    inference(forward_demodulation,[],[f4192,f144])).
% 27.78/3.87  fof(f144,plain,(
% 27.78/3.87    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl2_13),
% 27.78/3.87    inference(avatar_component_clause,[],[f143])).
% 27.78/3.87  fof(f4192,plain,(
% 27.78/3.87    ( ! [X33,X31,X32] : (k4_xboole_0(k1_xboole_0,X33) = k4_xboole_0(X31,k4_xboole_0(X31,k4_xboole_0(k4_xboole_0(X32,X31),X33)))) ) | (~spl2_65 | ~spl2_74)),
% 27.78/3.87    inference(superposition,[],[f1869,f4155])).
% 27.78/3.87  fof(f4155,plain,(
% 27.78/3.87    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) ) | ~spl2_74),
% 27.78/3.87    inference(avatar_component_clause,[],[f4154])).
% 27.78/3.87  fof(f4381,plain,(
% 27.78/3.87    spl2_76 | ~spl2_10 | ~spl2_27 | ~spl2_74),
% 27.78/3.87    inference(avatar_split_clause,[],[f4235,f4154,f529,f101,f4379])).
% 27.78/3.87  fof(f4235,plain,(
% 27.78/3.87    ( ! [X14,X13] : (k4_xboole_0(X14,X13) = k4_xboole_0(k4_xboole_0(X14,X13),X13)) ) | (~spl2_10 | ~spl2_27 | ~spl2_74)),
% 27.78/3.87    inference(forward_demodulation,[],[f4185,f102])).
% 27.78/3.87  fof(f4185,plain,(
% 27.78/3.87    ( ! [X14,X13] : (k4_xboole_0(k4_xboole_0(X14,X13),X13) = k5_xboole_0(k4_xboole_0(X14,X13),k1_xboole_0)) ) | (~spl2_27 | ~spl2_74)),
% 27.78/3.87    inference(superposition,[],[f530,f4155])).
% 27.78/3.87  fof(f4282,plain,(
% 27.78/3.87    spl2_75 | ~spl2_5 | ~spl2_10 | ~spl2_74),
% 27.78/3.87    inference(avatar_split_clause,[],[f4231,f4154,f101,f53,f4280])).
% 27.78/3.87  fof(f4231,plain,(
% 27.78/3.87    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1) ) | (~spl2_5 | ~spl2_10 | ~spl2_74)),
% 27.78/3.87    inference(forward_demodulation,[],[f4181,f102])).
% 27.78/3.87  fof(f4181,plain,(
% 27.78/3.87    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X2,X1))) ) | (~spl2_5 | ~spl2_74)),
% 27.78/3.87    inference(superposition,[],[f54,f4155])).
% 27.78/3.87  fof(f4156,plain,(
% 27.78/3.87    spl2_74 | ~spl2_24 | ~spl2_65),
% 27.78/3.87    inference(avatar_split_clause,[],[f4001,f1868,f430,f4154])).
% 27.78/3.87  fof(f430,plain,(
% 27.78/3.87    spl2_24 <=> ! [X13,X12] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X13)),X12)),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 27.78/3.87  fof(f4001,plain,(
% 27.78/3.87    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) ) | (~spl2_24 | ~spl2_65)),
% 27.78/3.87    inference(superposition,[],[f1869,f431])).
% 27.78/3.87  fof(f431,plain,(
% 27.78/3.87    ( ! [X12,X13] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X13)),X12)) ) | ~spl2_24),
% 27.78/3.87    inference(avatar_component_clause,[],[f430])).
% 27.78/3.87  fof(f1894,plain,(
% 27.78/3.87    spl2_71 | ~spl2_4 | ~spl2_23 | ~spl2_38),
% 27.78/3.87    inference(avatar_split_clause,[],[f1236,f1068,f342,f49,f1892])).
% 27.78/3.87  fof(f1236,plain,(
% 27.78/3.87    ( ! [X14,X12,X13] : (k5_xboole_0(X12,X14) = k5_xboole_0(X13,k5_xboole_0(X13,k5_xboole_0(X14,X12)))) ) | (~spl2_4 | ~spl2_23 | ~spl2_38)),
% 27.78/3.87    inference(forward_demodulation,[],[f1209,f50])).
% 27.78/3.87  fof(f1209,plain,(
% 27.78/3.87    ( ! [X14,X12,X13] : (k5_xboole_0(X12,X14) = k5_xboole_0(X13,k5_xboole_0(k5_xboole_0(X13,X14),X12))) ) | (~spl2_23 | ~spl2_38)),
% 27.78/3.87    inference(superposition,[],[f1069,f343])).
% 27.78/3.87  fof(f1870,plain,(
% 27.78/3.87    spl2_65),
% 27.78/3.87    inference(avatar_split_clause,[],[f30,f1868])).
% 27.78/3.87  fof(f30,plain,(
% 27.78/3.87    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 27.78/3.87    inference(definition_unfolding,[],[f24,f20,f20])).
% 27.78/3.87  fof(f20,plain,(
% 27.78/3.87    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 27.78/3.87    inference(cnf_transformation,[],[f6])).
% 27.78/3.87  fof(f6,axiom,(
% 27.78/3.87    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 27.78/3.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 27.78/3.87  fof(f24,plain,(
% 27.78/3.87    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 27.78/3.87    inference(cnf_transformation,[],[f7])).
% 27.78/3.87  fof(f7,axiom,(
% 27.78/3.87    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 27.78/3.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 27.78/3.87  fof(f1834,plain,(
% 27.78/3.87    spl2_56 | ~spl2_22 | ~spl2_31),
% 27.78/3.87    inference(avatar_split_clause,[],[f809,f780,f338,f1832])).
% 27.78/3.87  fof(f780,plain,(
% 27.78/3.87    spl2_31 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 27.78/3.87  fof(f809,plain,(
% 27.78/3.87    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X0,X1)),k5_xboole_0(X2,X1)) = X0) ) | (~spl2_22 | ~spl2_31)),
% 27.78/3.87    inference(superposition,[],[f781,f339])).
% 27.78/3.87  fof(f781,plain,(
% 27.78/3.87    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2) ) | ~spl2_31),
% 27.78/3.87    inference(avatar_component_clause,[],[f780])).
% 27.78/3.87  fof(f1826,plain,(
% 27.78/3.87    spl2_54 | ~spl2_22 | ~spl2_29),
% 27.78/3.87    inference(avatar_split_clause,[],[f670,f537,f338,f1824])).
% 27.78/3.87  fof(f537,plain,(
% 27.78/3.87    spl2_29 <=> ! [X3,X2] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,X3))),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 27.78/3.87  fof(f670,plain,(
% 27.78/3.87    ( ! [X14,X13] : (k4_xboole_0(X13,X14) = k5_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X13)),X13)) ) | (~spl2_22 | ~spl2_29)),
% 27.78/3.87    inference(superposition,[],[f339,f538])).
% 27.78/3.87  fof(f538,plain,(
% 27.78/3.87    ( ! [X2,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,X3))) ) | ~spl2_29),
% 27.78/3.87    inference(avatar_component_clause,[],[f537])).
% 27.78/3.87  fof(f1822,plain,(
% 27.78/3.87    spl2_53 | ~spl2_22 | ~spl2_27),
% 27.78/3.87    inference(avatar_split_clause,[],[f560,f529,f338,f1820])).
% 27.78/3.87  fof(f560,plain,(
% 27.78/3.87    ( ! [X10,X11] : (k4_xboole_0(X11,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,X11),X10)) ) | (~spl2_22 | ~spl2_27)),
% 27.78/3.87    inference(superposition,[],[f339,f530])).
% 27.78/3.87  fof(f1818,plain,(
% 27.78/3.87    spl2_52 | ~spl2_21 | ~spl2_27),
% 27.78/3.87    inference(avatar_split_clause,[],[f559,f529,f334,f1816])).
% 27.78/3.87  fof(f334,plain,(
% 27.78/3.87    spl2_21 <=> ! [X7,X6] : k5_xboole_0(k5_xboole_0(X6,X7),X7) = X6),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 27.78/3.87  fof(f559,plain,(
% 27.78/3.87    ( ! [X8,X9] : (k5_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,k4_xboole_0(X9,X8))) = X8) ) | (~spl2_21 | ~spl2_27)),
% 27.78/3.87    inference(superposition,[],[f335,f530])).
% 27.78/3.87  fof(f335,plain,(
% 27.78/3.87    ( ! [X6,X7] : (k5_xboole_0(k5_xboole_0(X6,X7),X7) = X6) ) | ~spl2_21),
% 27.78/3.87    inference(avatar_component_clause,[],[f334])).
% 27.78/3.87  fof(f1814,plain,(
% 27.78/3.87    spl2_51 | ~spl2_4 | ~spl2_23),
% 27.78/3.87    inference(avatar_split_clause,[],[f409,f342,f49,f1812])).
% 27.78/3.87  fof(f409,plain,(
% 27.78/3.87    ( ! [X2,X3,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(k5_xboole_0(X2,X1),X3)) ) | (~spl2_4 | ~spl2_23)),
% 27.78/3.87    inference(superposition,[],[f50,f343])).
% 27.78/3.87  fof(f1806,plain,(
% 27.78/3.87    spl2_49 | ~spl2_4 | ~spl2_22),
% 27.78/3.87    inference(avatar_split_clause,[],[f374,f338,f49,f1804])).
% 27.78/3.87  fof(f374,plain,(
% 27.78/3.87    ( ! [X10,X11,X9] : (k5_xboole_0(X10,X11) = k5_xboole_0(k5_xboole_0(X9,X10),k5_xboole_0(X9,X11))) ) | (~spl2_4 | ~spl2_22)),
% 27.78/3.87    inference(superposition,[],[f50,f339])).
% 27.78/3.87  fof(f1078,plain,(
% 27.78/3.87    spl2_40 | ~spl2_20 | ~spl2_31),
% 27.78/3.87    inference(avatar_split_clause,[],[f820,f780,f309,f1076])).
% 27.78/3.87  fof(f820,plain,(
% 27.78/3.87    ( ! [X35,X36,X34] : (k5_xboole_0(X35,X34) = k5_xboole_0(k5_xboole_0(X36,X34),k5_xboole_0(X36,X35))) ) | (~spl2_20 | ~spl2_31)),
% 27.78/3.87    inference(superposition,[],[f781,f310])).
% 27.78/3.87  fof(f1074,plain,(
% 27.78/3.87    spl2_39 | ~spl2_20 | ~spl2_27),
% 27.78/3.87    inference(avatar_split_clause,[],[f558,f529,f309,f1072])).
% 27.78/3.87  fof(f558,plain,(
% 27.78/3.87    ( ! [X6,X7] : (k5_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7)) = X6) ) | (~spl2_20 | ~spl2_27)),
% 27.78/3.87    inference(superposition,[],[f310,f530])).
% 27.78/3.87  fof(f1070,plain,(
% 27.78/3.87    spl2_38 | ~spl2_4 | ~spl2_20),
% 27.78/3.87    inference(avatar_split_clause,[],[f330,f309,f49,f1068])).
% 27.78/3.87  fof(f330,plain,(
% 27.78/3.87    ( ! [X4,X5,X3] : (k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X5)))) ) | (~spl2_4 | ~spl2_20)),
% 27.78/3.87    inference(forward_demodulation,[],[f322,f50])).
% 27.78/3.87  fof(f322,plain,(
% 27.78/3.87    ( ! [X4,X5,X3] : (k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X4,X3),X5))) ) | (~spl2_4 | ~spl2_20)),
% 27.78/3.87    inference(superposition,[],[f50,f310])).
% 27.78/3.87  fof(f883,plain,(
% 27.78/3.87    ~spl2_35),
% 27.78/3.87    inference(avatar_split_clause,[],[f26,f880])).
% 27.78/3.87  fof(f26,plain,(
% 27.78/3.87    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 27.78/3.87    inference(definition_unfolding,[],[f15,f19,f20])).
% 27.78/3.87  fof(f19,plain,(
% 27.78/3.87    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 27.78/3.87    inference(cnf_transformation,[],[f9])).
% 27.78/3.87  fof(f9,axiom,(
% 27.78/3.87    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 27.78/3.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 27.78/3.87  fof(f15,plain,(
% 27.78/3.87    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 27.78/3.87    inference(cnf_transformation,[],[f14])).
% 27.78/3.87  fof(f14,plain,(
% 27.78/3.87    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 27.78/3.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).
% 27.78/3.87  fof(f13,plain,(
% 27.78/3.87    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 27.78/3.87    introduced(choice_axiom,[])).
% 27.78/3.87  fof(f12,plain,(
% 27.78/3.87    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 27.78/3.87    inference(ennf_transformation,[],[f11])).
% 27.78/3.87  fof(f11,negated_conjecture,(
% 27.78/3.87    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 27.78/3.87    inference(negated_conjecture,[],[f10])).
% 27.78/3.87  fof(f10,conjecture,(
% 27.78/3.87    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 27.78/3.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
% 27.78/3.87  fof(f794,plain,(
% 27.78/3.87    spl2_34 | ~spl2_1 | ~spl2_2 | ~spl2_6 | ~spl2_30),
% 27.78/3.87    inference(avatar_split_clause,[],[f765,f714,f57,f36,f32,f792])).
% 27.78/3.87  fof(f714,plain,(
% 27.78/3.87    spl2_30 <=> ! [X7,X8] : k4_xboole_0(X8,X7) = k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X8,X7)),X7)),
% 27.78/3.87    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 27.78/3.87  fof(f765,plain,(
% 27.78/3.87    ( ! [X4,X5] : (k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,X4)) = X4) ) | (~spl2_1 | ~spl2_2 | ~spl2_6 | ~spl2_30)),
% 27.78/3.87    inference(forward_demodulation,[],[f764,f33])).
% 27.78/3.87  fof(f764,plain,(
% 27.78/3.87    ( ! [X4,X5] : (k4_xboole_0(X4,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,X4))) ) | (~spl2_2 | ~spl2_6 | ~spl2_30)),
% 27.78/3.87    inference(forward_demodulation,[],[f736,f37])).
% 27.78/3.87  fof(f736,plain,(
% 27.78/3.87    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,k5_xboole_0(X4,k4_xboole_0(X5,X4)))) = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,X4))) ) | (~spl2_6 | ~spl2_30)),
% 27.78/3.87    inference(superposition,[],[f58,f715])).
% 27.78/3.87  fof(f715,plain,(
% 27.78/3.87    ( ! [X8,X7] : (k4_xboole_0(X8,X7) = k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X8,X7)),X7)) ) | ~spl2_30),
% 27.78/3.87    inference(avatar_component_clause,[],[f714])).
% 27.78/3.87  fof(f790,plain,(
% 27.78/3.87    spl2_33 | ~spl2_25 | ~spl2_30),
% 27.78/3.87    inference(avatar_split_clause,[],[f740,f714,f460,f788])).
% 27.78/3.87  fof(f740,plain,(
% 27.78/3.87    ( ! [X12,X13] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X13,X12),k5_xboole_0(X12,k4_xboole_0(X13,X12)))) ) | (~spl2_25 | ~spl2_30)),
% 27.78/3.87    inference(superposition,[],[f461,f715])).
% 27.78/3.87  fof(f786,plain,(
% 27.78/3.87    spl2_32 | ~spl2_5 | ~spl2_8 | ~spl2_10 | ~spl2_15),
% 27.78/3.87    inference(avatar_split_clause,[],[f246,f171,f101,f77,f53,f784])).
% 27.78/3.88  fof(f171,plain,(
% 27.78/3.88    spl2_15 <=> ! [X1,X0] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))),
% 27.78/3.88    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 27.78/3.88  fof(f246,plain,(
% 27.78/3.88    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))) ) | (~spl2_5 | ~spl2_8 | ~spl2_10 | ~spl2_15)),
% 27.78/3.88    inference(forward_demodulation,[],[f222,f238])).
% 27.78/3.88  fof(f238,plain,(
% 27.78/3.88    ( ! [X3] : (k5_xboole_0(k1_xboole_0,X3) = X3) ) | (~spl2_8 | ~spl2_10 | ~spl2_15)),
% 27.78/3.88    inference(forward_demodulation,[],[f221,f102])).
% 27.78/3.88  fof(f221,plain,(
% 27.78/3.88    ( ! [X3] : (k5_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X3,k1_xboole_0)) ) | (~spl2_8 | ~spl2_15)),
% 27.78/3.88    inference(superposition,[],[f172,f78])).
% 27.78/3.88  fof(f172,plain,(
% 27.78/3.88    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) ) | ~spl2_15),
% 27.78/3.88    inference(avatar_component_clause,[],[f171])).
% 27.78/3.88  fof(f222,plain,(
% 27.78/3.88    ( ! [X4,X5] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X4,k4_xboole_0(X4,X5))) = k5_xboole_0(X4,k4_xboole_0(X4,X5))) ) | (~spl2_5 | ~spl2_15)),
% 27.78/3.88    inference(superposition,[],[f172,f54])).
% 27.78/3.88  fof(f782,plain,(
% 27.78/3.88    spl2_31 | ~spl2_4 | ~spl2_8 | ~spl2_10 | ~spl2_15),
% 27.78/3.88    inference(avatar_split_clause,[],[f244,f171,f101,f77,f49,f780])).
% 27.78/3.88  fof(f244,plain,(
% 27.78/3.88    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2) ) | (~spl2_4 | ~spl2_8 | ~spl2_10 | ~spl2_15)),
% 27.78/3.88    inference(backward_demodulation,[],[f220,f238])).
% 27.78/3.88  fof(f220,plain,(
% 27.78/3.88    ( ! [X2,X0,X1] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2)))) ) | (~spl2_4 | ~spl2_15)),
% 27.78/3.88    inference(superposition,[],[f172,f50])).
% 27.78/3.88  fof(f716,plain,(
% 27.78/3.88    spl2_30 | ~spl2_1 | ~spl2_2 | ~spl2_22 | ~spl2_27),
% 27.78/3.88    inference(avatar_split_clause,[],[f570,f529,f338,f36,f32,f714])).
% 27.78/3.88  fof(f570,plain,(
% 27.78/3.88    ( ! [X8,X7] : (k4_xboole_0(X8,X7) = k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X8,X7)),X7)) ) | (~spl2_1 | ~spl2_2 | ~spl2_22 | ~spl2_27)),
% 27.78/3.88    inference(forward_demodulation,[],[f569,f339])).
% 27.78/3.88  fof(f569,plain,(
% 27.78/3.88    ( ! [X8,X7] : (k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X8,X7)),X7) = k5_xboole_0(k5_xboole_0(X7,k4_xboole_0(X8,X7)),X7)) ) | (~spl2_1 | ~spl2_2 | ~spl2_27)),
% 27.78/3.88    inference(forward_demodulation,[],[f544,f33])).
% 27.78/3.88  fof(f544,plain,(
% 27.78/3.88    ( ! [X8,X7] : (k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X8,X7)),X7) = k5_xboole_0(k5_xboole_0(X7,k4_xboole_0(X8,X7)),k4_xboole_0(X7,k1_xboole_0))) ) | (~spl2_2 | ~spl2_27)),
% 27.78/3.88    inference(superposition,[],[f530,f37])).
% 27.78/3.88  fof(f539,plain,(
% 27.78/3.88    spl2_29 | ~spl2_5 | ~spl2_6 | ~spl2_7),
% 27.78/3.88    inference(avatar_split_clause,[],[f395,f61,f57,f53,f537])).
% 27.78/3.88  fof(f61,plain,(
% 27.78/3.88    spl2_7 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 27.78/3.88    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 27.78/3.88  fof(f395,plain,(
% 27.78/3.88    ( ! [X2,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,X3))) ) | (~spl2_5 | ~spl2_6 | ~spl2_7)),
% 27.78/3.88    inference(backward_demodulation,[],[f135,f383])).
% 27.78/3.88  fof(f383,plain,(
% 27.78/3.88    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | (~spl2_6 | ~spl2_7)),
% 27.78/3.88    inference(superposition,[],[f62,f58])).
% 27.78/3.88  fof(f62,plain,(
% 27.78/3.88    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl2_7),
% 27.78/3.88    inference(avatar_component_clause,[],[f61])).
% 27.78/3.88  fof(f135,plain,(
% 27.78/3.88    ( ! [X2,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))))) ) | (~spl2_5 | ~spl2_6)),
% 27.78/3.88    inference(superposition,[],[f54,f58])).
% 27.78/3.88  fof(f535,plain,(
% 27.78/3.88    spl2_28 | ~spl2_6 | ~spl2_7),
% 27.78/3.88    inference(avatar_split_clause,[],[f383,f61,f57,f533])).
% 27.78/3.88  fof(f531,plain,(
% 27.78/3.88    spl2_27 | ~spl2_5 | ~spl2_6),
% 27.78/3.88    inference(avatar_split_clause,[],[f134,f57,f53,f529])).
% 27.78/3.88  fof(f134,plain,(
% 27.78/3.88    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | (~spl2_5 | ~spl2_6)),
% 27.78/3.88    inference(superposition,[],[f54,f58])).
% 27.78/3.88  fof(f488,plain,(
% 27.78/3.88    spl2_26 | ~spl2_6 | ~spl2_24),
% 27.78/3.88    inference(avatar_split_clause,[],[f441,f430,f57,f486])).
% 27.78/3.88  fof(f441,plain,(
% 27.78/3.88    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) ) | (~spl2_6 | ~spl2_24)),
% 27.78/3.88    inference(superposition,[],[f431,f58])).
% 27.78/3.88  fof(f462,plain,(
% 27.78/3.88    spl2_25 | ~spl2_6 | ~spl2_7 | ~spl2_24),
% 27.78/3.88    inference(avatar_split_clause,[],[f453,f430,f61,f57,f460])).
% 27.78/3.88  fof(f453,plain,(
% 27.78/3.88    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1)) ) | (~spl2_6 | ~spl2_7 | ~spl2_24)),
% 27.78/3.88    inference(forward_demodulation,[],[f434,f383])).
% 27.78/3.88  fof(f434,plain,(
% 27.78/3.88    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))),X1)) ) | (~spl2_6 | ~spl2_24)),
% 27.78/3.88    inference(superposition,[],[f431,f58])).
% 27.78/3.88  fof(f432,plain,(
% 27.78/3.88    spl2_24 | ~spl2_2 | ~spl2_5 | ~spl2_7 | ~spl2_21 | ~spl2_23),
% 27.78/3.88    inference(avatar_split_clause,[],[f398,f342,f334,f61,f53,f36,f430])).
% 27.78/3.88  fof(f398,plain,(
% 27.78/3.88    ( ! [X12,X13] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X13)),X12)) ) | (~spl2_2 | ~spl2_5 | ~spl2_7 | ~spl2_21 | ~spl2_23)),
% 27.78/3.88    inference(forward_demodulation,[],[f397,f347])).
% 27.78/3.88  fof(f347,plain,(
% 27.78/3.88    ( ! [X6,X7] : (k5_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X6,k4_xboole_0(X6,X7))) = X6) ) | (~spl2_5 | ~spl2_21)),
% 27.78/3.88    inference(superposition,[],[f335,f54])).
% 27.78/3.88  fof(f397,plain,(
% 27.78/3.88    ( ! [X12,X13] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X13)),k5_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X12,k4_xboole_0(X12,X13))))) ) | (~spl2_2 | ~spl2_7 | ~spl2_23)),
% 27.78/3.88    inference(forward_demodulation,[],[f389,f343])).
% 27.78/3.88  fof(f389,plain,(
% 27.78/3.88    ( ! [X12,X13] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X13)),k5_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X13)),k4_xboole_0(X12,X13)))) ) | (~spl2_2 | ~spl2_7)),
% 27.78/3.88    inference(superposition,[],[f37,f62])).
% 27.78/3.88  fof(f344,plain,(
% 27.78/3.88    spl2_23 | ~spl2_19 | ~spl2_20),
% 27.78/3.88    inference(avatar_split_clause,[],[f321,f309,f282,f342])).
% 27.78/3.88  fof(f282,plain,(
% 27.78/3.88    spl2_19 <=> ! [X1,X0] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1),
% 27.78/3.88    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 27.78/3.88  fof(f321,plain,(
% 27.78/3.88    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)) ) | (~spl2_19 | ~spl2_20)),
% 27.78/3.88    inference(superposition,[],[f283,f310])).
% 27.78/3.88  fof(f283,plain,(
% 27.78/3.88    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) ) | ~spl2_19),
% 27.78/3.88    inference(avatar_component_clause,[],[f282])).
% 27.78/3.88  fof(f340,plain,(
% 27.78/3.88    spl2_22 | ~spl2_20),
% 27.78/3.88    inference(avatar_split_clause,[],[f316,f309,f338])).
% 27.78/3.88  fof(f316,plain,(
% 27.78/3.88    ( ! [X8,X9] : (k5_xboole_0(k5_xboole_0(X9,X8),X9) = X8) ) | ~spl2_20),
% 27.78/3.88    inference(superposition,[],[f310,f310])).
% 27.78/3.88  fof(f336,plain,(
% 27.78/3.88    spl2_21 | ~spl2_19 | ~spl2_20),
% 27.78/3.88    inference(avatar_split_clause,[],[f315,f309,f282,f334])).
% 27.78/3.88  fof(f315,plain,(
% 27.78/3.88    ( ! [X6,X7] : (k5_xboole_0(k5_xboole_0(X6,X7),X7) = X6) ) | (~spl2_19 | ~spl2_20)),
% 27.78/3.88    inference(superposition,[],[f310,f283])).
% 27.78/3.88  fof(f311,plain,(
% 27.78/3.88    spl2_20 | ~spl2_10 | ~spl2_14 | ~spl2_19),
% 27.78/3.88    inference(avatar_split_clause,[],[f300,f282,f167,f101,f309])).
% 27.78/3.88  fof(f167,plain,(
% 27.78/3.88    spl2_14 <=> ! [X1,X0] : k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))),
% 27.78/3.88    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 27.78/3.88  fof(f300,plain,(
% 27.78/3.88    ( ! [X6,X7] : (k5_xboole_0(X7,k5_xboole_0(X6,X7)) = X6) ) | (~spl2_10 | ~spl2_14 | ~spl2_19)),
% 27.78/3.88    inference(forward_demodulation,[],[f288,f102])).
% 27.78/3.88  fof(f288,plain,(
% 27.78/3.88    ( ! [X6,X7] : (k5_xboole_0(X7,k5_xboole_0(X6,X7)) = k5_xboole_0(X6,k1_xboole_0)) ) | (~spl2_14 | ~spl2_19)),
% 27.78/3.88    inference(superposition,[],[f283,f168])).
% 27.78/3.88  fof(f168,plain,(
% 27.78/3.88    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) ) | ~spl2_14),
% 27.78/3.88    inference(avatar_component_clause,[],[f167])).
% 27.78/3.88  fof(f284,plain,(
% 27.78/3.88    spl2_19 | ~spl2_8 | ~spl2_10 | ~spl2_15),
% 27.78/3.88    inference(avatar_split_clause,[],[f240,f171,f101,f77,f282])).
% 27.78/3.88  fof(f240,plain,(
% 27.78/3.88    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) ) | (~spl2_8 | ~spl2_10 | ~spl2_15)),
% 27.78/3.88    inference(backward_demodulation,[],[f172,f238])).
% 27.78/3.88  fof(f267,plain,(
% 27.78/3.88    spl2_18 | ~spl2_8 | ~spl2_10 | ~spl2_15),
% 27.78/3.88    inference(avatar_split_clause,[],[f238,f171,f101,f77,f265])).
% 27.78/3.88  fof(f173,plain,(
% 27.78/3.88    spl2_15 | ~spl2_4 | ~spl2_8),
% 27.78/3.88    inference(avatar_split_clause,[],[f81,f77,f49,f171])).
% 27.78/3.88  fof(f81,plain,(
% 27.78/3.88    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) ) | (~spl2_4 | ~spl2_8)),
% 27.78/3.88    inference(superposition,[],[f50,f78])).
% 27.78/3.88  fof(f169,plain,(
% 27.78/3.88    spl2_14 | ~spl2_4 | ~spl2_8),
% 27.78/3.88    inference(avatar_split_clause,[],[f80,f77,f49,f167])).
% 27.78/3.88  fof(f80,plain,(
% 27.78/3.88    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) ) | (~spl2_4 | ~spl2_8)),
% 27.78/3.88    inference(superposition,[],[f78,f50])).
% 27.78/3.88  fof(f145,plain,(
% 27.78/3.88    spl2_13 | ~spl2_5 | ~spl2_8 | ~spl2_12),
% 27.78/3.88    inference(avatar_split_clause,[],[f128,f117,f77,f53,f143])).
% 27.78/3.88  fof(f117,plain,(
% 27.78/3.88    spl2_12 <=> ! [X3] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3))),
% 27.78/3.88    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 27.78/3.88  fof(f128,plain,(
% 27.78/3.88    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | (~spl2_5 | ~spl2_8 | ~spl2_12)),
% 27.78/3.88    inference(forward_demodulation,[],[f125,f78])).
% 27.78/3.88  fof(f125,plain,(
% 27.78/3.88    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)) ) | (~spl2_5 | ~spl2_12)),
% 27.78/3.88    inference(superposition,[],[f54,f118])).
% 27.78/3.88  fof(f118,plain,(
% 27.78/3.88    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3))) ) | ~spl2_12),
% 27.78/3.88    inference(avatar_component_clause,[],[f117])).
% 27.78/3.88  fof(f119,plain,(
% 27.78/3.88    spl2_12 | ~spl2_3 | ~spl2_5),
% 27.78/3.88    inference(avatar_split_clause,[],[f73,f53,f43,f117])).
% 27.78/3.88  fof(f43,plain,(
% 27.78/3.88    spl2_3 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))),
% 27.78/3.88    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 27.78/3.88  fof(f73,plain,(
% 27.78/3.88    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3))) ) | (~spl2_3 | ~spl2_5)),
% 27.78/3.88    inference(superposition,[],[f44,f54])).
% 27.78/3.88  fof(f44,plain,(
% 27.78/3.88    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) ) | ~spl2_3),
% 27.78/3.88    inference(avatar_component_clause,[],[f43])).
% 27.78/3.88  fof(f103,plain,(
% 27.78/3.88    spl2_10 | ~spl2_2 | ~spl2_9),
% 27.78/3.88    inference(avatar_split_clause,[],[f94,f85,f36,f101])).
% 27.78/3.88  fof(f85,plain,(
% 27.78/3.88    spl2_9 <=> ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0),
% 27.78/3.88    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 27.78/3.88  fof(f94,plain,(
% 27.78/3.88    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | (~spl2_2 | ~spl2_9)),
% 27.78/3.88    inference(backward_demodulation,[],[f86,f90])).
% 27.78/3.88  fof(f90,plain,(
% 27.78/3.88    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl2_2 | ~spl2_9)),
% 27.78/3.88    inference(superposition,[],[f37,f86])).
% 27.78/3.88  fof(f86,plain,(
% 27.78/3.88    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) ) | ~spl2_9),
% 27.78/3.88    inference(avatar_component_clause,[],[f85])).
% 27.78/3.88  fof(f87,plain,(
% 27.78/3.88    spl2_9 | ~spl2_1 | ~spl2_5),
% 27.78/3.88    inference(avatar_split_clause,[],[f68,f53,f32,f85])).
% 27.78/3.88  fof(f68,plain,(
% 27.78/3.88    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) ) | (~spl2_1 | ~spl2_5)),
% 27.78/3.88    inference(superposition,[],[f54,f33])).
% 27.78/3.88  fof(f79,plain,(
% 27.78/3.88    spl2_8 | ~spl2_1 | ~spl2_2 | ~spl2_5),
% 27.78/3.88    inference(avatar_split_clause,[],[f75,f53,f36,f32,f77])).
% 27.78/3.88  fof(f75,plain,(
% 27.78/3.88    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) ) | (~spl2_1 | ~spl2_2 | ~spl2_5)),
% 27.78/3.88    inference(forward_demodulation,[],[f69,f33])).
% 27.78/3.88  fof(f69,plain,(
% 27.78/3.88    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) ) | (~spl2_2 | ~spl2_5)),
% 27.78/3.88    inference(superposition,[],[f54,f37])).
% 27.78/3.88  fof(f63,plain,(
% 27.78/3.88    spl2_7),
% 27.78/3.88    inference(avatar_split_clause,[],[f29,f61])).
% 27.78/3.88  fof(f29,plain,(
% 27.78/3.88    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 27.78/3.88    inference(definition_unfolding,[],[f22,f20])).
% 27.78/3.88  fof(f22,plain,(
% 27.78/3.88    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 27.78/3.88    inference(cnf_transformation,[],[f5])).
% 27.78/3.88  fof(f5,axiom,(
% 27.78/3.88    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 27.78/3.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 27.78/3.88  fof(f59,plain,(
% 27.78/3.88    spl2_6),
% 27.78/3.88    inference(avatar_split_clause,[],[f28,f57])).
% 27.78/3.88  fof(f28,plain,(
% 27.78/3.88    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 27.78/3.88    inference(definition_unfolding,[],[f18,f20,f20])).
% 27.78/3.88  fof(f18,plain,(
% 27.78/3.88    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 27.78/3.88    inference(cnf_transformation,[],[f1])).
% 27.78/3.88  fof(f1,axiom,(
% 27.78/3.88    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 27.78/3.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 27.78/3.88  fof(f55,plain,(
% 27.78/3.88    spl2_5),
% 27.78/3.88    inference(avatar_split_clause,[],[f25,f53])).
% 27.78/3.88  fof(f25,plain,(
% 27.78/3.88    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 27.78/3.88    inference(definition_unfolding,[],[f21,f20])).
% 27.78/3.88  fof(f21,plain,(
% 27.78/3.88    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 27.78/3.88    inference(cnf_transformation,[],[f2])).
% 27.78/3.88  fof(f2,axiom,(
% 27.78/3.88    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 27.78/3.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 27.78/3.88  fof(f51,plain,(
% 27.78/3.88    spl2_4),
% 27.78/3.88    inference(avatar_split_clause,[],[f23,f49])).
% 27.78/3.88  fof(f23,plain,(
% 27.78/3.88    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 27.78/3.88    inference(cnf_transformation,[],[f8])).
% 27.78/3.88  fof(f8,axiom,(
% 27.78/3.88    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 27.78/3.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 27.78/3.88  fof(f45,plain,(
% 27.78/3.88    spl2_3 | ~spl2_1 | ~spl2_2),
% 27.78/3.88    inference(avatar_split_clause,[],[f39,f36,f32,f43])).
% 27.78/3.88  fof(f39,plain,(
% 27.78/3.88    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) ) | (~spl2_1 | ~spl2_2)),
% 27.78/3.88    inference(superposition,[],[f37,f33])).
% 27.78/3.88  fof(f38,plain,(
% 27.78/3.88    spl2_2),
% 27.78/3.88    inference(avatar_split_clause,[],[f27,f36])).
% 27.78/3.88  fof(f27,plain,(
% 27.78/3.88    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 27.78/3.88    inference(definition_unfolding,[],[f17,f19])).
% 27.78/3.88  fof(f17,plain,(
% 27.78/3.88    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 27.78/3.88    inference(cnf_transformation,[],[f4])).
% 27.78/3.88  fof(f4,axiom,(
% 27.78/3.88    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 27.78/3.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 27.78/3.88  fof(f34,plain,(
% 27.78/3.88    spl2_1),
% 27.78/3.88    inference(avatar_split_clause,[],[f16,f32])).
% 27.78/3.88  fof(f16,plain,(
% 27.78/3.88    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 27.78/3.88    inference(cnf_transformation,[],[f3])).
% 27.78/3.88  fof(f3,axiom,(
% 27.78/3.88    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 27.78/3.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 27.78/3.88  % SZS output end Proof for theBenchmark
% 27.78/3.88  % (17413)------------------------------
% 27.78/3.88  % (17413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 27.78/3.88  % (17413)Termination reason: Refutation
% 27.78/3.88  
% 27.78/3.88  % (17413)Memory used [KB]: 96970
% 27.78/3.88  % (17413)Time elapsed: 3.459 s
% 27.78/3.88  % (17413)------------------------------
% 27.78/3.88  % (17413)------------------------------
% 27.78/3.89  % (17405)Success in time 3.526 s
%------------------------------------------------------------------------------
