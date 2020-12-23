%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:14 EST 2020

% Result     : Theorem 14.02s
% Output     : Refutation 14.69s
% Verified   : 
% Statistics : Number of formulae       : 1016 (4117 expanded)
%              Number of leaves         :  173 (1519 expanded)
%              Depth                    :   19
%              Number of atoms          : 2939 (11837 expanded)
%              Number of equality atoms :  520 (3327 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :   10 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7656,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f137,f146,f184,f188,f236,f240,f247,f255,f262,f282,f288,f325,f327,f343,f445,f484,f488,f525,f529,f533,f588,f595,f599,f603,f634,f665,f678,f682,f704,f719,f863,f867,f933,f990,f1009,f1053,f1057,f1065,f1104,f1142,f1276,f1297,f1304,f1329,f1485,f1493,f1495,f1628,f1643,f1652,f1658,f1887,f1906,f1918,f1959,f1990,f1994,f2022,f2031,f2033,f2063,f2095,f2288,f2295,f2299,f2310,f2314,f2329,f2347,f2360,f2364,f2384,f2388,f2408,f2412,f2438,f2460,f2464,f2484,f2510,f2527,f2531,f2630,f2634,f2779,f2782,f2790,f2992,f3031,f3085,f3152,f3196,f3198,f3201,f3206,f3391,f3443,f3447,f3480,f3532,f3552,f3572,f3597,f3618,f3641,f3662,f3666,f3685,f3709,f3713,f3732,f3741,f3743,f4124,f4142,f4146,f4205,f4381,f4383,f4414,f4453,f4495,f4506,f4512,f4527,f4543,f4557,f4561,f4611,f4645,f4649,f4684,f4688,f4705,f4709,f4726,f5000,f5061,f5065,f5069,f5073,f5077,f5093,f5109,f5113,f5117,f5121,f5125,f5129,f5133,f5137,f5192,f5284,f5289,f5453,f5475,f5507,f5508,f5537,f5598,f5712,f5731,f5735,f5806,f5810,f5986,f6050,f6051,f6103,f6107,f6120,f6212,f6216,f6218,f6233,f6262,f6266,f6273,f6276,f6561,f6565,f6688,f6717,f6751,f6800,f6952,f6973,f7046,f7090,f7173,f7204,f7285,f7294,f7336,f7655])).

fof(f7655,plain,
    ( ~ spl5_90
    | spl5_16
    | spl5_18 ),
    inference(avatar_split_clause,[],[f6294,f523,f482,f4140])).

fof(f4140,plain,
    ( spl5_90
  <=> r2_hidden(sK1,k5_xboole_0(k1_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).

fof(f482,plain,
    ( spl5_16
  <=> r2_hidden(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f523,plain,
    ( spl5_18
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f6294,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k1_xboole_0,sK2))
    | spl5_16
    | spl5_18 ),
    inference(unit_resulting_resolution,[],[f483,f1325,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f1325,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl5_18 ),
    inference(avatar_component_clause,[],[f523])).

fof(f483,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f482])).

fof(f7336,plain,
    ( ~ spl5_149
    | spl5_115 ),
    inference(avatar_split_clause,[],[f5099,f5091,f7334])).

fof(f7334,plain,
    ( spl5_149
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_149])])).

fof(f5091,plain,
    ( spl5_115
  <=> k1_xboole_0 = k5_xboole_0(k1_tarski(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_115])])).

fof(f5099,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_tarski(sK1))
    | spl5_115 ),
    inference(superposition,[],[f5092,f91])).

fof(f91,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f5092,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_tarski(sK1),k1_xboole_0)
    | spl5_115 ),
    inference(avatar_component_clause,[],[f5091])).

fof(f7294,plain,
    ( ~ spl5_148
    | spl5_114 ),
    inference(avatar_split_clause,[],[f5083,f5075,f7292])).

fof(f7292,plain,
    ( spl5_148
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_148])])).

fof(f5075,plain,
    ( spl5_114
  <=> k1_xboole_0 = k5_xboole_0(k1_tarski(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).

fof(f5083,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_tarski(sK0))
    | spl5_114 ),
    inference(superposition,[],[f5076,f91])).

fof(f5076,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_tarski(sK0),k1_xboole_0)
    | spl5_114 ),
    inference(avatar_component_clause,[],[f5075])).

fof(f7285,plain,
    ( ~ spl5_71
    | ~ spl5_147
    | spl5_2
    | ~ spl5_11
    | spl5_18
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f6932,f527,f523,f257,f144,f7283,f2628])).

fof(f2628,plain,
    ( spl5_71
  <=> r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f7283,plain,
    ( spl5_147
  <=> k5_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_147])])).

fof(f144,plain,
    ( spl5_2
  <=> k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) = k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f257,plain,
    ( spl5_11
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f527,plain,
    ( spl5_19
  <=> r1_xboole_0(sK2,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f6932,plain,
    ( k5_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))
    | ~ r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_2
    | ~ spl5_11
    | spl5_18
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f6931,f91])).

fof(f6931,plain,
    ( k5_xboole_0(sK2,k1_xboole_0) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))
    | ~ r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_2
    | ~ spl5_11
    | spl5_18
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f6861,f102])).

fof(f102,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f6861,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_2
    | ~ spl5_11
    | spl5_18
    | ~ spl5_19 ),
    inference(backward_demodulation,[],[f6675,f6802])).

fof(f6802,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK1))
    | ~ spl5_19 ),
    inference(unit_resulting_resolution,[],[f2032,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f2032,plain,
    ( r1_xboole_0(sK2,k1_tarski(sK1))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f527])).

fof(f6675,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))
    | ~ r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_2
    | ~ spl5_11
    | spl5_18 ),
    inference(forward_demodulation,[],[f6575,f91])).

fof(f6575,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))
    | ~ r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_2
    | ~ spl5_11
    | spl5_18 ),
    inference(backward_demodulation,[],[f6536,f6426])).

fof(f6426,plain,
    ( k1_tarski(sK0) = k3_xboole_0(sK2,k1_tarski(sK0))
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f326,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f326,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f257])).

fof(f6536,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1))))
    | ~ r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_2
    | ~ spl5_11
    | spl5_18 ),
    inference(forward_demodulation,[],[f6535,f91])).

fof(f6535,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k1_xboole_0))
    | ~ r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_2
    | ~ spl5_11
    | spl5_18 ),
    inference(forward_demodulation,[],[f6534,f6457])).

fof(f6457,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f6448,f94])).

fof(f94,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f6448,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2))
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f326,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(k1_tarski(X0),k3_xboole_0(k1_tarski(X0),X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f101,f73])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f101,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f6534,plain,
    ( ~ r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))
    | spl5_2
    | ~ spl5_11
    | spl5_18 ),
    inference(forward_demodulation,[],[f6482,f91])).

fof(f6482,plain,
    ( ~ r1_tarski(k1_tarski(sK1),k5_xboole_0(sK2,k1_xboole_0))
    | k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))
    | spl5_2
    | ~ spl5_11
    | spl5_18 ),
    inference(backward_demodulation,[],[f6364,f6457])).

fof(f6364,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))
    | ~ r1_tarski(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))
    | spl5_2
    | spl5_18 ),
    inference(forward_demodulation,[],[f6320,f94])).

fof(f6320,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2))))
    | ~ r1_tarski(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))
    | spl5_2
    | spl5_18 ),
    inference(backward_demodulation,[],[f176,f6307])).

fof(f6307,plain,
    ( sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))
    | spl5_18 ),
    inference(unit_resulting_resolution,[],[f1325,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_tarski(X1))) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f70,f73])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f176,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(sK2,k1_tarski(sK0)))))
    | ~ r1_tarski(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))
    | spl5_2 ),
    inference(forward_demodulation,[],[f175,f91])).

fof(f175,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1))))
    | ~ r1_tarski(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))
    | spl5_2 ),
    inference(forward_demodulation,[],[f174,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f174,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))),k1_tarski(sK1)))
    | ~ r1_tarski(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))
    | spl5_2 ),
    inference(forward_demodulation,[],[f154,f90])).

fof(f154,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))),k1_tarski(sK1))
    | ~ r1_tarski(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))
    | spl5_2 ),
    inference(superposition,[],[f145,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f145,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f144])).

fof(f7204,plain,
    ( ~ spl5_71
    | ~ spl5_146
    | ~ spl5_19
    | spl5_138 ),
    inference(avatar_split_clause,[],[f6944,f6686,f527,f7202,f2628])).

fof(f7202,plain,
    ( spl5_146
  <=> k5_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_146])])).

fof(f6686,plain,
    ( spl5_138
  <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_138])])).

fof(f6944,plain,
    ( k5_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_tarski(sK1)))
    | ~ r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | ~ spl5_19
    | spl5_138 ),
    inference(forward_demodulation,[],[f6943,f91])).

fof(f6943,plain,
    ( k5_xboole_0(sK2,k1_xboole_0) != k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_tarski(sK1)))
    | ~ r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | ~ spl5_19
    | spl5_138 ),
    inference(forward_demodulation,[],[f6867,f102])).

fof(f6867,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_tarski(sK1)))
    | ~ r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | ~ spl5_19
    | spl5_138 ),
    inference(backward_demodulation,[],[f6701,f6802])).

fof(f6701,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_tarski(sK1)))
    | ~ r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_138 ),
    inference(forward_demodulation,[],[f6693,f90])).

fof(f6693,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k1_tarski(sK1))
    | ~ r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_138 ),
    inference(superposition,[],[f6687,f93])).

fof(f6687,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))
    | spl5_138 ),
    inference(avatar_component_clause,[],[f6686])).

fof(f7173,plain,
    ( spl5_123
    | spl5_135 ),
    inference(avatar_contradiction_clause,[],[f7172])).

fof(f7172,plain,
    ( $false
    | spl5_123
    | spl5_135 ),
    inference(subsumption_resolution,[],[f7116,f6260])).

fof(f6260,plain,
    ( ~ r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))
    | spl5_135 ),
    inference(trivial_inequality_removal,[],[f6259])).

fof(f6259,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))
    | ~ r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))
    | spl5_135 ),
    inference(forward_demodulation,[],[f6258,f91])).

fof(f6258,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_xboole_0)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))
    | ~ r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))
    | spl5_135 ),
    inference(forward_demodulation,[],[f6113,f102])).

fof(f6113,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_xboole_0)))
    | ~ r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))
    | spl5_135 ),
    inference(superposition,[],[f6106,f86])).

fof(f6106,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))))
    | spl5_135 ),
    inference(avatar_component_clause,[],[f6105])).

fof(f6105,plain,
    ( spl5_135
  <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_135])])).

fof(f7116,plain,
    ( r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))
    | spl5_123 ),
    inference(unit_resulting_resolution,[],[f5136,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f5136,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(sK2,k1_tarski(sK0)))
    | spl5_123 ),
    inference(avatar_component_clause,[],[f5135])).

fof(f5135,plain,
    ( spl5_123
  <=> r2_hidden(sK1,k5_xboole_0(sK2,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_123])])).

fof(f7090,plain,
    ( ~ spl5_145
    | ~ spl5_19
    | spl5_138 ),
    inference(avatar_split_clause,[],[f6942,f6686,f527,f7088])).

fof(f7088,plain,
    ( spl5_145
  <=> r2_hidden(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),k1_tarski(k5_xboole_0(k1_xboole_0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_145])])).

fof(f6942,plain,
    ( ~ r2_hidden(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),k1_tarski(k5_xboole_0(k1_xboole_0,sK2)))
    | ~ spl5_19
    | spl5_138 ),
    inference(forward_demodulation,[],[f6941,f91])).

fof(f6941,plain,
    ( ~ r2_hidden(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),k1_tarski(k5_xboole_0(sK2,k1_xboole_0)))
    | ~ spl5_19
    | spl5_138 ),
    inference(forward_demodulation,[],[f6866,f102])).

fof(f6866,plain,
    ( ~ r2_hidden(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0))))
    | ~ spl5_19
    | spl5_138 ),
    inference(backward_demodulation,[],[f6700,f6802])).

fof(f6700,plain,
    ( ~ r2_hidden(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1))))))
    | spl5_138 ),
    inference(forward_demodulation,[],[f6689,f90])).

fof(f6689,plain,
    ( ~ r2_hidden(k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1))))))
    | spl5_138 ),
    inference(unit_resulting_resolution,[],[f6687,f126])).

fof(f126,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f7046,plain,
    ( ~ spl5_144
    | ~ spl5_19
    | spl5_138 ),
    inference(avatar_split_clause,[],[f6938,f6686,f527,f7044])).

fof(f7044,plain,
    ( spl5_144
  <=> r2_hidden(k5_xboole_0(k1_xboole_0,sK2),k1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_144])])).

fof(f6938,plain,
    ( ~ r2_hidden(k5_xboole_0(k1_xboole_0,sK2),k1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))))
    | ~ spl5_19
    | spl5_138 ),
    inference(forward_demodulation,[],[f6937,f91])).

fof(f6937,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k1_xboole_0),k1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))))
    | ~ spl5_19
    | spl5_138 ),
    inference(forward_demodulation,[],[f6864,f102])).

fof(f6864,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0)),k1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))))
    | ~ spl5_19
    | spl5_138 ),
    inference(backward_demodulation,[],[f6698,f6802])).

fof(f6698,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))),k1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))))
    | spl5_138 ),
    inference(forward_demodulation,[],[f6691,f90])).

fof(f6691,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))),k1_tarski(k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))))
    | spl5_138 ),
    inference(unit_resulting_resolution,[],[f6687,f126])).

fof(f6973,plain,
    ( ~ spl5_143
    | ~ spl5_19
    | spl5_141 ),
    inference(avatar_split_clause,[],[f6948,f6798,f527,f6971])).

fof(f6971,plain,
    ( spl5_143
  <=> k5_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_143])])).

fof(f6798,plain,
    ( spl5_141
  <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_141])])).

fof(f6948,plain,
    ( k5_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | ~ spl5_19
    | spl5_141 ),
    inference(forward_demodulation,[],[f6947,f91])).

fof(f6947,plain,
    ( k5_xboole_0(sK2,k1_xboole_0) != k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | ~ spl5_19
    | spl5_141 ),
    inference(forward_demodulation,[],[f6870,f102])).

fof(f6870,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | ~ spl5_19
    | spl5_141 ),
    inference(backward_demodulation,[],[f6799,f6802])).

fof(f6799,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | spl5_141 ),
    inference(avatar_component_clause,[],[f6798])).

fof(f6952,plain,
    ( ~ spl5_142
    | ~ spl5_19
    | spl5_138 ),
    inference(avatar_split_clause,[],[f6934,f6686,f527,f6950])).

fof(f6950,plain,
    ( spl5_142
  <=> k5_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_142])])).

fof(f6934,plain,
    ( k5_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))
    | ~ spl5_19
    | spl5_138 ),
    inference(forward_demodulation,[],[f6933,f91])).

fof(f6933,plain,
    ( k5_xboole_0(sK2,k1_xboole_0) != k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))
    | ~ spl5_19
    | spl5_138 ),
    inference(forward_demodulation,[],[f6862,f102])).

fof(f6862,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))
    | ~ spl5_19
    | spl5_138 ),
    inference(backward_demodulation,[],[f6687,f6802])).

fof(f6800,plain,
    ( ~ spl5_141
    | spl5_138 ),
    inference(avatar_split_clause,[],[f6695,f6686,f6798])).

fof(f6695,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | spl5_138 ),
    inference(superposition,[],[f6687,f90])).

fof(f6751,plain,
    ( ~ spl5_140
    | ~ spl5_11
    | spl5_92 ),
    inference(avatar_split_clause,[],[f6510,f4412,f257,f6749])).

fof(f6749,plain,
    ( spl5_140
  <=> r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),k1_tarski(k5_xboole_0(k1_xboole_0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_140])])).

fof(f4412,plain,
    ( spl5_92
  <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).

fof(f6510,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),k1_tarski(k5_xboole_0(k1_xboole_0,sK2)))
    | ~ spl5_11
    | spl5_92 ),
    inference(forward_demodulation,[],[f6509,f91])).

fof(f6509,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),k1_tarski(k5_xboole_0(sK2,k1_xboole_0)))
    | ~ spl5_11
    | spl5_92 ),
    inference(forward_demodulation,[],[f6467,f102])).

fof(f6467,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0))))
    | ~ spl5_11
    | spl5_92 ),
    inference(backward_demodulation,[],[f4417,f6457])).

fof(f4417,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))))
    | spl5_92 ),
    inference(unit_resulting_resolution,[],[f4413,f126])).

fof(f4413,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))
    | spl5_92 ),
    inference(avatar_component_clause,[],[f4412])).

fof(f6717,plain,
    ( ~ spl5_139
    | ~ spl5_11
    | spl5_92 ),
    inference(avatar_split_clause,[],[f6505,f4412,f257,f6715])).

fof(f6715,plain,
    ( spl5_139
  <=> r2_hidden(k5_xboole_0(k1_xboole_0,sK2),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_139])])).

fof(f6505,plain,
    ( ~ r2_hidden(k5_xboole_0(k1_xboole_0,sK2),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))))
    | ~ spl5_11
    | spl5_92 ),
    inference(forward_demodulation,[],[f6504,f91])).

fof(f6504,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k1_xboole_0),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))))
    | ~ spl5_11
    | spl5_92 ),
    inference(forward_demodulation,[],[f6465,f102])).

fof(f6465,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0)),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))))
    | ~ spl5_11
    | spl5_92 ),
    inference(backward_demodulation,[],[f4415,f6457])).

fof(f4415,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))))
    | spl5_92 ),
    inference(unit_resulting_resolution,[],[f4413,f126])).

fof(f6688,plain,
    ( ~ spl5_138
    | spl5_2
    | ~ spl5_11
    | spl5_18 ),
    inference(avatar_split_clause,[],[f6527,f523,f257,f144,f6686])).

fof(f6527,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))
    | spl5_2
    | ~ spl5_11
    | spl5_18 ),
    inference(forward_demodulation,[],[f6526,f91])).

fof(f6526,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k1_xboole_0)) != k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))
    | spl5_2
    | ~ spl5_11
    | spl5_18 ),
    inference(forward_demodulation,[],[f6478,f91])).

fof(f6478,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k1_xboole_0)) != k5_xboole_0(k5_xboole_0(sK2,k1_xboole_0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_xboole_0)))
    | spl5_2
    | ~ spl5_11
    | spl5_18 ),
    inference(backward_demodulation,[],[f6360,f6457])).

fof(f6360,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))) != k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))
    | spl5_2
    | spl5_18 ),
    inference(forward_demodulation,[],[f6316,f94])).

fof(f6316,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))) != k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2))))
    | spl5_2
    | spl5_18 ),
    inference(backward_demodulation,[],[f145,f6307])).

fof(f6565,plain,
    ( ~ spl5_11
    | spl5_32
    | spl5_98 ),
    inference(avatar_contradiction_clause,[],[f6564])).

fof(f6564,plain,
    ( $false
    | ~ spl5_11
    | spl5_32
    | spl5_98 ),
    inference(subsumption_resolution,[],[f6563,f6053])).

fof(f6053,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(k1_xboole_0,sK2))
    | spl5_98 ),
    inference(resolution,[],[f4542,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f4542,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_98 ),
    inference(avatar_component_clause,[],[f4541])).

fof(f4541,plain,
    ( spl5_98
  <=> r1_tarski(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).

fof(f6563,plain,
    ( r2_hidden(sK0,k5_xboole_0(k1_xboole_0,sK2))
    | ~ spl5_11
    | spl5_32 ),
    inference(forward_demodulation,[],[f6434,f91])).

fof(f6434,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK2,k1_xboole_0))
    | ~ spl5_11
    | spl5_32 ),
    inference(unit_resulting_resolution,[],[f989,f326,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f989,plain,
    ( ~ r2_hidden(sK0,k1_xboole_0)
    | spl5_32 ),
    inference(avatar_component_clause,[],[f988])).

fof(f988,plain,
    ( spl5_32
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f6561,plain,
    ( ~ spl5_11
    | spl5_32
    | spl5_98 ),
    inference(avatar_contradiction_clause,[],[f6560])).

fof(f6560,plain,
    ( $false
    | ~ spl5_11
    | spl5_32
    | spl5_98 ),
    inference(subsumption_resolution,[],[f6440,f6053])).

fof(f6440,plain,
    ( r2_hidden(sK0,k5_xboole_0(k1_xboole_0,sK2))
    | ~ spl5_11
    | spl5_32 ),
    inference(unit_resulting_resolution,[],[f989,f326,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f6276,plain,
    ( spl5_4
    | ~ spl5_11
    | spl5_132 ),
    inference(avatar_contradiction_clause,[],[f6275])).

fof(f6275,plain,
    ( $false
    | spl5_4
    | ~ spl5_11
    | spl5_132 ),
    inference(subsumption_resolution,[],[f6274,f326])).

fof(f6274,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_4
    | spl5_132 ),
    inference(subsumption_resolution,[],[f5838,f187])).

fof(f187,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK1))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl5_4
  <=> r2_hidden(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f5838,plain,
    ( r2_hidden(sK0,k1_tarski(sK1))
    | ~ r2_hidden(sK0,sK2)
    | spl5_132 ),
    inference(resolution,[],[f5809,f84])).

fof(f5809,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(sK2,k1_tarski(sK1)))
    | spl5_132 ),
    inference(avatar_component_clause,[],[f5808])).

fof(f5808,plain,
    ( spl5_132
  <=> r2_hidden(sK0,k5_xboole_0(sK2,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_132])])).

fof(f6273,plain,
    ( spl5_4
    | ~ spl5_11
    | spl5_132 ),
    inference(avatar_contradiction_clause,[],[f6272])).

fof(f6272,plain,
    ( $false
    | spl5_4
    | ~ spl5_11
    | spl5_132 ),
    inference(subsumption_resolution,[],[f5811,f326])).

fof(f5811,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_4
    | spl5_132 ),
    inference(unit_resulting_resolution,[],[f187,f5809,f84])).

fof(f6266,plain,
    ( ~ spl5_11
    | spl5_32
    | spl5_95 ),
    inference(avatar_contradiction_clause,[],[f6265])).

fof(f6265,plain,
    ( $false
    | ~ spl5_11
    | spl5_32
    | spl5_95 ),
    inference(subsumption_resolution,[],[f326,f6239])).

fof(f6239,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_32
    | spl5_95 ),
    inference(subsumption_resolution,[],[f6017,f989])).

fof(f6017,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ r2_hidden(sK0,sK2)
    | spl5_95 ),
    inference(resolution,[],[f4494,f85])).

fof(f4494,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(k1_xboole_0,sK2))
    | spl5_95 ),
    inference(avatar_component_clause,[],[f4493])).

fof(f4493,plain,
    ( spl5_95
  <=> r2_hidden(sK0,k5_xboole_0(k1_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_95])])).

fof(f6262,plain,
    ( ~ spl5_19
    | spl5_130 ),
    inference(avatar_contradiction_clause,[],[f6261])).

fof(f6261,plain,
    ( $false
    | ~ spl5_19
    | spl5_130 ),
    inference(subsumption_resolution,[],[f2032,f5795])).

fof(f5795,plain,
    ( ~ r1_xboole_0(sK2,k1_tarski(sK1))
    | spl5_130 ),
    inference(trivial_inequality_removal,[],[f5794])).

fof(f5794,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(sK2,k1_tarski(sK1))
    | spl5_130 ),
    inference(superposition,[],[f5734,f86])).

fof(f5734,plain,
    ( k1_xboole_0 != k3_xboole_0(sK2,k1_tarski(sK1))
    | spl5_130 ),
    inference(avatar_component_clause,[],[f5733])).

fof(f5733,plain,
    ( spl5_130
  <=> k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_130])])).

fof(f6233,plain,
    ( ~ spl5_74
    | ~ spl5_18
    | spl5_25
    | spl5_132 ),
    inference(avatar_split_clause,[],[f6221,f5808,f632,f523,f3441])).

fof(f3441,plain,
    ( spl5_74
  <=> k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f632,plain,
    ( spl5_25
  <=> k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f6221,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl5_18
    | spl5_25
    | spl5_132 ),
    inference(subsumption_resolution,[],[f6220,f5813])).

fof(f5813,plain,
    ( r1_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_tarski(sK1)))
    | spl5_132 ),
    inference(unit_resulting_resolution,[],[f5809,f81])).

fof(f6220,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_tarski(sK1)))
    | k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl5_18
    | spl5_25 ),
    inference(forward_demodulation,[],[f6219,f5292])).

fof(f5292,plain,
    ( k1_tarski(sK1) = k3_xboole_0(sK2,k1_tarski(sK1))
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f524,f80])).

fof(f524,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f523])).

fof(f6219,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ r1_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))
    | ~ spl5_18
    | spl5_25 ),
    inference(forward_demodulation,[],[f931,f5292])).

fof(f931,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
    | ~ r1_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))
    | spl5_25 ),
    inference(forward_demodulation,[],[f918,f91])).

fof(f918,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
    | ~ r1_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))
    | spl5_25 ),
    inference(superposition,[],[f633,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f71,f73])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f633,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
    | spl5_25 ),
    inference(avatar_component_clause,[],[f632])).

fof(f6218,plain,
    ( spl5_3
    | ~ spl5_18
    | spl5_120 ),
    inference(avatar_contradiction_clause,[],[f6217])).

fof(f6217,plain,
    ( $false
    | spl5_3
    | ~ spl5_18
    | spl5_120 ),
    inference(subsumption_resolution,[],[f6214,f5323])).

fof(f5323,plain,
    ( r2_hidden(sK1,k5_xboole_0(sK2,k1_tarski(sK0)))
    | spl5_3
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f5303,f91])).

fof(f5303,plain,
    ( r2_hidden(sK1,k5_xboole_0(k1_tarski(sK0),sK2))
    | spl5_3
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f183,f524,f85])).

fof(f183,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK0))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl5_3
  <=> r2_hidden(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f6214,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(sK2,k1_tarski(sK0)))
    | spl5_120 ),
    inference(resolution,[],[f5124,f96])).

fof(f5124,plain,
    ( ~ r1_tarski(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))
    | spl5_120 ),
    inference(avatar_component_clause,[],[f5123])).

fof(f5123,plain,
    ( spl5_120
  <=> r1_tarski(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_120])])).

fof(f6216,plain,
    ( spl5_3
    | ~ spl5_18
    | spl5_120 ),
    inference(avatar_contradiction_clause,[],[f6215])).

fof(f6215,plain,
    ( $false
    | spl5_3
    | ~ spl5_18
    | spl5_120 ),
    inference(subsumption_resolution,[],[f6213,f5323])).

fof(f6213,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(sK2,k1_tarski(sK0)))
    | spl5_120 ),
    inference(unit_resulting_resolution,[],[f5124,f96])).

fof(f6212,plain,
    ( ~ spl5_137
    | spl5_99 ),
    inference(avatar_split_clause,[],[f4585,f4555,f6210])).

fof(f6210,plain,
    ( spl5_137
  <=> r1_tarski(k1_tarski(sK0),k5_xboole_0(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_137])])).

fof(f4555,plain,
    ( spl5_99
  <=> r2_hidden(sK0,k5_xboole_0(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_99])])).

fof(f4585,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k5_xboole_0(sK2,sK2))
    | spl5_99 ),
    inference(unit_resulting_resolution,[],[f4556,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f4556,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(sK2,sK2))
    | spl5_99 ),
    inference(avatar_component_clause,[],[f4555])).

fof(f6120,plain,
    ( spl5_136
    | spl5_99 ),
    inference(avatar_split_clause,[],[f4571,f4555,f6118])).

fof(f6118,plain,
    ( spl5_136
  <=> r1_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_136])])).

fof(f4571,plain,
    ( r1_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,sK2))
    | spl5_99 ),
    inference(unit_resulting_resolution,[],[f4556,f81])).

fof(f6107,plain,
    ( ~ spl5_135
    | spl5_100
    | ~ spl5_133 ),
    inference(avatar_split_clause,[],[f6068,f6048,f4559,f6105])).

fof(f4559,plain,
    ( spl5_100
  <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).

fof(f6048,plain,
    ( spl5_133
  <=> r1_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_133])])).

fof(f6068,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))))
    | spl5_100
    | ~ spl5_133 ),
    inference(backward_demodulation,[],[f4560,f6056])).

fof(f6056,plain,
    ( k1_tarski(sK0) = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2)))
    | ~ spl5_133 ),
    inference(unit_resulting_resolution,[],[f6049,f116])).

fof(f6049,plain,
    ( r1_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))
    | ~ spl5_133 ),
    inference(avatar_component_clause,[],[f6048])).

fof(f4560,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))))
    | spl5_100 ),
    inference(avatar_component_clause,[],[f4559])).

fof(f6103,plain,
    ( spl5_134
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f4462,f253,f6101])).

fof(f6101,plain,
    ( spl5_134
  <=> k1_xboole_0 = k3_xboole_0(k1_tarski(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_134])])).

fof(f253,plain,
    ( spl5_10
  <=> r1_xboole_0(k1_tarski(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f4462,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_tarski(sK0),sK2)
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f587,f86])).

fof(f587,plain,
    ( r1_xboole_0(k1_tarski(sK0),sK2)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f253])).

fof(f6051,plain,
    ( ~ spl5_98
    | spl5_95 ),
    inference(avatar_split_clause,[],[f6009,f4493,f4541])).

fof(f6009,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_95 ),
    inference(unit_resulting_resolution,[],[f4494,f95])).

fof(f6050,plain,
    ( spl5_133
    | spl5_95 ),
    inference(avatar_split_clause,[],[f5989,f4493,f6048])).

fof(f5989,plain,
    ( r1_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_95 ),
    inference(unit_resulting_resolution,[],[f4494,f81])).

fof(f5986,plain,
    ( ~ spl5_95
    | spl5_11
    | spl5_32 ),
    inference(avatar_split_clause,[],[f4430,f988,f257,f4493])).

fof(f4430,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(k1_xboole_0,sK2))
    | spl5_11
    | spl5_32 ),
    inference(unit_resulting_resolution,[],[f989,f258,f82])).

fof(f258,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f257])).

fof(f5810,plain,
    ( ~ spl5_132
    | spl5_4
    | spl5_11 ),
    inference(avatar_split_clause,[],[f4448,f257,f186,f5808])).

fof(f4448,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(sK2,k1_tarski(sK1)))
    | spl5_4
    | spl5_11 ),
    inference(forward_demodulation,[],[f4431,f91])).

fof(f4431,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(k1_tarski(sK1),sK2))
    | spl5_4
    | spl5_11 ),
    inference(unit_resulting_resolution,[],[f187,f258,f82])).

fof(f5806,plain,
    ( spl5_131
    | spl5_11 ),
    inference(avatar_split_clause,[],[f4442,f257,f5804])).

fof(f5804,plain,
    ( spl5_131
  <=> ! [X0] : ~ r2_hidden(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_131])])).

fof(f4442,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0)))
    | spl5_11 ),
    inference(unit_resulting_resolution,[],[f258,f123])).

fof(f123,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f63,f73])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f5735,plain,
    ( ~ spl5_130
    | spl5_19 ),
    inference(avatar_split_clause,[],[f5446,f527,f5733])).

fof(f5446,plain,
    ( k1_xboole_0 != k3_xboole_0(sK2,k1_tarski(sK1))
    | spl5_19 ),
    inference(unit_resulting_resolution,[],[f528,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f528,plain,
    ( ~ r1_xboole_0(sK2,k1_tarski(sK1))
    | spl5_19 ),
    inference(avatar_component_clause,[],[f527])).

fof(f5731,plain,
    ( ~ spl5_129
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f5407,f523,f5729])).

fof(f5729,plain,
    ( spl5_129
  <=> sK2 = k5_xboole_0(sK2,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_129])])).

fof(f5407,plain,
    ( sK2 != k5_xboole_0(sK2,k1_tarski(sK1))
    | ~ spl5_18 ),
    inference(backward_demodulation,[],[f5309,f5292])).

fof(f5309,plain,
    ( sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f524,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_tarski(X1))) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f69,f73])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f5712,plain,
    ( ~ spl5_72
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f5325,f523,f2632])).

fof(f2632,plain,
    ( spl5_72
  <=> r2_hidden(sK1,k5_xboole_0(sK2,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f5325,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(sK2,k1_tarski(sK1)))
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f5296,f91])).

fof(f5296,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k1_tarski(sK1),sK2))
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f125,f524,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f125,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f124])).

fof(f124,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f5598,plain,
    ( ~ spl5_128
    | ~ spl5_8
    | spl5_93 ),
    inference(avatar_split_clause,[],[f5198,f4451,f242,f5596])).

fof(f5596,plain,
    ( spl5_128
  <=> r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_128])])).

fof(f242,plain,
    ( spl5_8
  <=> r1_xboole_0(sK2,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f4451,plain,
    ( spl5_93
  <=> k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).

fof(f5198,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))
    | ~ spl5_8
    | spl5_93 ),
    inference(forward_demodulation,[],[f5197,f91])).

fof(f5197,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k1_xboole_0)))))
    | ~ spl5_8
    | spl5_93 ),
    inference(forward_demodulation,[],[f4456,f4524])).

fof(f4524,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK0))
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f932,f86])).

fof(f932,plain,
    ( r1_xboole_0(sK2,k1_tarski(sK0))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f242])).

fof(f4456,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))))
    | spl5_93 ),
    inference(unit_resulting_resolution,[],[f4452,f126])).

fof(f4452,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))
    | spl5_93 ),
    inference(avatar_component_clause,[],[f4451])).

fof(f5537,plain,
    ( ~ spl5_127
    | ~ spl5_8
    | spl5_93 ),
    inference(avatar_split_clause,[],[f5194,f4451,f242,f5535])).

fof(f5535,plain,
    ( spl5_127
  <=> r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_127])])).

fof(f5194,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))))
    | ~ spl5_8
    | spl5_93 ),
    inference(forward_demodulation,[],[f5193,f91])).

fof(f5193,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k1_xboole_0))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))))
    | ~ spl5_8
    | spl5_93 ),
    inference(forward_demodulation,[],[f4454,f4524])).

fof(f4454,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))))
    | spl5_93 ),
    inference(unit_resulting_resolution,[],[f4452,f126])).

fof(f5508,plain,
    ( ~ spl5_16
    | spl5_3
    | ~ spl5_61 ),
    inference(avatar_split_clause,[],[f2504,f2382,f182,f482])).

fof(f2382,plain,
    ( spl5_61
  <=> r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f2504,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | spl5_3
    | ~ spl5_61 ),
    inference(backward_demodulation,[],[f196,f2499])).

fof(f2499,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl5_61 ),
    inference(unit_resulting_resolution,[],[f2383,f86])).

fof(f2383,plain,
    ( r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl5_61 ),
    inference(avatar_component_clause,[],[f2382])).

fof(f196,plain,
    ( ~ r2_hidden(sK1,k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f120,f183,f85])).

fof(f120,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(X1,k3_xboole_0(X1,k1_tarski(X2)))) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k1_tarski(X2)))) ) ),
    inference(definition_unfolding,[],[f61,f73])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f5507,plain,
    ( ~ spl5_126
    | ~ spl5_8
    | spl5_92 ),
    inference(avatar_split_clause,[],[f5207,f4412,f242,f5505])).

fof(f5505,plain,
    ( spl5_126
  <=> r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_126])])).

fof(f5207,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))
    | ~ spl5_8
    | spl5_92 ),
    inference(forward_demodulation,[],[f5206,f91])).

fof(f5206,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k1_xboole_0)))))
    | ~ spl5_8
    | spl5_92 ),
    inference(forward_demodulation,[],[f4417,f4524])).

fof(f5475,plain,
    ( ~ spl5_125
    | ~ spl5_8
    | spl5_92 ),
    inference(avatar_split_clause,[],[f5202,f4412,f242,f5473])).

fof(f5473,plain,
    ( spl5_125
  <=> r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_125])])).

fof(f5202,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))))
    | ~ spl5_8
    | spl5_92 ),
    inference(forward_demodulation,[],[f5201,f91])).

fof(f5201,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k1_xboole_0))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))))
    | ~ spl5_8
    | spl5_92 ),
    inference(forward_demodulation,[],[f4415,f4524])).

fof(f5453,plain,
    ( ~ spl5_124
    | ~ spl5_8
    | spl5_92 ),
    inference(avatar_split_clause,[],[f4424,f4412,f242,f5451])).

fof(f5451,plain,
    ( spl5_124
  <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_124])])).

fof(f4424,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))
    | ~ spl5_8
    | spl5_92 ),
    inference(forward_demodulation,[],[f4423,f91])).

fof(f4423,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k1_xboole_0)))
    | ~ spl5_8
    | spl5_92 ),
    inference(subsumption_resolution,[],[f4421,f932])).

fof(f4421,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k1_xboole_0)))
    | ~ r1_xboole_0(sK2,k1_tarski(sK0))
    | spl5_92 ),
    inference(superposition,[],[f4413,f86])).

fof(f5289,plain,
    ( spl5_3
    | ~ spl5_18
    | ~ spl5_61
    | spl5_90 ),
    inference(avatar_contradiction_clause,[],[f5288])).

fof(f5288,plain,
    ( $false
    | spl5_3
    | ~ spl5_18
    | ~ spl5_61
    | spl5_90 ),
    inference(subsumption_resolution,[],[f2504,f5287])).

fof(f5287,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl5_18
    | spl5_90 ),
    inference(subsumption_resolution,[],[f4186,f524])).

fof(f4186,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ r2_hidden(sK1,sK2)
    | spl5_90 ),
    inference(resolution,[],[f4141,f85])).

fof(f4141,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k1_xboole_0,sK2))
    | spl5_90 ),
    inference(avatar_component_clause,[],[f4140])).

fof(f5284,plain,
    ( ~ spl5_18
    | spl5_48
    | spl5_90 ),
    inference(avatar_contradiction_clause,[],[f5283])).

fof(f5283,plain,
    ( $false
    | ~ spl5_18
    | spl5_48
    | spl5_90 ),
    inference(subsumption_resolution,[],[f524,f5223])).

fof(f5223,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl5_48
    | spl5_90 ),
    inference(subsumption_resolution,[],[f4186,f3430])).

fof(f3430,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | spl5_48 ),
    inference(resolution,[],[f1989,f96])).

fof(f1989,plain,
    ( ~ r1_tarski(k1_tarski(sK1),k1_xboole_0)
    | spl5_48 ),
    inference(avatar_component_clause,[],[f1988])).

fof(f1988,plain,
    ( spl5_48
  <=> r1_tarski(k1_tarski(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f5192,plain,
    ( spl5_117
    | spl5_123 ),
    inference(avatar_contradiction_clause,[],[f5191])).

fof(f5191,plain,
    ( $false
    | spl5_117
    | spl5_123 ),
    inference(subsumption_resolution,[],[f5140,f5112])).

fof(f5112,plain,
    ( ~ r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))
    | spl5_117 ),
    inference(avatar_component_clause,[],[f5111])).

fof(f5111,plain,
    ( spl5_117
  <=> r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_117])])).

fof(f5140,plain,
    ( r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))
    | spl5_123 ),
    inference(unit_resulting_resolution,[],[f5136,f81])).

fof(f5137,plain,
    ( ~ spl5_123
    | spl5_3
    | spl5_18 ),
    inference(avatar_split_clause,[],[f3935,f523,f182,f5135])).

fof(f3935,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(sK2,k1_tarski(sK0)))
    | spl5_3
    | spl5_18 ),
    inference(forward_demodulation,[],[f3796,f91])).

fof(f3796,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k1_tarski(sK0),sK2))
    | spl5_3
    | spl5_18 ),
    inference(unit_resulting_resolution,[],[f183,f1325,f82])).

fof(f5133,plain,
    ( ~ spl5_122
    | spl5_66 ),
    inference(avatar_split_clause,[],[f2599,f2458,f5131])).

fof(f5131,plain,
    ( spl5_122
  <=> r1_tarski(k1_tarski(sK1),k5_xboole_0(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_122])])).

fof(f2458,plain,
    ( spl5_66
  <=> r2_hidden(sK1,k5_xboole_0(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).

fof(f2599,plain,
    ( ~ r1_tarski(k1_tarski(sK1),k5_xboole_0(sK2,sK2))
    | spl5_66 ),
    inference(unit_resulting_resolution,[],[f2459,f95])).

fof(f2459,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(sK2,sK2))
    | spl5_66 ),
    inference(avatar_component_clause,[],[f2458])).

fof(f5129,plain,
    ( spl5_121
    | spl5_18 ),
    inference(avatar_split_clause,[],[f3809,f523,f5127])).

fof(f5127,plain,
    ( spl5_121
  <=> ! [X0] : ~ r2_hidden(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_121])])).

fof(f3809,plain,
    ( ! [X0] : ~ r2_hidden(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,X0)))
    | spl5_18 ),
    inference(unit_resulting_resolution,[],[f1325,f123])).

fof(f5125,plain,
    ( ~ spl5_120
    | spl5_74 ),
    inference(avatar_split_clause,[],[f3454,f3441,f5123])).

fof(f3454,plain,
    ( ~ r1_tarski(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))
    | spl5_74 ),
    inference(trivial_inequality_removal,[],[f3452])).

fof(f3452,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ r1_tarski(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))
    | spl5_74 ),
    inference(superposition,[],[f3442,f93])).

fof(f3442,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | spl5_74 ),
    inference(avatar_component_clause,[],[f3441])).

fof(f5121,plain,
    ( spl5_119
    | spl5_66 ),
    inference(avatar_split_clause,[],[f2585,f2458,f5119])).

fof(f5119,plain,
    ( spl5_119
  <=> r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_119])])).

fof(f2585,plain,
    ( r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,sK2))
    | spl5_66 ),
    inference(unit_resulting_resolution,[],[f2459,f81])).

fof(f5117,plain,
    ( ~ spl5_118
    | spl5_4 ),
    inference(avatar_split_clause,[],[f3316,f186,f5115])).

fof(f5115,plain,
    ( spl5_118
  <=> r2_hidden(sK0,k5_xboole_0(k1_tarski(sK1),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).

fof(f3316,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(k1_tarski(sK1),k1_tarski(sK1)))
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f187,f187,f82])).

fof(f5113,plain,
    ( ~ spl5_117
    | spl5_57 ),
    inference(avatar_split_clause,[],[f3264,f2327,f5111])).

fof(f2327,plain,
    ( spl5_57
  <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f3264,plain,
    ( ~ r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))
    | spl5_57 ),
    inference(trivial_inequality_removal,[],[f3263])).

fof(f3263,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))
    | ~ r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))
    | spl5_57 ),
    inference(forward_demodulation,[],[f2335,f91])).

fof(f2335,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_xboole_0)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))
    | ~ r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))
    | spl5_57 ),
    inference(superposition,[],[f2328,f86])).

fof(f2328,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
    | spl5_57 ),
    inference(avatar_component_clause,[],[f2327])).

fof(f5109,plain,
    ( spl5_116
    | spl5_32 ),
    inference(avatar_split_clause,[],[f2560,f988,f5107])).

fof(f5107,plain,
    ( spl5_116
  <=> r2_hidden(sK0,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_116])])).

fof(f2560,plain,
    ( r2_hidden(sK0,k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))
    | spl5_32 ),
    inference(unit_resulting_resolution,[],[f125,f989,f85])).

fof(f5093,plain,
    ( ~ spl5_115
    | spl5_3
    | ~ spl5_61 ),
    inference(avatar_split_clause,[],[f2506,f2382,f182,f5091])).

fof(f2506,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_tarski(sK1),k1_xboole_0)
    | spl5_3
    | ~ spl5_61 ),
    inference(backward_demodulation,[],[f204,f2499])).

fof(f204,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | spl5_3 ),
    inference(forward_demodulation,[],[f200,f94])).

fof(f200,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f183,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(k1_tarski(X0),k3_xboole_0(k1_tarski(X0),X1))
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f100,f73])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f5077,plain,
    ( ~ spl5_114
    | spl5_4
    | ~ spl5_61 ),
    inference(avatar_split_clause,[],[f2503,f2382,f186,f5075])).

fof(f2503,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_tarski(sK0),k1_xboole_0)
    | spl5_4
    | ~ spl5_61 ),
    inference(backward_demodulation,[],[f220,f2499])).

fof(f220,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f187,f119])).

fof(f5073,plain,
    ( spl5_113
    | spl5_4 ),
    inference(avatar_split_clause,[],[f227,f186,f5071])).

fof(f5071,plain,
    ( spl5_113
  <=> r2_hidden(sK0,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_113])])).

fof(f227,plain,
    ( r2_hidden(sK0,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | spl5_4 ),
    inference(forward_demodulation,[],[f215,f91])).

fof(f215,plain,
    ( r2_hidden(sK0,k5_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f125,f187,f85])).

fof(f5069,plain,
    ( spl5_112
    | spl5_16 ),
    inference(avatar_split_clause,[],[f1113,f482,f5067])).

fof(f5067,plain,
    ( spl5_112
  <=> r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_112])])).

fof(f1113,plain,
    ( r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k1_tarski(sK1)))
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f125,f483,f85])).

fof(f5065,plain,
    ( spl5_111
    | spl5_3 ),
    inference(avatar_split_clause,[],[f195,f182,f5063])).

fof(f5063,plain,
    ( spl5_111
  <=> r2_hidden(sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_111])])).

fof(f195,plain,
    ( r2_hidden(sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f125,f183,f85])).

fof(f5061,plain,
    ( ~ spl5_110
    | spl5_3 ),
    inference(avatar_split_clause,[],[f192,f182,f5059])).

fof(f5059,plain,
    ( spl5_110
  <=> r2_hidden(sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).

fof(f192,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f183,f183,f82])).

fof(f5000,plain,
    ( spl5_109
    | spl5_11 ),
    inference(avatar_split_clause,[],[f4435,f257,f4998])).

fof(f4998,plain,
    ( spl5_109
  <=> r2_hidden(sK0,k5_xboole_0(sK2,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_109])])).

fof(f4435,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK2,k1_tarski(sK0)))
    | spl5_11 ),
    inference(unit_resulting_resolution,[],[f125,f258,f85])).

fof(f4726,plain,
    ( ~ spl5_108
    | spl5_87 ),
    inference(avatar_split_clause,[],[f3735,f3711,f4724])).

fof(f4724,plain,
    ( spl5_108
  <=> r2_hidden(k1_xboole_0,k1_tarski(k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_108])])).

fof(f3711,plain,
    ( spl5_87
  <=> k1_xboole_0 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).

fof(f3735,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_tarski(sK1)))
    | spl5_87 ),
    inference(unit_resulting_resolution,[],[f3712,f126])).

fof(f3712,plain,
    ( k1_xboole_0 != k1_tarski(sK1)
    | spl5_87 ),
    inference(avatar_component_clause,[],[f3711])).

fof(f4709,plain,
    ( spl5_107
    | ~ spl5_19
    | ~ spl5_51 ),
    inference(avatar_split_clause,[],[f4040,f2061,f527,f4707])).

fof(f4707,plain,
    ( spl5_107
  <=> ! [X0] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,X0))
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),k1_tarski(sK0))
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_107])])).

fof(f2061,plain,
    ( spl5_51
  <=> ! [X0] :
        ( r2_hidden(sK3(k1_tarski(sK0),sK2,X0),X0)
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),k1_tarski(sK0))
        | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X0)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f4040,plain,
    ( ! [X0] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,X0))
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),k1_tarski(sK0))
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),X0) )
    | ~ spl5_19
    | ~ spl5_51 ),
    inference(backward_demodulation,[],[f2062,f3992])).

fof(f3992,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK1))
    | ~ spl5_19 ),
    inference(unit_resulting_resolution,[],[f2032,f86])).

fof(f2062,plain,
    ( ! [X0] :
        ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X0)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),k1_tarski(sK0))
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),X0) )
    | ~ spl5_51 ),
    inference(avatar_component_clause,[],[f2061])).

fof(f4705,plain,
    ( ~ spl5_106
    | spl5_87 ),
    inference(avatar_split_clause,[],[f3733,f3711,f4703])).

fof(f4703,plain,
    ( spl5_106
  <=> r2_hidden(k1_tarski(sK1),k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_106])])).

fof(f3733,plain,
    ( ~ r2_hidden(k1_tarski(sK1),k1_tarski(k1_xboole_0))
    | spl5_87 ),
    inference(unit_resulting_resolution,[],[f3712,f126])).

fof(f4688,plain,
    ( spl5_105
    | ~ spl5_19
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f4039,f2029,f527,f4686])).

fof(f4686,plain,
    ( spl5_105
  <=> ! [X1] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,X1))
        | ~ r2_hidden(sK3(k1_tarski(sK0),sK2,X1),sK2)
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_105])])).

fof(f2029,plain,
    ( spl5_50
  <=> ! [X1] :
        ( r2_hidden(sK3(k1_tarski(sK0),sK2,X1),X1)
        | ~ r2_hidden(sK3(k1_tarski(sK0),sK2,X1),sK2)
        | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X1)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f4039,plain,
    ( ! [X1] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,X1))
        | ~ r2_hidden(sK3(k1_tarski(sK0),sK2,X1),sK2)
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X1),X1) )
    | ~ spl5_19
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f2030,f3992])).

fof(f2030,plain,
    ( ! [X1] :
        ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X1)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
        | ~ r2_hidden(sK3(k1_tarski(sK0),sK2,X1),sK2)
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X1),X1) )
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f2029])).

fof(f4684,plain,
    ( ~ spl5_104
    | spl5_84 ),
    inference(avatar_split_clause,[],[f3688,f3664,f4682])).

fof(f4682,plain,
    ( spl5_104
  <=> r2_hidden(k1_xboole_0,k1_tarski(k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).

fof(f3664,plain,
    ( spl5_84
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f3688,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_tarski(sK0)))
    | spl5_84 ),
    inference(unit_resulting_resolution,[],[f3665,f126])).

fof(f3665,plain,
    ( k1_xboole_0 != k1_tarski(sK0)
    | spl5_84 ),
    inference(avatar_component_clause,[],[f3664])).

fof(f4649,plain,
    ( ~ spl5_103
    | spl5_2
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f4534,f527,f253,f242,f144,f4647])).

fof(f4647,plain,
    ( spl5_103
  <=> r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_103])])).

fof(f4534,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2)))))))
    | spl5_2
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_19 ),
    inference(backward_demodulation,[],[f4479,f4524])).

fof(f4479,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2)))))))
    | spl5_2
    | ~ spl5_10
    | ~ spl5_19 ),
    inference(backward_demodulation,[],[f4338,f4464])).

fof(f4464,plain,
    ( k1_tarski(sK0) = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f4463,f94])).

fof(f4463,plain,
    ( k1_tarski(sK0) = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2))
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f587,f116])).

fof(f4338,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2)))))))
    | spl5_2
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f4337,f91])).

fof(f4337,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_xboole_0)))))))
    | spl5_2
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f165,f3992])).

fof(f165,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))))))))
    | spl5_2 ),
    inference(forward_demodulation,[],[f164,f90])).

fof(f164,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))))))))
    | spl5_2 ),
    inference(forward_demodulation,[],[f147,f90])).

fof(f147,plain,
    ( ~ r2_hidden(k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))))))))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f145,f126])).

fof(f4645,plain,
    ( ~ spl5_102
    | spl5_84 ),
    inference(avatar_split_clause,[],[f3686,f3664,f4643])).

fof(f4643,plain,
    ( spl5_102
  <=> r2_hidden(k1_tarski(sK0),k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).

fof(f3686,plain,
    ( ~ r2_hidden(k1_tarski(sK0),k1_tarski(k1_xboole_0))
    | spl5_84 ),
    inference(unit_resulting_resolution,[],[f3665,f126])).

fof(f4611,plain,
    ( ~ spl5_101
    | ~ spl5_8
    | ~ spl5_10
    | spl5_14
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f4532,f527,f341,f253,f242,f4609])).

fof(f4609,plain,
    ( spl5_101
  <=> r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_101])])).

fof(f341,plain,
    ( spl5_14
  <=> r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f4532,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))))))
    | ~ spl5_8
    | ~ spl5_10
    | spl5_14
    | ~ spl5_19 ),
    inference(backward_demodulation,[],[f4474,f4524])).

fof(f4474,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))))))
    | ~ spl5_10
    | spl5_14
    | ~ spl5_19 ),
    inference(backward_demodulation,[],[f4326,f4464])).

fof(f4326,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))))))))
    | spl5_14
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f4325,f91])).

fof(f4325,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_xboole_0))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))))))))
    | spl5_14
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f342,f3992])).

fof(f342,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))))))))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f341])).

fof(f4561,plain,
    ( ~ spl5_100
    | ~ spl5_8
    | ~ spl5_10
    | spl5_13
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f4533,f527,f323,f253,f242,f4559])).

fof(f323,plain,
    ( spl5_13
  <=> k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f4533,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))))
    | ~ spl5_8
    | ~ spl5_10
    | spl5_13
    | ~ spl5_19 ),
    inference(backward_demodulation,[],[f4475,f4524])).

fof(f4475,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))))
    | ~ spl5_10
    | spl5_13
    | ~ spl5_19 ),
    inference(backward_demodulation,[],[f4328,f4464])).

fof(f4328,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2)))))
    | spl5_13
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f4327,f91])).

fof(f4327,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_xboole_0)))))
    | spl5_13
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f324,f3992])).

fof(f324,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))))))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f323])).

fof(f4557,plain,
    ( ~ spl5_99
    | spl5_11 ),
    inference(avatar_split_clause,[],[f4432,f257,f4555])).

fof(f4432,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(sK2,sK2))
    | spl5_11 ),
    inference(unit_resulting_resolution,[],[f258,f258,f82])).

fof(f4543,plain,
    ( ~ spl5_97
    | ~ spl5_98
    | spl5_15
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f4227,f527,f443,f4541,f4538])).

fof(f4538,plain,
    ( spl5_97
  <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).

fof(f443,plain,
    ( spl5_15
  <=> k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f4227,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))
    | k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))))
    | spl5_15
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f4226,f91])).

fof(f4226,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k5_xboole_0(sK2,k1_xboole_0))
    | k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))))
    | spl5_15
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f4225,f3992])).

fof(f4225,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))))
    | ~ r1_tarski(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))
    | spl5_15
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f3764,f3992])).

fof(f3764,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | ~ r1_tarski(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))
    | spl5_15 ),
    inference(superposition,[],[f444,f93])).

fof(f444,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f443])).

fof(f4527,plain,
    ( ~ spl5_8
    | spl5_88 ),
    inference(avatar_contradiction_clause,[],[f4526])).

fof(f4526,plain,
    ( $false
    | ~ spl5_8
    | spl5_88 ),
    inference(subsumption_resolution,[],[f4524,f3731])).

fof(f3731,plain,
    ( k1_xboole_0 != k3_xboole_0(sK2,k1_tarski(sK0))
    | spl5_88 ),
    inference(avatar_component_clause,[],[f3730])).

fof(f3730,plain,
    ( spl5_88
  <=> k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).

fof(f4512,plain,
    ( ~ spl5_96
    | spl5_9
    | ~ spl5_10
    | spl5_18
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f4473,f527,f523,f253,f245,f4510])).

fof(f4510,plain,
    ( spl5_96
  <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).

fof(f245,plain,
    ( spl5_9
  <=> k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f4473,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))))))
    | spl5_9
    | ~ spl5_10
    | spl5_18
    | ~ spl5_19 ),
    inference(backward_demodulation,[],[f4218,f4464])).

fof(f4218,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))
    | spl5_9
    | spl5_18
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f3843,f3992])).

fof(f3843,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) != k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))
    | spl5_9
    | spl5_18 ),
    inference(forward_demodulation,[],[f3812,f94])).

fof(f3812,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) != k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2))))
    | spl5_9
    | spl5_18 ),
    inference(backward_demodulation,[],[f246,f3806])).

fof(f3806,plain,
    ( sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))
    | spl5_18 ),
    inference(unit_resulting_resolution,[],[f1325,f113])).

fof(f246,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))))))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f245])).

fof(f4506,plain,
    ( spl5_90
    | spl5_94 ),
    inference(avatar_contradiction_clause,[],[f4505])).

fof(f4505,plain,
    ( $false
    | spl5_90
    | spl5_94 ),
    inference(subsumption_resolution,[],[f4504,f91])).

fof(f4504,plain,
    ( k5_xboole_0(sK2,k1_xboole_0) != k5_xboole_0(k1_xboole_0,sK2)
    | spl5_90
    | spl5_94 ),
    inference(forward_demodulation,[],[f4503,f102])).

fof(f4503,plain,
    ( k5_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0))
    | spl5_90
    | spl5_94 ),
    inference(subsumption_resolution,[],[f4501,f4163])).

fof(f4163,plain,
    ( r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_90 ),
    inference(unit_resulting_resolution,[],[f4141,f81])).

fof(f4501,plain,
    ( k5_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_94 ),
    inference(superposition,[],[f4491,f86])).

fof(f4491,plain,
    ( k5_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | spl5_94 ),
    inference(avatar_component_clause,[],[f4490])).

fof(f4490,plain,
    ( spl5_94
  <=> k5_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).

fof(f4495,plain,
    ( ~ spl5_94
    | ~ spl5_95
    | spl5_15
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f4385,f527,f443,f4493,f4490])).

fof(f4385,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(k1_xboole_0,sK2))
    | k5_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | spl5_15
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f4384,f91])).

fof(f4384,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(sK2,k1_xboole_0))
    | k5_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | spl5_15
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f4379,f3992])).

fof(f4379,plain,
    ( k5_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | ~ r2_hidden(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))
    | spl5_15
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f4378,f91])).

fof(f4378,plain,
    ( k5_xboole_0(sK2,k1_xboole_0) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | ~ r2_hidden(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))
    | spl5_15
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f4377,f102])).

fof(f4377,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ r2_hidden(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))
    | spl5_15
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f535,f3992])).

fof(f535,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | ~ r2_hidden(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))
    | spl5_15 ),
    inference(forward_demodulation,[],[f460,f91])).

fof(f460,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k1_xboole_0)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | ~ r2_hidden(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))
    | spl5_15 ),
    inference(superposition,[],[f444,f118])).

fof(f4453,plain,
    ( ~ spl5_93
    | spl5_18
    | ~ spl5_19
    | spl5_25 ),
    inference(avatar_split_clause,[],[f4214,f632,f527,f523,f4451])).

fof(f4214,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))
    | spl5_18
    | ~ spl5_19
    | spl5_25 ),
    inference(forward_demodulation,[],[f3865,f3992])).

fof(f3865,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
    | spl5_18
    | spl5_25 ),
    inference(forward_demodulation,[],[f3819,f94])).

fof(f3819,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
    | spl5_18
    | spl5_25 ),
    inference(backward_demodulation,[],[f633,f3806])).

fof(f4414,plain,
    ( ~ spl5_92
    | spl5_15
    | spl5_18
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f4217,f527,f523,f443,f4412])).

fof(f4217,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))
    | spl5_15
    | spl5_18
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f3847,f3992])).

fof(f3847,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | spl5_15
    | spl5_18 ),
    inference(forward_demodulation,[],[f3813,f94])).

fof(f3813,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | spl5_15
    | spl5_18 ),
    inference(backward_demodulation,[],[f444,f3806])).

fof(f4383,plain,
    ( ~ spl5_8
    | spl5_18
    | spl5_39 ),
    inference(avatar_contradiction_clause,[],[f4382])).

fof(f4382,plain,
    ( $false
    | ~ spl5_8
    | spl5_18
    | spl5_39 ),
    inference(subsumption_resolution,[],[f932,f3839])).

fof(f3839,plain,
    ( ~ r1_xboole_0(sK2,k1_tarski(sK0))
    | spl5_18
    | spl5_39 ),
    inference(backward_demodulation,[],[f1311,f3806])).

fof(f1311,plain,
    ( ~ r1_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),k1_tarski(sK0))
    | spl5_39 ),
    inference(unit_resulting_resolution,[],[f1300,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1300,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))
    | spl5_39 ),
    inference(avatar_component_clause,[],[f1299])).

fof(f1299,plain,
    ( spl5_39
  <=> r1_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f4381,plain,
    ( ~ spl5_10
    | spl5_18
    | spl5_39 ),
    inference(avatar_contradiction_clause,[],[f4380])).

fof(f4380,plain,
    ( $false
    | ~ spl5_10
    | spl5_18
    | spl5_39 ),
    inference(subsumption_resolution,[],[f587,f3838])).

fof(f3838,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),sK2)
    | spl5_18
    | spl5_39 ),
    inference(backward_demodulation,[],[f1300,f3806])).

fof(f4205,plain,
    ( spl5_17
    | ~ spl5_19
    | spl5_90 ),
    inference(avatar_contradiction_clause,[],[f4204])).

fof(f4204,plain,
    ( $false
    | spl5_17
    | ~ spl5_19
    | spl5_90 ),
    inference(subsumption_resolution,[],[f4163,f4066])).

fof(f4066,plain,
    ( ~ r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_17
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f4065,f91])).

fof(f4065,plain,
    ( k5_xboole_0(sK2,k1_xboole_0) != k5_xboole_0(k1_xboole_0,sK2)
    | ~ r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_17
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f4001,f102])).

fof(f4001,plain,
    ( k5_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_17
    | ~ spl5_19 ),
    inference(backward_demodulation,[],[f497,f3992])).

fof(f497,plain,
    ( k5_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1))))
    | ~ r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_17 ),
    inference(forward_demodulation,[],[f496,f91])).

fof(f496,plain,
    ( k5_xboole_0(sK2,k1_xboole_0) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1))))
    | ~ r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_17 ),
    inference(forward_demodulation,[],[f494,f102])).

fof(f494,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_17 ),
    inference(superposition,[],[f487,f86])).

fof(f487,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f486])).

fof(f486,plain,
    ( spl5_17
  <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f4146,plain,
    ( spl5_91
    | ~ spl5_19
    | ~ spl5_49 ),
    inference(avatar_split_clause,[],[f4038,f1992,f527,f4144])).

fof(f4144,plain,
    ( spl5_91
  <=> ! [X0] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,X0))
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),k1_tarski(sK0))
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).

fof(f1992,plain,
    ( spl5_49
  <=> ! [X0] :
        ( r2_hidden(sK3(k1_tarski(sK0),sK2,X0),X0)
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),k1_tarski(sK0))
        | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X0)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f4038,plain,
    ( ! [X0] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,X0))
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),k1_tarski(sK0))
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),X0) )
    | ~ spl5_19
    | ~ spl5_49 ),
    inference(backward_demodulation,[],[f1993,f3992])).

fof(f1993,plain,
    ( ! [X0] :
        ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X0)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),k1_tarski(sK0))
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),X0) )
    | ~ spl5_49 ),
    inference(avatar_component_clause,[],[f1992])).

fof(f4142,plain,
    ( ~ spl5_90
    | spl5_71 ),
    inference(avatar_split_clause,[],[f3739,f2628,f4140])).

fof(f3739,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k1_xboole_0,sK2))
    | spl5_71 ),
    inference(resolution,[],[f2629,f96])).

fof(f2629,plain,
    ( ~ r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_71 ),
    inference(avatar_component_clause,[],[f2628])).

fof(f4124,plain,
    ( spl5_89
    | ~ spl5_19
    | ~ spl5_47 ),
    inference(avatar_split_clause,[],[f4037,f1957,f527,f4122])).

fof(f4122,plain,
    ( spl5_89
  <=> ! [X1] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,X1))
        | ~ r2_hidden(sK3(k1_tarski(sK0),sK2,X1),sK2)
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_89])])).

fof(f1957,plain,
    ( spl5_47
  <=> ! [X1] :
        ( r2_hidden(sK3(k1_tarski(sK0),sK2,X1),X1)
        | ~ r2_hidden(sK3(k1_tarski(sK0),sK2,X1),sK2)
        | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X1)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f4037,plain,
    ( ! [X1] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,X1))
        | ~ r2_hidden(sK3(k1_tarski(sK0),sK2,X1),sK2)
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X1),X1) )
    | ~ spl5_19
    | ~ spl5_47 ),
    inference(backward_demodulation,[],[f1958,f3992])).

fof(f1958,plain,
    ( ! [X1] :
        ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X1)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
        | ~ r2_hidden(sK3(k1_tarski(sK0),sK2,X1),sK2)
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X1),X1) )
    | ~ spl5_47 ),
    inference(avatar_component_clause,[],[f1957])).

fof(f3743,plain,
    ( spl5_16
    | ~ spl5_18
    | spl5_71 ),
    inference(avatar_contradiction_clause,[],[f3742])).

fof(f3742,plain,
    ( $false
    | spl5_16
    | ~ spl5_18
    | spl5_71 ),
    inference(subsumption_resolution,[],[f3739,f2759])).

fof(f2759,plain,
    ( r2_hidden(sK1,k5_xboole_0(k1_xboole_0,sK2))
    | spl5_16
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f483,f524,f85])).

fof(f3741,plain,
    ( spl5_16
    | ~ spl5_18
    | spl5_71 ),
    inference(avatar_contradiction_clause,[],[f3740])).

fof(f3740,plain,
    ( $false
    | spl5_16
    | ~ spl5_18
    | spl5_71 ),
    inference(subsumption_resolution,[],[f3738,f2759])).

fof(f3738,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k1_xboole_0,sK2))
    | spl5_71 ),
    inference(unit_resulting_resolution,[],[f2629,f96])).

fof(f3732,plain,
    ( ~ spl5_88
    | spl5_8 ),
    inference(avatar_split_clause,[],[f2024,f242,f3730])).

fof(f2024,plain,
    ( k1_xboole_0 != k3_xboole_0(sK2,k1_tarski(sK0))
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f243,f87])).

fof(f243,plain,
    ( ~ r1_xboole_0(sK2,k1_tarski(sK0))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f242])).

fof(f3713,plain,
    ( ~ spl5_87
    | ~ spl5_18
    | spl5_27 ),
    inference(avatar_split_clause,[],[f3378,f676,f523,f3711])).

fof(f676,plain,
    ( spl5_27
  <=> r1_xboole_0(k1_tarski(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f3378,plain,
    ( k1_xboole_0 != k1_tarski(sK1)
    | ~ spl5_18
    | spl5_27 ),
    inference(forward_demodulation,[],[f3377,f3209])).

fof(f3209,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_tarski(sK1),k1_tarski(sK1))
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f2776,f2747])).

fof(f2747,plain,
    ( k1_tarski(sK1) = k3_xboole_0(sK2,k1_tarski(sK1))
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f524,f80])).

fof(f2776,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_tarski(sK1),k3_xboole_0(sK2,k1_tarski(sK1)))
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f2767,f94])).

fof(f2767,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),sK2))
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f524,f118])).

fof(f3377,plain,
    ( k1_tarski(sK1) != k5_xboole_0(k1_tarski(sK1),k1_tarski(sK1))
    | ~ spl5_18
    | spl5_27 ),
    inference(forward_demodulation,[],[f3376,f2747])).

fof(f3376,plain,
    ( k1_tarski(sK1) != k5_xboole_0(k1_tarski(sK1),k3_xboole_0(sK2,k1_tarski(sK1)))
    | spl5_27 ),
    inference(forward_demodulation,[],[f3373,f94])).

fof(f3373,plain,
    ( k1_tarski(sK1) != k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),sK2))
    | spl5_27 ),
    inference(unit_resulting_resolution,[],[f677,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f72,f73])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f677,plain,
    ( ~ r1_xboole_0(k1_tarski(sK1),sK2)
    | spl5_27 ),
    inference(avatar_component_clause,[],[f676])).

fof(f3709,plain,
    ( spl5_86
    | ~ spl5_18
    | spl5_25 ),
    inference(avatar_split_clause,[],[f3303,f632,f523,f3707])).

fof(f3707,plain,
    ( spl5_86
  <=> ! [X2] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X2))))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X2),k1_tarski(sK1))
        | ~ r2_hidden(sK3(sK2,k1_tarski(sK1),X2),sK2)
        | ~ r2_hidden(sK3(sK2,k1_tarski(sK1),X2),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).

fof(f3303,plain,
    ( ! [X2] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X2))))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X2),k1_tarski(sK1))
        | ~ r2_hidden(sK3(sK2,k1_tarski(sK1),X2),sK2)
        | ~ r2_hidden(sK3(sK2,k1_tarski(sK1),X2),X2) )
    | ~ spl5_18
    | spl5_25 ),
    inference(forward_demodulation,[],[f646,f2747])).

fof(f646,plain,
    ( ! [X2] :
        ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X2),k1_tarski(sK1))
        | ~ r2_hidden(sK3(sK2,k1_tarski(sK1),X2),sK2)
        | ~ r2_hidden(sK3(sK2,k1_tarski(sK1),X2),X2) )
    | spl5_25 ),
    inference(superposition,[],[f633,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f68,f73])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3685,plain,
    ( spl5_85
    | spl5_15
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f3312,f523,f443,f3683])).

fof(f3683,plain,
    ( spl5_85
  <=> ! [X2] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X2))))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X2),k1_tarski(sK1))
        | ~ r2_hidden(sK3(sK2,k1_tarski(sK1),X2),sK2)
        | ~ r2_hidden(sK3(sK2,k1_tarski(sK1),X2),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).

fof(f3312,plain,
    ( ! [X2] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X2))))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X2),k1_tarski(sK1))
        | ~ r2_hidden(sK3(sK2,k1_tarski(sK1),X2),sK2)
        | ~ r2_hidden(sK3(sK2,k1_tarski(sK1),X2),X2) )
    | spl5_15
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f457,f2747])).

fof(f457,plain,
    ( ! [X2] :
        ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X2),k1_tarski(sK1))
        | ~ r2_hidden(sK3(sK2,k1_tarski(sK1),X2),sK2)
        | ~ r2_hidden(sK3(sK2,k1_tarski(sK1),X2),X2) )
    | spl5_15 ),
    inference(superposition,[],[f444,f107])).

fof(f3666,plain,
    ( ~ spl5_84
    | spl5_10
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f1293,f257,f253,f3664])).

fof(f1293,plain,
    ( k1_xboole_0 != k1_tarski(sK0)
    | spl5_10
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f1292,f1215])).

fof(f1215,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f1164,f1143])).

fof(f1143,plain,
    ( k1_tarski(sK0) = k3_xboole_0(sK2,k1_tarski(sK0))
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f326,f80])).

fof(f1164,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f1157,f94])).

fof(f1157,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2))
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f326,f118])).

fof(f1292,plain,
    ( k1_tarski(sK0) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | spl5_10
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f1291,f1143])).

fof(f1291,plain,
    ( k1_tarski(sK0) != k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))
    | spl5_10 ),
    inference(forward_demodulation,[],[f1288,f94])).

fof(f1288,plain,
    ( k1_tarski(sK0) != k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2))
    | spl5_10 ),
    inference(unit_resulting_resolution,[],[f254,f115])).

fof(f254,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),sK2)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f253])).

fof(f3662,plain,
    ( spl5_83
    | ~ spl5_18
    | spl5_25 ),
    inference(avatar_split_clause,[],[f3304,f632,f523,f3660])).

fof(f3660,plain,
    ( spl5_83
  <=> ! [X1] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1))))
        | ~ r2_hidden(sK3(sK2,k1_tarski(sK1),X1),k1_tarski(sK1))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).

fof(f3304,plain,
    ( ! [X1] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1))))
        | ~ r2_hidden(sK3(sK2,k1_tarski(sK1),X1),k1_tarski(sK1))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X1),X1) )
    | ~ spl5_18
    | spl5_25 ),
    inference(forward_demodulation,[],[f645,f2747])).

fof(f645,plain,
    ( ! [X1] :
        ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
        | ~ r2_hidden(sK3(sK2,k1_tarski(sK1),X1),k1_tarski(sK1))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X1),X1) )
    | spl5_25 ),
    inference(superposition,[],[f633,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f67,f73])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3641,plain,
    ( spl5_82
    | ~ spl5_18
    | spl5_25 ),
    inference(avatar_split_clause,[],[f3305,f632,f523,f3639])).

fof(f3639,plain,
    ( spl5_82
  <=> ! [X0] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0))))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),sK2)
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).

fof(f3305,plain,
    ( ! [X0] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0))))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),sK2)
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),X0) )
    | ~ spl5_18
    | spl5_25 ),
    inference(forward_demodulation,[],[f644,f2747])).

fof(f644,plain,
    ( ! [X0] :
        ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),sK2)
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),X0) )
    | spl5_25 ),
    inference(superposition,[],[f633,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f66,f73])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3618,plain,
    ( spl5_81
    | spl5_15
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f3313,f523,f443,f3616])).

fof(f3616,plain,
    ( spl5_81
  <=> ! [X1] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1))))
        | ~ r2_hidden(sK3(sK2,k1_tarski(sK1),X1),k1_tarski(sK1))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).

fof(f3313,plain,
    ( ! [X1] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1))))
        | ~ r2_hidden(sK3(sK2,k1_tarski(sK1),X1),k1_tarski(sK1))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X1),X1) )
    | spl5_15
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f456,f2747])).

fof(f456,plain,
    ( ! [X1] :
        ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
        | ~ r2_hidden(sK3(sK2,k1_tarski(sK1),X1),k1_tarski(sK1))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X1),X1) )
    | spl5_15 ),
    inference(superposition,[],[f444,f108])).

fof(f3597,plain,
    ( spl5_80
    | ~ spl5_18
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f3267,f2093,f523,f3595])).

fof(f3595,plain,
    ( spl5_80
  <=> ! [X0] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0))))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),sK2)
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f2093,plain,
    ( spl5_52
  <=> ! [X0] :
        ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),sK2)
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f3267,plain,
    ( ! [X0] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0))))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),sK2)
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),X0) )
    | ~ spl5_18
    | ~ spl5_52 ),
    inference(forward_demodulation,[],[f2094,f2747])).

fof(f2094,plain,
    ( ! [X0] :
        ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),sK2)
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),X0) )
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f2093])).

fof(f3572,plain,
    ( ~ spl5_42
    | ~ spl5_79
    | spl5_2
    | ~ spl5_11
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f3242,f523,f257,f144,f3570,f1480])).

fof(f1480,plain,
    ( spl5_42
  <=> r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f3570,plain,
    ( spl5_79
  <=> k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_tarski(sK1)))))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).

fof(f3242,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_tarski(sK1)))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))
    | ~ r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_2
    | ~ spl5_11
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f1219,f2747])).

fof(f1219,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))
    | ~ r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_2
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f1192,f1143])).

fof(f1192,plain,
    ( ~ r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK0)))))
    | spl5_2
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f1170,f91])).

fof(f1170,plain,
    ( ~ r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_xboole_0))
    | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK0)))))
    | spl5_2
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f179,f1164])).

fof(f179,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK0)))))
    | ~ r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))
    | spl5_2 ),
    inference(forward_demodulation,[],[f178,f91])).

fof(f178,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k1_xboole_0)))
    | ~ r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))
    | spl5_2 ),
    inference(forward_demodulation,[],[f177,f90])).

fof(f177,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))),k1_xboole_0))
    | ~ r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))
    | spl5_2 ),
    inference(forward_demodulation,[],[f155,f90])).

fof(f155,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))),k1_xboole_0)
    | ~ r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))
    | spl5_2 ),
    inference(superposition,[],[f145,f86])).

fof(f3552,plain,
    ( ~ spl5_78
    | spl5_9
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f3211,f523,f245,f3550])).

fof(f3550,plain,
    ( spl5_78
  <=> k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_tarski(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f3211,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_tarski(sK1))))))
    | spl5_9
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f246,f2747])).

fof(f3532,plain,
    ( spl5_77
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f2622,f1055,f3530])).

fof(f3530,plain,
    ( spl5_77
  <=> r1_xboole_0(k1_xboole_0,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).

fof(f1055,plain,
    ( spl5_35
  <=> r1_xboole_0(k1_tarski(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f2622,plain,
    ( r1_xboole_0(k1_xboole_0,k1_tarski(sK0))
    | ~ spl5_35 ),
    inference(unit_resulting_resolution,[],[f1056,f88])).

fof(f1056,plain,
    ( r1_xboole_0(k1_tarski(sK0),k1_xboole_0)
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f1055])).

fof(f3480,plain,
    ( ~ spl5_76
    | ~ spl5_18
    | spl5_46 ),
    inference(avatar_split_clause,[],[f3274,f1916,f523,f3478])).

fof(f3478,plain,
    ( spl5_76
  <=> k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f1916,plain,
    ( spl5_46
  <=> k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f3274,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK1)))
    | ~ spl5_18
    | spl5_46 ),
    inference(forward_demodulation,[],[f1917,f2747])).

fof(f1917,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1))))
    | spl5_46 ),
    inference(avatar_component_clause,[],[f1916])).

fof(f3447,plain,
    ( ~ spl5_75
    | spl5_32 ),
    inference(avatar_split_clause,[],[f2562,f988,f3445])).

fof(f3445,plain,
    ( spl5_75
  <=> r1_tarski(k1_tarski(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f2562,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k1_xboole_0)
    | spl5_32 ),
    inference(unit_resulting_resolution,[],[f989,f95])).

fof(f3443,plain,
    ( ~ spl5_74
    | ~ spl5_18
    | spl5_28 ),
    inference(avatar_split_clause,[],[f3296,f680,f523,f3441])).

fof(f680,plain,
    ( spl5_28
  <=> k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK1)))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f3296,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl5_18
    | spl5_28 ),
    inference(forward_demodulation,[],[f681,f2747])).

fof(f681,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
    | spl5_28 ),
    inference(avatar_component_clause,[],[f680])).

fof(f3391,plain,
    ( ~ spl5_73
    | ~ spl5_18
    | spl5_43 ),
    inference(avatar_split_clause,[],[f3279,f1483,f523,f3389])).

fof(f3389,plain,
    ( spl5_73
  <=> k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f1483,plain,
    ( spl5_43
  <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f3279,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK1)))
    | ~ spl5_18
    | spl5_43 ),
    inference(forward_demodulation,[],[f1484,f2747])).

fof(f1484,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))
    | spl5_43 ),
    inference(avatar_component_clause,[],[f1483])).

fof(f3206,plain,
    ( spl5_16
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f3205])).

fof(f3205,plain,
    ( $false
    | spl5_16
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f3204,f2759])).

fof(f3204,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k1_xboole_0,sK2))
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f2989,f91])).

fof(f2989,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(sK2,k1_xboole_0))
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(backward_demodulation,[],[f2792,f2793])).

fof(f2793,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f2747,f2097])).

fof(f2097,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK1))
    | ~ spl5_19 ),
    inference(unit_resulting_resolution,[],[f2032,f86])).

fof(f2792,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(sK2,k1_tarski(sK1)))
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f2751,f91])).

fof(f2751,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k1_tarski(sK1),sK2))
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f125,f524,f83])).

fof(f3201,plain,
    ( spl5_16
    | ~ spl5_18
    | ~ spl5_19
    | spl5_66 ),
    inference(avatar_contradiction_clause,[],[f3200])).

fof(f3200,plain,
    ( $false
    | spl5_16
    | ~ spl5_18
    | ~ spl5_19
    | spl5_66 ),
    inference(subsumption_resolution,[],[f3199,f2620])).

fof(f2620,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,sK2)))
    | spl5_16
    | spl5_66 ),
    inference(forward_demodulation,[],[f2619,f91])).

fof(f2619,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,k1_xboole_0)))
    | spl5_16
    | spl5_66 ),
    inference(forward_demodulation,[],[f2587,f90])).

fof(f2587,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k5_xboole_0(sK2,sK2),k1_xboole_0))
    | spl5_16
    | spl5_66 ),
    inference(unit_resulting_resolution,[],[f483,f2459,f82])).

fof(f3199,plain,
    ( r2_hidden(sK1,k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,sK2)))
    | ~ spl5_18
    | ~ spl5_19
    | spl5_66 ),
    inference(forward_demodulation,[],[f2972,f91])).

fof(f2972,plain,
    ( r2_hidden(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,k1_xboole_0)))
    | ~ spl5_18
    | ~ spl5_19
    | spl5_66 ),
    inference(backward_demodulation,[],[f2611,f2793])).

fof(f2611,plain,
    ( r2_hidden(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,k1_tarski(sK1))))
    | spl5_66 ),
    inference(forward_demodulation,[],[f2597,f90])).

fof(f2597,plain,
    ( r2_hidden(sK1,k5_xboole_0(k5_xboole_0(sK2,sK2),k1_tarski(sK1)))
    | spl5_66 ),
    inference(unit_resulting_resolution,[],[f125,f2459,f85])).

fof(f3198,plain,
    ( spl5_16
    | ~ spl5_18
    | ~ spl5_19
    | spl5_66 ),
    inference(avatar_contradiction_clause,[],[f3197])).

fof(f3197,plain,
    ( $false
    | spl5_16
    | ~ spl5_18
    | ~ spl5_19
    | spl5_66 ),
    inference(subsumption_resolution,[],[f2969,f1120])).

fof(f1120,plain,
    ( ! [X0] : ~ r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)))
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f483,f123])).

fof(f2969,plain,
    ( r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(sK2,sK2))))
    | ~ spl5_18
    | ~ spl5_19
    | spl5_66 ),
    inference(backward_demodulation,[],[f2603,f2793])).

fof(f2603,plain,
    ( r2_hidden(sK1,k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,sK2))))
    | spl5_66 ),
    inference(unit_resulting_resolution,[],[f125,f2459,f121])).

fof(f121,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f110])).

fof(f110,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f65,f73])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3196,plain,
    ( spl5_16
    | ~ spl5_18
    | ~ spl5_19
    | spl5_66 ),
    inference(avatar_contradiction_clause,[],[f3195])).

fof(f3195,plain,
    ( $false
    | spl5_16
    | ~ spl5_18
    | ~ spl5_19
    | spl5_66 ),
    inference(subsumption_resolution,[],[f2966,f2592])).

fof(f2592,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,sK2)))
    | spl5_16
    | spl5_66 ),
    inference(unit_resulting_resolution,[],[f483,f2459,f82])).

fof(f2966,plain,
    ( r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,sK2)))
    | ~ spl5_18
    | ~ spl5_19
    | spl5_66 ),
    inference(backward_demodulation,[],[f2596,f2793])).

fof(f2596,plain,
    ( r2_hidden(sK1,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,sK2)))
    | spl5_66 ),
    inference(unit_resulting_resolution,[],[f125,f2459,f84])).

fof(f3152,plain,
    ( spl5_3
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_61 ),
    inference(avatar_contradiction_clause,[],[f3151])).

fof(f3151,plain,
    ( $false
    | spl5_3
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_61 ),
    inference(subsumption_resolution,[],[f2950,f102])).

fof(f2950,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl5_3
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_61 ),
    inference(backward_demodulation,[],[f2506,f2793])).

fof(f3085,plain,
    ( ~ spl5_18
    | ~ spl5_19
    | spl5_48 ),
    inference(avatar_contradiction_clause,[],[f3084])).

fof(f3084,plain,
    ( $false
    | ~ spl5_18
    | ~ spl5_19
    | spl5_48 ),
    inference(subsumption_resolution,[],[f2880,f128])).

fof(f128,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2880,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl5_18
    | ~ spl5_19
    | spl5_48 ),
    inference(backward_demodulation,[],[f1989,f2793])).

fof(f3031,plain,
    ( spl5_16
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f3030])).

fof(f3030,plain,
    ( $false
    | spl5_16
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f3029,f483])).

fof(f3029,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | spl5_16
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f2844,f102])).

fof(f2844,plain,
    ( r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k1_xboole_0))
    | spl5_16
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(backward_demodulation,[],[f1113,f2793])).

fof(f2992,plain,
    ( spl5_3
    | spl5_16
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f2991])).

fof(f2991,plain,
    ( $false
    | spl5_3
    | spl5_16
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f2990,f1127])).

fof(f1127,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))
    | spl5_3
    | spl5_16 ),
    inference(forward_demodulation,[],[f1109,f91])).

fof(f1109,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k1_tarski(sK0),k1_xboole_0))
    | spl5_3
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f183,f483,f82])).

fof(f2990,plain,
    ( r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))
    | spl5_3
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f2796,f91])).

fof(f2796,plain,
    ( r2_hidden(sK1,k5_xboole_0(k1_tarski(sK0),k1_xboole_0))
    | spl5_3
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(backward_demodulation,[],[f195,f2793])).

fof(f2790,plain,
    ( spl5_16
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f2789])).

fof(f2789,plain,
    ( $false
    | spl5_16
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f2788,f483])).

fof(f2788,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f2757,f2097])).

fof(f2757,plain,
    ( r2_hidden(sK1,k3_xboole_0(sK2,k1_tarski(sK1)))
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f120,f524,f84])).

fof(f2782,plain,
    ( ~ spl5_18
    | ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f2781])).

fof(f2781,plain,
    ( $false
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f2780,f102])).

fof(f2780,plain,
    ( sK2 != k5_xboole_0(sK2,k1_xboole_0)
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f2766,f2097])).

fof(f2766,plain,
    ( sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f524,f114])).

fof(f2779,plain,
    ( spl5_3
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_61 ),
    inference(avatar_contradiction_clause,[],[f2778])).

fof(f2778,plain,
    ( $false
    | spl5_3
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_61 ),
    inference(subsumption_resolution,[],[f2777,f2506])).

fof(f2777,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_tarski(sK1),k1_xboole_0)
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f2776,f2097])).

fof(f2634,plain,
    ( spl5_72
    | spl5_18 ),
    inference(avatar_split_clause,[],[f1737,f523,f2632])).

fof(f1737,plain,
    ( r2_hidden(sK1,k5_xboole_0(sK2,k1_tarski(sK1)))
    | spl5_18 ),
    inference(unit_resulting_resolution,[],[f125,f1325,f85])).

fof(f2630,plain,
    ( ~ spl5_71
    | spl5_30 ),
    inference(avatar_split_clause,[],[f940,f861,f2628])).

fof(f861,plain,
    ( spl5_30
  <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f940,plain,
    ( ~ r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_30 ),
    inference(trivial_inequality_removal,[],[f938])).

fof(f938,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK1))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK1)))
    | ~ r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_30 ),
    inference(superposition,[],[f862,f93])).

fof(f862,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK1)))
    | spl5_30 ),
    inference(avatar_component_clause,[],[f861])).

fof(f2531,plain,
    ( spl5_70
    | ~ spl5_19
    | spl5_25 ),
    inference(avatar_split_clause,[],[f2109,f632,f527,f2529])).

fof(f2529,plain,
    ( spl5_70
  <=> ! [X2] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X2))))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X2),k1_tarski(sK1))
        | ~ r2_hidden(sK3(sK2,k1_tarski(sK1),X2),sK2)
        | ~ r2_hidden(sK3(sK2,k1_tarski(sK1),X2),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f2109,plain,
    ( ! [X2] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X2))))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X2),k1_tarski(sK1))
        | ~ r2_hidden(sK3(sK2,k1_tarski(sK1),X2),sK2)
        | ~ r2_hidden(sK3(sK2,k1_tarski(sK1),X2),X2) )
    | ~ spl5_19
    | spl5_25 ),
    inference(backward_demodulation,[],[f646,f2097])).

fof(f2527,plain,
    ( ~ spl5_32
    | spl5_4
    | ~ spl5_61 ),
    inference(avatar_split_clause,[],[f2501,f2382,f186,f988])).

fof(f2501,plain,
    ( ~ r2_hidden(sK0,k1_xboole_0)
    | spl5_4
    | ~ spl5_61 ),
    inference(backward_demodulation,[],[f226,f2499])).

fof(f226,plain,
    ( ~ r2_hidden(sK0,k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | spl5_4 ),
    inference(forward_demodulation,[],[f216,f94])).

fof(f216,plain,
    ( ~ r2_hidden(sK0,k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f120,f187,f85])).

fof(f2510,plain,
    ( spl5_69
    | spl5_15
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f2100,f527,f443,f2508])).

fof(f2508,plain,
    ( spl5_69
  <=> ! [X2] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X2))))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X2),k1_tarski(sK1))
        | ~ r2_hidden(sK3(sK2,k1_tarski(sK1),X2),sK2)
        | ~ r2_hidden(sK3(sK2,k1_tarski(sK1),X2),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).

fof(f2100,plain,
    ( ! [X2] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X2))))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X2),k1_tarski(sK1))
        | ~ r2_hidden(sK3(sK2,k1_tarski(sK1),X2),sK2)
        | ~ r2_hidden(sK3(sK2,k1_tarski(sK1),X2),X2) )
    | spl5_15
    | ~ spl5_19 ),
    inference(backward_demodulation,[],[f457,f2097])).

fof(f2484,plain,
    ( spl5_68
    | spl5_18
    | ~ spl5_19
    | spl5_25 ),
    inference(avatar_split_clause,[],[f2139,f632,f527,f523,f2482])).

fof(f2482,plain,
    ( spl5_68
  <=> ! [X2] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,X2))
        | ~ r2_hidden(sK3(k1_tarski(sK0),sK2,X2),X2)
        | ~ r2_hidden(sK3(k1_tarski(sK0),sK2,X2),k1_tarski(sK0))
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X2),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f2139,plain,
    ( ! [X2] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,X2))
        | ~ r2_hidden(sK3(k1_tarski(sK0),sK2,X2),X2)
        | ~ r2_hidden(sK3(k1_tarski(sK0),sK2,X2),k1_tarski(sK0))
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X2),sK2) )
    | spl5_18
    | ~ spl5_19
    | spl5_25 ),
    inference(backward_demodulation,[],[f1820,f2097])).

fof(f1820,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK3(k1_tarski(sK0),sK2,X2),X2)
        | ~ r2_hidden(sK3(k1_tarski(sK0),sK2,X2),k1_tarski(sK0))
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X2),sK2)
        | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X2)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) )
    | spl5_18
    | spl5_25 ),
    inference(forward_demodulation,[],[f1819,f1741])).

fof(f1741,plain,
    ( sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))
    | spl5_18 ),
    inference(unit_resulting_resolution,[],[f1325,f113])).

fof(f1819,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK3(k1_tarski(sK0),sK2,X2),k1_tarski(sK0))
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X2),sK2)
        | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X2)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
        | ~ r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X2),X2) )
    | spl5_18
    | spl5_25 ),
    inference(forward_demodulation,[],[f1760,f1741])).

fof(f1760,plain,
    ( ! [X2] :
        ( r2_hidden(sK3(k1_tarski(sK0),sK2,X2),sK2)
        | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X2)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
        | ~ r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X2),k1_tarski(sK0))
        | ~ r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X2),X2) )
    | spl5_18
    | spl5_25 ),
    inference(backward_demodulation,[],[f653,f1741])).

fof(f653,plain,
    ( ! [X2] :
        ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X2)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
        | r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X2),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))
        | ~ r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X2),k1_tarski(sK0))
        | ~ r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X2),X2) )
    | spl5_25 ),
    inference(superposition,[],[f633,f107])).

fof(f2464,plain,
    ( spl5_67
    | spl5_15
    | spl5_18
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f2138,f527,f523,f443,f2462])).

fof(f2462,plain,
    ( spl5_67
  <=> ! [X2] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,X2))
        | ~ r2_hidden(sK3(k1_tarski(sK0),sK2,X2),X2)
        | ~ r2_hidden(sK3(k1_tarski(sK0),sK2,X2),k1_tarski(sK0))
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X2),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f2138,plain,
    ( ! [X2] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,X2))
        | ~ r2_hidden(sK3(k1_tarski(sK0),sK2,X2),X2)
        | ~ r2_hidden(sK3(k1_tarski(sK0),sK2,X2),k1_tarski(sK0))
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X2),sK2) )
    | spl5_15
    | spl5_18
    | ~ spl5_19 ),
    inference(backward_demodulation,[],[f1794,f2097])).

fof(f1794,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK3(k1_tarski(sK0),sK2,X2),X2)
        | ~ r2_hidden(sK3(k1_tarski(sK0),sK2,X2),k1_tarski(sK0))
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X2),sK2)
        | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X2)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) )
    | spl5_15
    | spl5_18 ),
    inference(forward_demodulation,[],[f1793,f1741])).

fof(f1793,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK3(k1_tarski(sK0),sK2,X2),k1_tarski(sK0))
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X2),sK2)
        | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X2)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
        | ~ r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X2),X2) )
    | spl5_15
    | spl5_18 ),
    inference(forward_demodulation,[],[f1752,f1741])).

fof(f1752,plain,
    ( ! [X2] :
        ( r2_hidden(sK3(k1_tarski(sK0),sK2,X2),sK2)
        | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X2)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
        | ~ r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X2),k1_tarski(sK0))
        | ~ r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X2),X2) )
    | spl5_15
    | spl5_18 ),
    inference(backward_demodulation,[],[f464,f1741])).

fof(f464,plain,
    ( ! [X2] :
        ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X2)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
        | r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X2),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))
        | ~ r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X2),k1_tarski(sK0))
        | ~ r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X2),X2) )
    | spl5_15 ),
    inference(superposition,[],[f444,f107])).

fof(f2460,plain,
    ( ~ spl5_66
    | spl5_18 ),
    inference(avatar_split_clause,[],[f1734,f523,f2458])).

fof(f1734,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(sK2,sK2))
    | spl5_18 ),
    inference(unit_resulting_resolution,[],[f1325,f1325,f82])).

fof(f2438,plain,
    ( spl5_65
    | ~ spl5_19
    | spl5_25 ),
    inference(avatar_split_clause,[],[f2108,f632,f527,f2436])).

fof(f2436,plain,
    ( spl5_65
  <=> ! [X1] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1))))
        | ~ r2_hidden(sK3(sK2,k1_tarski(sK1),X1),k1_tarski(sK1))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).

fof(f2108,plain,
    ( ! [X1] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1))))
        | ~ r2_hidden(sK3(sK2,k1_tarski(sK1),X1),k1_tarski(sK1))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X1),X1) )
    | ~ spl5_19
    | spl5_25 ),
    inference(backward_demodulation,[],[f645,f2097])).

fof(f2412,plain,
    ( spl5_64
    | ~ spl5_19
    | spl5_25 ),
    inference(avatar_split_clause,[],[f2107,f632,f527,f2410])).

fof(f2410,plain,
    ( spl5_64
  <=> ! [X0] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0))))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),sK2)
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f2107,plain,
    ( ! [X0] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0))))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),sK2)
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),X0) )
    | ~ spl5_19
    | spl5_25 ),
    inference(backward_demodulation,[],[f644,f2097])).

fof(f2408,plain,
    ( ~ spl5_63
    | spl5_4 ),
    inference(avatar_split_clause,[],[f217,f186,f2406])).

fof(f2406,plain,
    ( spl5_63
  <=> r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f217,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k1_tarski(sK1))
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f187,f95])).

fof(f2388,plain,
    ( spl5_62
    | spl5_15
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f2099,f527,f443,f2386])).

fof(f2386,plain,
    ( spl5_62
  <=> ! [X1] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1))))
        | ~ r2_hidden(sK3(sK2,k1_tarski(sK1),X1),k1_tarski(sK1))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f2099,plain,
    ( ! [X1] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1))))
        | ~ r2_hidden(sK3(sK2,k1_tarski(sK1),X1),k1_tarski(sK1))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X1),X1) )
    | spl5_15
    | ~ spl5_19 ),
    inference(backward_demodulation,[],[f456,f2097])).

fof(f2384,plain,
    ( spl5_61
    | spl5_4 ),
    inference(avatar_split_clause,[],[f209,f186,f2382])).

fof(f209,plain,
    ( r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f187,f81])).

fof(f2364,plain,
    ( spl5_60
    | ~ spl5_19
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f2193,f2093,f527,f2362])).

fof(f2362,plain,
    ( spl5_60
  <=> ! [X0] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0))))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),sK2)
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f2193,plain,
    ( ! [X0] :
        ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0))))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),sK2)
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),X0) )
    | ~ spl5_19
    | ~ spl5_52 ),
    inference(backward_demodulation,[],[f2094,f2097])).

fof(f2360,plain,
    ( ~ spl5_59
    | spl5_3 ),
    inference(avatar_split_clause,[],[f197,f182,f2358])).

fof(f2358,plain,
    ( spl5_59
  <=> r1_tarski(k1_tarski(sK1),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f197,plain,
    ( ~ r1_tarski(k1_tarski(sK1),k1_tarski(sK0))
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f183,f95])).

fof(f2347,plain,
    ( ~ spl5_58
    | ~ spl5_19
    | spl5_46 ),
    inference(avatar_split_clause,[],[f2252,f1916,f527,f2345])).

fof(f2345,plain,
    ( spl5_58
  <=> k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) = k5_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f2252,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) != k5_xboole_0(k1_xboole_0,sK2)
    | ~ spl5_19
    | spl5_46 ),
    inference(forward_demodulation,[],[f2251,f91])).

fof(f2251,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) != k5_xboole_0(sK2,k1_xboole_0)
    | ~ spl5_19
    | spl5_46 ),
    inference(forward_demodulation,[],[f2151,f102])).

fof(f2151,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl5_19
    | spl5_46 ),
    inference(backward_demodulation,[],[f1917,f2097])).

fof(f2329,plain,
    ( ~ spl5_57
    | ~ spl5_19
    | spl5_28 ),
    inference(avatar_split_clause,[],[f2211,f680,f527,f2327])).

fof(f2211,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
    | ~ spl5_19
    | spl5_28 ),
    inference(forward_demodulation,[],[f2116,f91])).

fof(f2116,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_xboole_0)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
    | ~ spl5_19
    | spl5_28 ),
    inference(backward_demodulation,[],[f681,f2097])).

fof(f2314,plain,
    ( ~ spl5_56
    | ~ spl5_19
    | spl5_26 ),
    inference(avatar_split_clause,[],[f2206,f663,f527,f2312])).

fof(f2312,plain,
    ( spl5_56
  <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f663,plain,
    ( spl5_26
  <=> k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK1)))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f2206,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | ~ spl5_19
    | spl5_26 ),
    inference(forward_demodulation,[],[f2110,f91])).

fof(f2110,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_xboole_0)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | ~ spl5_19
    | spl5_26 ),
    inference(backward_demodulation,[],[f664,f2097])).

fof(f664,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | spl5_26 ),
    inference(avatar_component_clause,[],[f663])).

fof(f2310,plain,
    ( spl5_55
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f1305,f531,f2308])).

fof(f2308,plain,
    ( spl5_55
  <=> r1_xboole_0(k1_xboole_0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).

fof(f531,plain,
    ( spl5_20
  <=> r1_xboole_0(k1_tarski(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f1305,plain,
    ( r1_xboole_0(k1_xboole_0,k1_tarski(sK1))
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f532,f88])).

fof(f532,plain,
    ( r1_xboole_0(k1_tarski(sK1),k1_xboole_0)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f531])).

fof(f2299,plain,
    ( ~ spl5_54
    | ~ spl5_19
    | spl5_37 ),
    inference(avatar_split_clause,[],[f2222,f1274,f527,f2297])).

fof(f2297,plain,
    ( spl5_54
  <=> k5_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f1274,plain,
    ( spl5_37
  <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f2222,plain,
    ( k5_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
    | ~ spl5_19
    | spl5_37 ),
    inference(forward_demodulation,[],[f2221,f91])).

fof(f2221,plain,
    ( k5_xboole_0(sK2,k1_xboole_0) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
    | ~ spl5_19
    | spl5_37 ),
    inference(forward_demodulation,[],[f2127,f102])).

fof(f2127,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
    | ~ spl5_19
    | spl5_37 ),
    inference(backward_demodulation,[],[f1275,f2097])).

fof(f1275,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
    | spl5_37 ),
    inference(avatar_component_clause,[],[f1274])).

fof(f2295,plain,
    ( spl5_23
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f1153,f257,f597])).

fof(f597,plain,
    ( spl5_23
  <=> r1_tarski(k1_tarski(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f1153,plain,
    ( r1_tarski(k1_tarski(sK0),sK2)
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f326,f96])).

fof(f2288,plain,
    ( ~ spl5_53
    | ~ spl5_19
    | spl5_43 ),
    inference(avatar_split_clause,[],[f2234,f1483,f527,f2286])).

fof(f2286,plain,
    ( spl5_53
  <=> k5_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f2234,plain,
    ( k5_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))
    | ~ spl5_19
    | spl5_43 ),
    inference(forward_demodulation,[],[f2233,f91])).

fof(f2233,plain,
    ( k5_xboole_0(sK2,k1_xboole_0) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))
    | ~ spl5_19
    | spl5_43 ),
    inference(forward_demodulation,[],[f2134,f102])).

fof(f2134,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl5_19
    | spl5_43 ),
    inference(backward_demodulation,[],[f1484,f2097])).

fof(f2095,plain,
    ( spl5_52
    | spl5_15 ),
    inference(avatar_split_clause,[],[f455,f443,f2093])).

fof(f455,plain,
    ( ! [X0] :
        ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),sK2)
        | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),X0) )
    | spl5_15 ),
    inference(superposition,[],[f444,f109])).

fof(f2063,plain,
    ( spl5_51
    | spl5_18
    | spl5_25 ),
    inference(avatar_split_clause,[],[f1817,f632,f523,f2061])).

fof(f1817,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(k1_tarski(sK0),sK2,X0),X0)
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),k1_tarski(sK0))
        | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X0)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) )
    | spl5_18
    | spl5_25 ),
    inference(forward_demodulation,[],[f1758,f1741])).

fof(f1758,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(k1_tarski(sK0),sK2,X0),k1_tarski(sK0))
        | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X0)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
        | r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X0),X0) )
    | spl5_18
    | spl5_25 ),
    inference(backward_demodulation,[],[f651,f1741])).

fof(f651,plain,
    ( ! [X0] :
        ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X0)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
        | r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X0),k1_tarski(sK0))
        | r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X0),X0) )
    | spl5_25 ),
    inference(superposition,[],[f633,f109])).

fof(f2033,plain,
    ( spl5_19
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f1919,f676,f527])).

fof(f1919,plain,
    ( r1_xboole_0(sK2,k1_tarski(sK1))
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f1886,f88])).

fof(f1886,plain,
    ( r1_xboole_0(k1_tarski(sK1),sK2)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f676])).

fof(f2031,plain,
    ( spl5_50
    | spl5_18
    | spl5_25 ),
    inference(avatar_split_clause,[],[f1818,f632,f523,f2029])).

fof(f1818,plain,
    ( ! [X1] :
        ( r2_hidden(sK3(k1_tarski(sK0),sK2,X1),X1)
        | ~ r2_hidden(sK3(k1_tarski(sK0),sK2,X1),sK2)
        | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X1)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) )
    | spl5_18
    | spl5_25 ),
    inference(forward_demodulation,[],[f1759,f1741])).

fof(f1759,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(k1_tarski(sK0),sK2,X1),sK2)
        | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X1)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
        | r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X1),X1) )
    | spl5_18
    | spl5_25 ),
    inference(backward_demodulation,[],[f652,f1741])).

fof(f652,plain,
    ( ! [X1] :
        ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X1)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
        | ~ r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X1),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))
        | r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X1),X1) )
    | spl5_25 ),
    inference(superposition,[],[f633,f108])).

fof(f2022,plain,
    ( ~ spl5_8
    | spl5_10 ),
    inference(avatar_split_clause,[],[f1286,f253,f242])).

fof(f1286,plain,
    ( ~ r1_xboole_0(sK2,k1_tarski(sK0))
    | spl5_10 ),
    inference(unit_resulting_resolution,[],[f254,f88])).

fof(f1994,plain,
    ( spl5_49
    | spl5_15
    | spl5_18 ),
    inference(avatar_split_clause,[],[f1791,f523,f443,f1992])).

fof(f1791,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(k1_tarski(sK0),sK2,X0),X0)
        | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),k1_tarski(sK0))
        | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X0)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) )
    | spl5_15
    | spl5_18 ),
    inference(forward_demodulation,[],[f1750,f1741])).

fof(f1750,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(k1_tarski(sK0),sK2,X0),k1_tarski(sK0))
        | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X0)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
        | r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X0),X0) )
    | spl5_15
    | spl5_18 ),
    inference(backward_demodulation,[],[f462,f1741])).

fof(f462,plain,
    ( ! [X0] :
        ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X0)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
        | r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X0),k1_tarski(sK0))
        | r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X0),X0) )
    | spl5_15 ),
    inference(superposition,[],[f444,f109])).

fof(f1990,plain,
    ( ~ spl5_48
    | spl5_16 ),
    inference(avatar_split_clause,[],[f1115,f482,f1988])).

fof(f1115,plain,
    ( ~ r1_tarski(k1_tarski(sK1),k1_xboole_0)
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f483,f95])).

fof(f1959,plain,
    ( spl5_47
    | spl5_15
    | spl5_18 ),
    inference(avatar_split_clause,[],[f1792,f523,f443,f1957])).

fof(f1792,plain,
    ( ! [X1] :
        ( r2_hidden(sK3(k1_tarski(sK0),sK2,X1),X1)
        | ~ r2_hidden(sK3(k1_tarski(sK0),sK2,X1),sK2)
        | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X1)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) )
    | spl5_15
    | spl5_18 ),
    inference(forward_demodulation,[],[f1751,f1741])).

fof(f1751,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(k1_tarski(sK0),sK2,X1),sK2)
        | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X1)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
        | r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X1),X1) )
    | spl5_15
    | spl5_18 ),
    inference(backward_demodulation,[],[f463,f1741])).

fof(f463,plain,
    ( ! [X1] :
        ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X1)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
        | ~ r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X1),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))
        | r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X1),X1) )
    | spl5_15 ),
    inference(superposition,[],[f444,f108])).

fof(f1918,plain,
    ( ~ spl5_46
    | spl5_9
    | ~ spl5_11
    | spl5_18 ),
    inference(avatar_split_clause,[],[f1781,f523,f257,f245,f1916])).

fof(f1781,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1))))
    | spl5_9
    | ~ spl5_11
    | spl5_18 ),
    inference(forward_demodulation,[],[f1780,f91])).

fof(f1780,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) != k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k1_xboole_0))
    | spl5_9
    | ~ spl5_11
    | spl5_18 ),
    inference(forward_demodulation,[],[f1779,f1215])).

fof(f1779,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) != k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))))
    | spl5_9
    | ~ spl5_11
    | spl5_18 ),
    inference(forward_demodulation,[],[f1778,f1143])).

fof(f1778,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) != k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))
    | spl5_9
    | spl5_18 ),
    inference(forward_demodulation,[],[f1747,f94])).

fof(f1747,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) != k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2))))
    | spl5_9
    | spl5_18 ),
    inference(backward_demodulation,[],[f246,f1741])).

fof(f1906,plain,
    ( ~ spl5_31
    | spl5_18 ),
    inference(avatar_split_clause,[],[f1739,f523,f865])).

fof(f865,plain,
    ( spl5_31
  <=> r1_tarski(k1_tarski(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f1739,plain,
    ( ~ r1_tarski(k1_tarski(sK1),sK2)
    | spl5_18 ),
    inference(unit_resulting_resolution,[],[f1325,f95])).

fof(f1887,plain,
    ( spl5_27
    | spl5_18 ),
    inference(avatar_split_clause,[],[f1727,f523,f676])).

fof(f1727,plain,
    ( r1_xboole_0(k1_tarski(sK1),sK2)
    | spl5_18 ),
    inference(unit_resulting_resolution,[],[f1325,f81])).

fof(f1658,plain,
    ( spl5_18
    | ~ spl5_31 ),
    inference(avatar_contradiction_clause,[],[f1657])).

fof(f1657,plain,
    ( $false
    | spl5_18
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f1325,f1638])).

fof(f1638,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_31 ),
    inference(resolution,[],[f866,f95])).

fof(f866,plain,
    ( r1_tarski(k1_tarski(sK1),sK2)
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f865])).

fof(f1652,plain,
    ( ~ spl5_32
    | spl5_4
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f1624,f523,f186,f988])).

fof(f1624,plain,
    ( ~ r2_hidden(sK0,k1_xboole_0)
    | spl5_4
    | ~ spl5_18 ),
    inference(backward_demodulation,[],[f212,f1600])).

fof(f1600,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_tarski(sK1),k1_tarski(sK1))
    | ~ spl5_18 ),
    inference(backward_demodulation,[],[f1522,f1498])).

fof(f1498,plain,
    ( k1_tarski(sK1) = k3_xboole_0(sK2,k1_tarski(sK1))
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f524,f80])).

fof(f1522,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_tarski(sK1),k3_xboole_0(sK2,k1_tarski(sK1)))
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f1514,f94])).

fof(f1514,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),sK2))
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f524,f118])).

fof(f212,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(k1_tarski(sK1),k1_tarski(sK1)))
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f187,f187,f82])).

fof(f1643,plain,
    ( ~ spl5_45
    | ~ spl5_18
    | spl5_37 ),
    inference(avatar_split_clause,[],[f1586,f1274,f523,f1641])).

fof(f1641,plain,
    ( spl5_45
  <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK1))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f1586,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK1))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
    | ~ spl5_18
    | spl5_37 ),
    inference(backward_demodulation,[],[f1275,f1498])).

fof(f1628,plain,
    ( ~ spl5_44
    | ~ spl5_18
    | spl5_26 ),
    inference(avatar_split_clause,[],[f1557,f663,f523,f1626])).

fof(f1626,plain,
    ( spl5_44
  <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f1557,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl5_18
    | spl5_26 ),
    inference(backward_demodulation,[],[f664,f1498])).

fof(f1495,plain,
    ( spl5_16
    | spl5_18
    | spl5_42 ),
    inference(avatar_contradiction_clause,[],[f1494])).

fof(f1494,plain,
    ( $false
    | spl5_16
    | spl5_18
    | spl5_42 ),
    inference(subsumption_resolution,[],[f1490,f1336])).

fof(f1336,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k1_xboole_0,sK2))
    | spl5_16
    | spl5_18 ),
    inference(unit_resulting_resolution,[],[f483,f1325,f82])).

fof(f1490,plain,
    ( r2_hidden(sK1,k5_xboole_0(k1_xboole_0,sK2))
    | spl5_42 ),
    inference(resolution,[],[f1481,f81])).

fof(f1481,plain,
    ( ~ r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_42 ),
    inference(avatar_component_clause,[],[f1480])).

fof(f1493,plain,
    ( spl5_16
    | spl5_18
    | spl5_42 ),
    inference(avatar_contradiction_clause,[],[f1492])).

fof(f1492,plain,
    ( $false
    | spl5_16
    | spl5_18
    | spl5_42 ),
    inference(subsumption_resolution,[],[f1486,f1336])).

fof(f1486,plain,
    ( r2_hidden(sK1,k5_xboole_0(k1_xboole_0,sK2))
    | spl5_42 ),
    inference(unit_resulting_resolution,[],[f1481,f81])).

fof(f1485,plain,
    ( ~ spl5_42
    | ~ spl5_43
    | spl5_2
    | ~ spl5_11
    | spl5_18 ),
    inference(avatar_split_clause,[],[f1440,f523,f257,f144,f1483,f1480])).

fof(f1440,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))
    | ~ r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_2
    | ~ spl5_11
    | spl5_18 ),
    inference(forward_demodulation,[],[f1439,f91])).

fof(f1439,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k1_xboole_0)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))
    | ~ r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_2
    | ~ spl5_11
    | spl5_18 ),
    inference(forward_demodulation,[],[f1438,f1215])).

fof(f1438,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))
    | ~ r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_2
    | ~ spl5_11
    | spl5_18 ),
    inference(forward_demodulation,[],[f1437,f1143])).

fof(f1437,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))
    | ~ r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_2
    | ~ spl5_11
    | spl5_18 ),
    inference(forward_demodulation,[],[f1368,f94])).

fof(f1368,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))
    | ~ r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))
    | spl5_2
    | ~ spl5_11
    | spl5_18 ),
    inference(backward_demodulation,[],[f1219,f1344])).

fof(f1344,plain,
    ( sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))
    | spl5_18 ),
    inference(unit_resulting_resolution,[],[f1325,f113])).

fof(f1329,plain,
    ( ~ spl5_18
    | ~ spl5_41
    | spl5_25 ),
    inference(avatar_split_clause,[],[f639,f632,f1327,f523])).

fof(f1327,plain,
    ( spl5_41
  <=> k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_tarski(sK1)))))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f639,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_tarski(sK1)))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
    | ~ r2_hidden(sK1,sK2)
    | spl5_25 ),
    inference(superposition,[],[f633,f80])).

fof(f1304,plain,
    ( ~ spl5_39
    | ~ spl5_40
    | spl5_15 ),
    inference(avatar_split_clause,[],[f477,f443,f1302,f1299])).

fof(f1302,plain,
    ( spl5_40
  <=> k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f477,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | ~ r1_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))
    | spl5_15 ),
    inference(forward_demodulation,[],[f459,f91])).

fof(f459,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k1_xboole_0))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | ~ r1_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))
    | spl5_15 ),
    inference(superposition,[],[f444,f86])).

fof(f1297,plain,
    ( ~ spl5_38
    | spl5_15 ),
    inference(avatar_split_clause,[],[f448,f443,f1295])).

fof(f1295,plain,
    ( spl5_38
  <=> r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f448,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))))
    | spl5_15 ),
    inference(unit_resulting_resolution,[],[f444,f126])).

fof(f1276,plain,
    ( ~ spl5_37
    | spl5_4
    | ~ spl5_11
    | spl5_25 ),
    inference(avatar_split_clause,[],[f1163,f632,f257,f186,f1274])).

fof(f1163,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
    | spl5_4
    | ~ spl5_11
    | spl5_25 ),
    inference(subsumption_resolution,[],[f1060,f1158])).

fof(f1158,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))
    | spl5_4
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f187,f326,f121])).

fof(f1060,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
    | ~ r2_hidden(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))
    | spl5_25 ),
    inference(forward_demodulation,[],[f917,f91])).

fof(f917,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k1_xboole_0)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
    | ~ r2_hidden(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))
    | spl5_25 ),
    inference(superposition,[],[f633,f118])).

fof(f1142,plain,
    ( ~ spl5_19
    | ~ spl5_36
    | spl5_15 ),
    inference(avatar_split_clause,[],[f898,f443,f1102,f527])).

fof(f1102,plain,
    ( spl5_36
  <=> k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f898,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | ~ r1_xboole_0(sK2,k1_tarski(sK1))
    | spl5_15 ),
    inference(forward_demodulation,[],[f882,f94])).

fof(f882,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | ~ r1_xboole_0(sK2,k1_tarski(sK1))
    | spl5_15 ),
    inference(superposition,[],[f444,f116])).

fof(f1104,plain,
    ( spl5_18
    | ~ spl5_36
    | spl5_15 ),
    inference(avatar_split_clause,[],[f895,f443,f1102,f523])).

fof(f895,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | r2_hidden(sK1,sK2)
    | spl5_15 ),
    inference(forward_demodulation,[],[f881,f94])).

fof(f881,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | r2_hidden(sK1,sK2)
    | spl5_15 ),
    inference(superposition,[],[f444,f113])).

fof(f1065,plain,
    ( ~ spl5_11
    | spl5_23 ),
    inference(avatar_contradiction_clause,[],[f1064])).

fof(f1064,plain,
    ( $false
    | ~ spl5_11
    | spl5_23 ),
    inference(subsumption_resolution,[],[f326,f661])).

fof(f661,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_23 ),
    inference(resolution,[],[f598,f96])).

fof(f598,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK2)
    | spl5_23 ),
    inference(avatar_component_clause,[],[f597])).

fof(f1057,plain,
    ( spl5_35
    | spl5_32 ),
    inference(avatar_split_clause,[],[f1010,f988,f1055])).

fof(f1010,plain,
    ( r1_xboole_0(k1_tarski(sK0),k1_xboole_0)
    | spl5_32 ),
    inference(unit_resulting_resolution,[],[f989,f81])).

fof(f1053,plain,
    ( ~ spl5_34
    | spl5_15 ),
    inference(avatar_split_clause,[],[f446,f443,f1051])).

fof(f1051,plain,
    ( spl5_34
  <=> r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f446,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))))))))
    | spl5_15 ),
    inference(unit_resulting_resolution,[],[f444,f126])).

fof(f1009,plain,
    ( ~ spl5_19
    | ~ spl5_33
    | spl5_25 ),
    inference(avatar_split_clause,[],[f871,f632,f1007,f527])).

fof(f1007,plain,
    ( spl5_33
  <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f871,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
    | ~ r1_xboole_0(sK2,k1_tarski(sK1))
    | spl5_25 ),
    inference(forward_demodulation,[],[f641,f91])).

fof(f641,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_xboole_0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
    | ~ r1_xboole_0(sK2,k1_tarski(sK1))
    | spl5_25 ),
    inference(superposition,[],[f633,f86])).

fof(f990,plain,
    ( ~ spl5_32
    | ~ spl5_8
    | spl5_11 ),
    inference(avatar_split_clause,[],[f956,f257,f242,f988])).

fof(f956,plain,
    ( ~ r2_hidden(sK0,k1_xboole_0)
    | ~ spl5_8
    | spl5_11 ),
    inference(backward_demodulation,[],[f574,f954])).

fof(f954,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK0))
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f932,f86])).

fof(f574,plain,
    ( ~ r2_hidden(sK0,k3_xboole_0(sK2,k1_tarski(sK0)))
    | spl5_11 ),
    inference(unit_resulting_resolution,[],[f120,f258,f85])).

fof(f933,plain,
    ( spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f608,f253,f242])).

fof(f608,plain,
    ( r1_xboole_0(sK2,k1_tarski(sK0))
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f587,f88])).

fof(f867,plain,
    ( spl5_31
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f730,f523,f865])).

fof(f730,plain,
    ( r1_tarski(k1_tarski(sK1),sK2)
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f524,f96])).

fof(f863,plain,
    ( ~ spl5_30
    | spl5_17
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f777,f523,f486,f861])).

fof(f777,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK1)))
    | spl5_17
    | ~ spl5_18 ),
    inference(backward_demodulation,[],[f487,f720])).

fof(f720,plain,
    ( k1_tarski(sK1) = k3_xboole_0(sK2,k1_tarski(sK1))
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f524,f80])).

fof(f719,plain,
    ( spl5_18
    | spl5_27 ),
    inference(avatar_split_clause,[],[f691,f676,f523])).

fof(f691,plain,
    ( r2_hidden(sK1,sK2)
    | spl5_27 ),
    inference(unit_resulting_resolution,[],[f677,f81])).

fof(f704,plain,
    ( ~ spl5_29
    | spl5_15
    | spl5_27 ),
    inference(avatar_split_clause,[],[f700,f676,f443,f702])).

fof(f702,plain,
    ( spl5_29
  <=> k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_tarski(sK1)))))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f700,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_tarski(sK1)))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | spl5_15
    | spl5_27 ),
    inference(subsumption_resolution,[],[f450,f691])).

fof(f450,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_tarski(sK1)))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | ~ r2_hidden(sK1,sK2)
    | spl5_15 ),
    inference(superposition,[],[f444,f80])).

fof(f682,plain,
    ( spl5_18
    | ~ spl5_28
    | ~ spl5_10
    | spl5_25 ),
    inference(avatar_split_clause,[],[f657,f632,f253,f680,f523])).

fof(f657,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
    | r2_hidden(sK1,sK2)
    | ~ spl5_10
    | spl5_25 ),
    inference(forward_demodulation,[],[f656,f91])).

fof(f656,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
    | r2_hidden(sK1,sK2)
    | ~ spl5_10
    | spl5_25 ),
    inference(forward_demodulation,[],[f655,f611])).

fof(f611,plain,
    ( k1_tarski(sK0) = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f610,f94])).

fof(f610,plain,
    ( k1_tarski(sK0) = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2))
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f587,f116])).

fof(f655,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
    | r2_hidden(sK1,sK2)
    | spl5_25 ),
    inference(forward_demodulation,[],[f642,f94])).

fof(f642,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
    | r2_hidden(sK1,sK2)
    | spl5_25 ),
    inference(superposition,[],[f633,f113])).

fof(f678,plain,
    ( ~ spl5_27
    | spl5_19 ),
    inference(avatar_split_clause,[],[f604,f527,f676])).

fof(f604,plain,
    ( ~ r1_xboole_0(k1_tarski(sK1),sK2)
    | spl5_19 ),
    inference(unit_resulting_resolution,[],[f528,f88])).

fof(f665,plain,
    ( spl5_18
    | ~ spl5_26
    | ~ spl5_10
    | spl5_15 ),
    inference(avatar_split_clause,[],[f629,f443,f253,f663,f523])).

fof(f629,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | r2_hidden(sK1,sK2)
    | ~ spl5_10
    | spl5_15 ),
    inference(forward_demodulation,[],[f622,f91])).

fof(f622,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | r2_hidden(sK1,sK2)
    | ~ spl5_10
    | spl5_15 ),
    inference(backward_demodulation,[],[f467,f611])).

fof(f467,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | r2_hidden(sK1,sK2)
    | spl5_15 ),
    inference(forward_demodulation,[],[f453,f94])).

fof(f453,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | r2_hidden(sK1,sK2)
    | spl5_15 ),
    inference(superposition,[],[f444,f113])).

fof(f634,plain,
    ( ~ spl5_25
    | spl5_2
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f625,f253,f144,f632])).

fof(f625,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))
    | spl5_2
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f612,f90])).

fof(f612,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(k5_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))
    | spl5_2
    | ~ spl5_10 ),
    inference(backward_demodulation,[],[f145,f611])).

fof(f603,plain,
    ( ~ spl5_19
    | ~ spl5_24
    | spl5_15 ),
    inference(avatar_split_clause,[],[f466,f443,f601,f527])).

fof(f601,plain,
    ( spl5_24
  <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f466,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | ~ r1_xboole_0(sK2,k1_tarski(sK1))
    | spl5_15 ),
    inference(forward_demodulation,[],[f452,f91])).

fof(f452,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_xboole_0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | ~ r1_xboole_0(sK2,k1_tarski(sK1))
    | spl5_15 ),
    inference(superposition,[],[f444,f86])).

fof(f599,plain,
    ( ~ spl5_23
    | spl5_11 ),
    inference(avatar_split_clause,[],[f575,f257,f597])).

fof(f575,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK2)
    | spl5_11 ),
    inference(unit_resulting_resolution,[],[f258,f95])).

fof(f595,plain,
    ( ~ spl5_21
    | ~ spl5_22
    | spl5_15 ),
    inference(avatar_split_clause,[],[f451,f443,f593,f590])).

fof(f590,plain,
    ( spl5_21
  <=> r1_tarski(sK2,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f593,plain,
    ( spl5_22
  <=> k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,sK2))))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f451,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,sK2))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | ~ r1_tarski(sK2,k1_tarski(sK1))
    | spl5_15 ),
    inference(superposition,[],[f444,f93])).

fof(f588,plain,
    ( spl5_10
    | spl5_11 ),
    inference(avatar_split_clause,[],[f565,f257,f253])).

fof(f565,plain,
    ( r1_xboole_0(k1_tarski(sK0),sK2)
    | spl5_11 ),
    inference(unit_resulting_resolution,[],[f258,f81])).

fof(f533,plain,
    ( spl5_20
    | spl5_16 ),
    inference(avatar_split_clause,[],[f498,f482,f531])).

fof(f498,plain,
    ( r1_xboole_0(k1_tarski(sK1),k1_xboole_0)
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f483,f81])).

fof(f529,plain,
    ( ~ spl5_19
    | ~ spl5_17
    | ~ spl5_11
    | spl5_15 ),
    inference(avatar_split_clause,[],[f474,f443,f257,f486,f527])).

fof(f474,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | ~ r1_xboole_0(sK2,k1_tarski(sK1))
    | ~ spl5_11
    | spl5_15 ),
    inference(forward_demodulation,[],[f473,f91])).

fof(f473,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k1_xboole_0)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | ~ r1_xboole_0(sK2,k1_tarski(sK1))
    | ~ spl5_11
    | spl5_15 ),
    inference(forward_demodulation,[],[f472,f395])).

fof(f395,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f364,f344])).

fof(f344,plain,
    ( k1_tarski(sK0) = k3_xboole_0(sK2,k1_tarski(sK0))
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f326,f80])).

fof(f364,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f358,f94])).

fof(f358,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2))
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f326,f118])).

fof(f472,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | ~ r1_xboole_0(sK2,k1_tarski(sK1))
    | ~ spl5_11
    | spl5_15 ),
    inference(forward_demodulation,[],[f471,f344])).

fof(f471,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | ~ r1_xboole_0(sK2,k1_tarski(sK1))
    | spl5_15 ),
    inference(forward_demodulation,[],[f454,f94])).

fof(f454,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | ~ r1_xboole_0(sK2,k1_tarski(sK1))
    | spl5_15 ),
    inference(superposition,[],[f444,f116])).

fof(f525,plain,
    ( spl5_18
    | ~ spl5_17
    | ~ spl5_11
    | spl5_15 ),
    inference(avatar_split_clause,[],[f470,f443,f257,f486,f523])).

fof(f470,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | r2_hidden(sK1,sK2)
    | ~ spl5_11
    | spl5_15 ),
    inference(forward_demodulation,[],[f469,f91])).

fof(f469,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k1_xboole_0)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | r2_hidden(sK1,sK2)
    | ~ spl5_11
    | spl5_15 ),
    inference(forward_demodulation,[],[f468,f395])).

fof(f468,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | r2_hidden(sK1,sK2)
    | ~ spl5_11
    | spl5_15 ),
    inference(forward_demodulation,[],[f467,f344])).

fof(f488,plain,
    ( ~ spl5_17
    | spl5_4
    | ~ spl5_11
    | spl5_15 ),
    inference(avatar_split_clause,[],[f479,f443,f257,f186,f486])).

fof(f479,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | spl5_4
    | ~ spl5_11
    | spl5_15 ),
    inference(forward_demodulation,[],[f478,f91])).

fof(f478,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k1_xboole_0)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | spl5_4
    | ~ spl5_11
    | spl5_15 ),
    inference(subsumption_resolution,[],[f460,f359])).

fof(f359,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))
    | spl5_4
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f187,f326,f121])).

fof(f484,plain,
    ( ~ spl5_16
    | spl5_3
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f403,f257,f182,f482])).

fof(f403,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | spl5_3
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f192,f395])).

fof(f445,plain,
    ( ~ spl5_15
    | spl5_2
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f377,f257,f144,f443])).

fof(f377,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))
    | spl5_2
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f376,f91])).

fof(f376,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_xboole_0))))
    | spl5_2
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f365,f90])).

fof(f365,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(k5_xboole_0(sK2,k1_xboole_0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_xboole_0)))
    | spl5_2
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f145,f364])).

fof(f343,plain,
    ( ~ spl5_14
    | spl5_2 ),
    inference(avatar_split_clause,[],[f161,f144,f341])).

fof(f161,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))))))))
    | spl5_2 ),
    inference(forward_demodulation,[],[f160,f90])).

fof(f160,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))))))
    | spl5_2 ),
    inference(forward_demodulation,[],[f149,f90])).

fof(f149,plain,
    ( ~ r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))),k1_tarski(k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))))))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f145,f126])).

fof(f327,plain,
    ( spl5_11
    | spl5_10 ),
    inference(avatar_split_clause,[],[f289,f253,f257])).

fof(f289,plain,
    ( r2_hidden(sK0,sK2)
    | spl5_10 ),
    inference(unit_resulting_resolution,[],[f254,f81])).

fof(f325,plain,
    ( ~ spl5_13
    | spl5_2 ),
    inference(avatar_split_clause,[],[f180,f144,f323])).

fof(f180,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))))))
    | spl5_2 ),
    inference(forward_demodulation,[],[f156,f90])).

fof(f156,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))))
    | spl5_2 ),
    inference(superposition,[],[f145,f90])).

fof(f288,plain,
    ( spl5_10
    | spl5_11 ),
    inference(avatar_contradiction_clause,[],[f287])).

fof(f287,plain,
    ( $false
    | spl5_10
    | spl5_11 ),
    inference(subsumption_resolution,[],[f263,f254])).

fof(f263,plain,
    ( r1_xboole_0(k1_tarski(sK0),sK2)
    | spl5_11 ),
    inference(unit_resulting_resolution,[],[f258,f81])).

fof(f282,plain,
    ( spl5_8
    | spl5_11 ),
    inference(avatar_contradiction_clause,[],[f281])).

fof(f281,plain,
    ( $false
    | spl5_8
    | spl5_11 ),
    inference(subsumption_resolution,[],[f275,f250])).

fof(f250,plain,
    ( sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK0)))
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f243,f115])).

fof(f275,plain,
    ( sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK0)))
    | spl5_11 ),
    inference(unit_resulting_resolution,[],[f258,f113])).

fof(f262,plain,
    ( ~ spl5_11
    | ~ spl5_12
    | spl5_2 ),
    inference(avatar_split_clause,[],[f167,f144,f260,f257])).

fof(f260,plain,
    ( spl5_12
  <=> k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f167,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))))))
    | ~ r2_hidden(sK0,sK2)
    | spl5_2 ),
    inference(forward_demodulation,[],[f166,f90])).

fof(f166,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))))))
    | ~ r2_hidden(sK0,sK2)
    | spl5_2 ),
    inference(forward_demodulation,[],[f151,f90])).

fof(f151,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))))
    | ~ r2_hidden(sK0,sK2)
    | spl5_2 ),
    inference(superposition,[],[f145,f80])).

fof(f255,plain,
    ( ~ spl5_10
    | spl5_8 ),
    inference(avatar_split_clause,[],[f248,f242,f253])).

fof(f248,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),sK2)
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f243,f88])).

fof(f247,plain,
    ( ~ spl5_8
    | ~ spl5_9
    | spl5_2 ),
    inference(avatar_split_clause,[],[f173,f144,f245,f242])).

fof(f173,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))))))
    | ~ r1_xboole_0(sK2,k1_tarski(sK0))
    | spl5_2 ),
    inference(forward_demodulation,[],[f172,f91])).

fof(f172,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_xboole_0))))))
    | ~ r1_xboole_0(sK2,k1_tarski(sK0))
    | spl5_2 ),
    inference(forward_demodulation,[],[f171,f90])).

fof(f171,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_xboole_0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_xboole_0)))))
    | ~ r1_xboole_0(sK2,k1_tarski(sK0))
    | spl5_2 ),
    inference(forward_demodulation,[],[f153,f90])).

fof(f153,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_xboole_0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_xboole_0))))
    | ~ r1_xboole_0(sK2,k1_tarski(sK0))
    | spl5_2 ),
    inference(superposition,[],[f145,f86])).

fof(f240,plain,
    ( spl5_7
    | spl5_3 ),
    inference(avatar_split_clause,[],[f189,f182,f238])).

fof(f238,plain,
    ( spl5_7
  <=> r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f189,plain,
    ( r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f183,f81])).

fof(f236,plain,
    ( ~ spl5_5
    | ~ spl5_6
    | spl5_2 ),
    inference(avatar_split_clause,[],[f170,f144,f234,f231])).

fof(f231,plain,
    ( spl5_5
  <=> r1_tarski(sK2,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f234,plain,
    ( spl5_6
  <=> k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(sK2,k1_tarski(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f170,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(sK2,k1_tarski(sK0)))))))
    | ~ r1_tarski(sK2,k1_tarski(sK0))
    | spl5_2 ),
    inference(forward_demodulation,[],[f169,f91])).

fof(f169,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),sK2))))))
    | ~ r1_tarski(sK2,k1_tarski(sK0))
    | spl5_2 ),
    inference(forward_demodulation,[],[f168,f90])).

fof(f168,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_tarski(sK0),sK2),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),sK2)))))
    | ~ r1_tarski(sK2,k1_tarski(sK0))
    | spl5_2 ),
    inference(forward_demodulation,[],[f152,f90])).

fof(f152,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),sK2)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),sK2))))
    | ~ r1_tarski(sK2,k1_tarski(sK0))
    | spl5_2 ),
    inference(superposition,[],[f145,f93])).

fof(f188,plain,
    ( ~ spl5_4
    | spl5_1 ),
    inference(avatar_split_clause,[],[f140,f135,f186])).

fof(f135,plain,
    ( spl5_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f140,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK1))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f136,f126])).

fof(f136,plain,
    ( sK0 != sK1
    | spl5_1 ),
    inference(avatar_component_clause,[],[f135])).

fof(f184,plain,
    ( ~ spl5_3
    | spl5_1 ),
    inference(avatar_split_clause,[],[f138,f135,f182])).

fof(f138,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK0))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f136,f126])).

fof(f146,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f133,f144])).

fof(f133,plain,(
    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))) ),
    inference(forward_demodulation,[],[f132,f90])).

fof(f132,plain,(
    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(sK2,k1_tarski(sK0))),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(sK2,k1_tarski(sK0))))) ),
    inference(forward_demodulation,[],[f131,f94])).

fof(f131,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(sK2,k1_tarski(sK0))),k3_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(sK2,k1_tarski(sK0))),k1_tarski(sK1))) != k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) ),
    inference(forward_demodulation,[],[f130,f94])).

fof(f130,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(sK2,k1_tarski(sK0))),k3_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(sK2,k1_tarski(sK0))),k1_tarski(sK1))) != k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),k1_tarski(sK0))))) ),
    inference(forward_demodulation,[],[f129,f90])).

fof(f129,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(sK2,k1_tarski(sK0))),k3_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(sK2,k1_tarski(sK0))),k1_tarski(sK1))) != k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),k1_tarski(sK0)))) ),
    inference(forward_demodulation,[],[f103,f90])).

fof(f103,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(sK2,k1_tarski(sK0))),k3_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(sK2,k1_tarski(sK0))),k1_tarski(sK1))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),k1_tarski(sK0)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(definition_unfolding,[],[f59,f73,f75,f75,f73])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f59,plain,(
    k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))
    & sK0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0))
        & X0 != X1 )
   => ( k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))
      & sK0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( X0 != X1
       => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f29,conjecture,(
    ! [X0,X1,X2] :
      ( X0 != X1
     => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_zfmisc_1)).

fof(f137,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f58,f135])).

fof(f58,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:47:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (18574)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.51  % (18589)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.51  % (18571)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (18582)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (18582)Refutation not found, incomplete strategy% (18582)------------------------------
% 0.21/0.52  % (18582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (18566)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (18564)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (18579)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (18582)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (18582)Memory used [KB]: 1663
% 0.21/0.52  % (18582)Time elapsed: 0.106 s
% 0.21/0.52  % (18582)------------------------------
% 0.21/0.52  % (18582)------------------------------
% 0.21/0.53  % (18585)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (18575)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (18578)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (18565)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (18578)Refutation not found, incomplete strategy% (18578)------------------------------
% 0.21/0.54  % (18578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18578)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (18578)Memory used [KB]: 1663
% 0.21/0.54  % (18578)Time elapsed: 0.127 s
% 0.21/0.54  % (18578)------------------------------
% 0.21/0.54  % (18578)------------------------------
% 0.21/0.54  % (18565)Refutation not found, incomplete strategy% (18565)------------------------------
% 0.21/0.54  % (18565)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18565)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (18565)Memory used [KB]: 1791
% 0.21/0.54  % (18565)Time elapsed: 0.132 s
% 0.21/0.54  % (18565)------------------------------
% 0.21/0.54  % (18565)------------------------------
% 0.21/0.54  % (18593)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (18590)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (18583)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (18590)Refutation not found, incomplete strategy% (18590)------------------------------
% 0.21/0.54  % (18590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18590)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (18590)Memory used [KB]: 6268
% 0.21/0.54  % (18590)Time elapsed: 0.122 s
% 0.21/0.54  % (18590)------------------------------
% 0.21/0.54  % (18590)------------------------------
% 0.21/0.55  % (18573)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (18592)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (18567)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.55  % (18570)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (18572)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (18584)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.56  % (18577)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (18568)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.56  % (18587)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.63/0.57  % (18569)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.63/0.57  % (18591)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.63/0.57  % (18591)Refutation not found, incomplete strategy% (18591)------------------------------
% 1.63/0.57  % (18591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.57  % (18591)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.57  
% 1.63/0.57  % (18591)Memory used [KB]: 6268
% 1.63/0.57  % (18591)Time elapsed: 0.166 s
% 1.63/0.57  % (18591)------------------------------
% 1.63/0.57  % (18591)------------------------------
% 1.63/0.57  % (18580)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.63/0.57  % (18580)Refutation not found, incomplete strategy% (18580)------------------------------
% 1.63/0.57  % (18580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.57  % (18580)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.57  
% 1.63/0.57  % (18580)Memory used [KB]: 10618
% 1.63/0.57  % (18580)Time elapsed: 0.169 s
% 1.63/0.57  % (18580)------------------------------
% 1.63/0.57  % (18580)------------------------------
% 1.63/0.57  % (18586)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.63/0.57  % (18576)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.63/0.58  % (18581)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.63/0.58  % (18581)Refutation not found, incomplete strategy% (18581)------------------------------
% 1.63/0.58  % (18581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % (18581)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.58  
% 1.63/0.58  % (18581)Memory used [KB]: 1791
% 1.63/0.58  % (18581)Time elapsed: 0.180 s
% 1.63/0.58  % (18581)------------------------------
% 1.63/0.58  % (18581)------------------------------
% 1.71/0.59  % (18588)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.71/0.59  % (18588)Refutation not found, incomplete strategy% (18588)------------------------------
% 1.71/0.59  % (18588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.59  % (18588)Termination reason: Refutation not found, incomplete strategy
% 1.71/0.59  
% 1.71/0.59  % (18588)Memory used [KB]: 10746
% 1.71/0.59  % (18588)Time elapsed: 0.188 s
% 1.71/0.59  % (18588)------------------------------
% 1.71/0.59  % (18588)------------------------------
% 2.18/0.66  % (18596)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.18/0.68  % (18595)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.18/0.71  % (18567)Refutation not found, incomplete strategy% (18567)------------------------------
% 2.18/0.71  % (18567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.71  % (18567)Termination reason: Refutation not found, incomplete strategy
% 2.18/0.71  
% 2.18/0.71  % (18567)Memory used [KB]: 6140
% 2.18/0.71  % (18567)Time elapsed: 0.298 s
% 2.18/0.71  % (18567)------------------------------
% 2.18/0.71  % (18567)------------------------------
% 2.18/0.71  % (18597)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.67/0.71  % (18598)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.67/0.72  % (18594)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.67/0.73  % (18598)Refutation not found, incomplete strategy% (18598)------------------------------
% 2.67/0.73  % (18598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.67/0.73  % (18598)Termination reason: Refutation not found, incomplete strategy
% 2.67/0.73  
% 2.67/0.73  % (18598)Memory used [KB]: 10746
% 2.67/0.73  % (18598)Time elapsed: 0.137 s
% 2.67/0.73  % (18598)------------------------------
% 2.67/0.73  % (18598)------------------------------
% 2.67/0.75  % (18599)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.67/0.75  % (18600)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 3.08/0.77  % (18601)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 3.08/0.85  % (18566)Time limit reached!
% 3.08/0.85  % (18566)------------------------------
% 3.08/0.85  % (18566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.65/0.86  % (18602)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 3.65/0.87  % (18566)Termination reason: Time limit
% 3.65/0.87  % (18566)Termination phase: Saturation
% 3.65/0.87  
% 3.65/0.87  % (18566)Memory used [KB]: 6652
% 3.65/0.87  % (18566)Time elapsed: 0.400 s
% 3.65/0.87  % (18566)------------------------------
% 3.65/0.87  % (18566)------------------------------
% 3.86/0.89  % (18603)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 3.86/0.89  % (18603)Refutation not found, incomplete strategy% (18603)------------------------------
% 3.86/0.89  % (18603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.86/0.89  % (18603)Termination reason: Refutation not found, incomplete strategy
% 3.86/0.89  
% 3.86/0.89  % (18603)Memory used [KB]: 10746
% 3.86/0.89  % (18603)Time elapsed: 0.133 s
% 3.86/0.89  % (18603)------------------------------
% 3.86/0.89  % (18603)------------------------------
% 4.16/0.93  % (18593)Time limit reached!
% 4.16/0.93  % (18593)------------------------------
% 4.16/0.93  % (18593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.16/0.94  % (18593)Termination reason: Time limit
% 4.16/0.94  
% 4.16/0.94  % (18593)Memory used [KB]: 4605
% 4.16/0.94  % (18593)Time elapsed: 0.520 s
% 4.16/0.94  % (18593)------------------------------
% 4.16/0.94  % (18593)------------------------------
% 4.26/0.95  % (18570)Time limit reached!
% 4.26/0.95  % (18570)------------------------------
% 4.26/0.95  % (18570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.26/0.95  % (18570)Termination reason: Time limit
% 4.26/0.95  
% 4.26/0.95  % (18570)Memory used [KB]: 14328
% 4.26/0.95  % (18570)Time elapsed: 0.530 s
% 4.26/0.95  % (18570)------------------------------
% 4.26/0.95  % (18570)------------------------------
% 4.26/1.00  % (18604)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 4.26/1.01  % (18571)Time limit reached!
% 4.26/1.01  % (18571)------------------------------
% 4.26/1.01  % (18571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.26/1.01  % (18571)Termination reason: Time limit
% 4.26/1.01  % (18571)Termination phase: Saturation
% 4.26/1.01  
% 4.26/1.01  % (18571)Memory used [KB]: 5884
% 4.26/1.01  % (18571)Time elapsed: 0.600 s
% 4.26/1.01  % (18571)------------------------------
% 4.26/1.01  % (18571)------------------------------
% 4.72/1.03  % (18605)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 5.60/1.08  % (18606)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 5.60/1.11  % (18607)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 5.60/1.11  % (18607)Refutation not found, incomplete strategy% (18607)------------------------------
% 5.60/1.11  % (18607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.60/1.11  % (18607)Termination reason: Refutation not found, incomplete strategy
% 5.60/1.11  
% 5.60/1.11  % (18607)Memory used [KB]: 10746
% 5.60/1.11  % (18607)Time elapsed: 0.149 s
% 5.60/1.11  % (18607)------------------------------
% 5.60/1.11  % (18607)------------------------------
% 5.60/1.15  % (18608)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 6.50/1.21  % (18600)Time limit reached!
% 6.50/1.21  % (18600)------------------------------
% 6.50/1.21  % (18600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.50/1.21  % (18600)Termination reason: Time limit
% 6.50/1.21  
% 6.50/1.21  % (18600)Memory used [KB]: 14328
% 6.50/1.21  % (18600)Time elapsed: 0.606 s
% 6.50/1.21  % (18600)------------------------------
% 6.50/1.21  % (18600)------------------------------
% 6.50/1.21  % (18609)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 7.33/1.34  % (18610)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 7.81/1.43  % (18576)Time limit reached!
% 7.81/1.43  % (18576)------------------------------
% 7.81/1.43  % (18576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.81/1.43  % (18576)Termination reason: Time limit
% 7.81/1.43  
% 7.81/1.43  % (18576)Memory used [KB]: 13048
% 7.81/1.43  % (18576)Time elapsed: 1.021 s
% 7.81/1.43  % (18576)------------------------------
% 7.81/1.43  % (18576)------------------------------
% 8.52/1.47  % (18596)Time limit reached!
% 8.52/1.47  % (18596)------------------------------
% 8.52/1.47  % (18596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.52/1.47  % (18596)Termination reason: Time limit
% 8.52/1.47  
% 8.52/1.47  % (18596)Memory used [KB]: 12409
% 8.52/1.47  % (18596)Time elapsed: 0.896 s
% 8.52/1.47  % (18596)------------------------------
% 8.52/1.47  % (18596)------------------------------
% 8.75/1.52  % (18609)Time limit reached!
% 8.75/1.52  % (18609)------------------------------
% 8.75/1.52  % (18609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.75/1.52  % (18609)Termination reason: Time limit
% 8.75/1.52  % (18609)Termination phase: Saturation
% 8.75/1.52  
% 8.75/1.52  % (18609)Memory used [KB]: 7675
% 8.75/1.52  % (18609)Time elapsed: 0.400 s
% 8.75/1.52  % (18609)------------------------------
% 8.75/1.52  % (18609)------------------------------
% 9.16/1.60  % (18611)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 9.87/1.63  % (18612)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 9.87/1.64  % (18564)Time limit reached!
% 9.87/1.64  % (18564)------------------------------
% 9.87/1.64  % (18564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.87/1.64  % (18564)Termination reason: Time limit
% 9.87/1.64  % (18564)Termination phase: Saturation
% 9.87/1.64  
% 9.87/1.64  % (18564)Memory used [KB]: 7419
% 9.87/1.64  % (18564)Time elapsed: 1.200 s
% 9.87/1.64  % (18564)------------------------------
% 9.87/1.64  % (18564)------------------------------
% 10.37/1.68  % (18613)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 10.37/1.73  % (18569)Time limit reached!
% 10.37/1.73  % (18569)------------------------------
% 10.37/1.73  % (18569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.37/1.73  % (18569)Termination reason: Time limit
% 10.37/1.73  
% 10.37/1.73  % (18569)Memory used [KB]: 12153
% 10.37/1.73  % (18569)Time elapsed: 1.305 s
% 10.37/1.73  % (18569)------------------------------
% 10.37/1.73  % (18569)------------------------------
% 10.37/1.75  % (18610)Time limit reached!
% 10.37/1.75  % (18610)------------------------------
% 10.37/1.75  % (18610)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.37/1.75  % (18610)Termination reason: Time limit
% 10.37/1.75  
% 10.37/1.75  % (18610)Memory used [KB]: 11769
% 10.37/1.75  % (18610)Time elapsed: 0.505 s
% 10.37/1.75  % (18610)------------------------------
% 10.37/1.75  % (18610)------------------------------
% 10.37/1.77  % (18614)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 11.47/1.89  % (18611)Time limit reached!
% 11.47/1.89  % (18611)------------------------------
% 11.47/1.89  % (18611)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.47/1.89  % (18611)Termination reason: Time limit
% 11.47/1.89  
% 11.47/1.89  % (18611)Memory used [KB]: 8315
% 11.47/1.89  % (18611)Time elapsed: 0.428 s
% 11.47/1.89  % (18611)------------------------------
% 11.47/1.89  % (18611)------------------------------
% 12.75/1.99  % (18613)Time limit reached!
% 12.75/1.99  % (18613)------------------------------
% 12.75/1.99  % (18613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.75/1.99  % (18613)Termination reason: Time limit
% 12.75/1.99  
% 12.75/1.99  % (18613)Memory used [KB]: 3070
% 12.75/1.99  % (18613)Time elapsed: 0.411 s
% 12.75/1.99  % (18613)------------------------------
% 12.75/1.99  % (18613)------------------------------
% 13.49/2.09  % (18614)Time limit reached!
% 13.49/2.09  % (18614)------------------------------
% 13.49/2.09  % (18614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.49/2.09  % (18614)Termination reason: Time limit
% 13.49/2.09  % (18614)Termination phase: Saturation
% 13.49/2.09  
% 13.49/2.09  % (18614)Memory used [KB]: 7803
% 13.49/2.09  % (18614)Time elapsed: 0.400 s
% 13.49/2.09  % (18614)------------------------------
% 13.49/2.09  % (18614)------------------------------
% 14.02/2.20  % (18602)Refutation found. Thanks to Tanya!
% 14.02/2.20  % SZS status Theorem for theBenchmark
% 14.02/2.20  % SZS output start Proof for theBenchmark
% 14.02/2.20  fof(f7656,plain,(
% 14.02/2.20    $false),
% 14.02/2.20    inference(avatar_sat_refutation,[],[f137,f146,f184,f188,f236,f240,f247,f255,f262,f282,f288,f325,f327,f343,f445,f484,f488,f525,f529,f533,f588,f595,f599,f603,f634,f665,f678,f682,f704,f719,f863,f867,f933,f990,f1009,f1053,f1057,f1065,f1104,f1142,f1276,f1297,f1304,f1329,f1485,f1493,f1495,f1628,f1643,f1652,f1658,f1887,f1906,f1918,f1959,f1990,f1994,f2022,f2031,f2033,f2063,f2095,f2288,f2295,f2299,f2310,f2314,f2329,f2347,f2360,f2364,f2384,f2388,f2408,f2412,f2438,f2460,f2464,f2484,f2510,f2527,f2531,f2630,f2634,f2779,f2782,f2790,f2992,f3031,f3085,f3152,f3196,f3198,f3201,f3206,f3391,f3443,f3447,f3480,f3532,f3552,f3572,f3597,f3618,f3641,f3662,f3666,f3685,f3709,f3713,f3732,f3741,f3743,f4124,f4142,f4146,f4205,f4381,f4383,f4414,f4453,f4495,f4506,f4512,f4527,f4543,f4557,f4561,f4611,f4645,f4649,f4684,f4688,f4705,f4709,f4726,f5000,f5061,f5065,f5069,f5073,f5077,f5093,f5109,f5113,f5117,f5121,f5125,f5129,f5133,f5137,f5192,f5284,f5289,f5453,f5475,f5507,f5508,f5537,f5598,f5712,f5731,f5735,f5806,f5810,f5986,f6050,f6051,f6103,f6107,f6120,f6212,f6216,f6218,f6233,f6262,f6266,f6273,f6276,f6561,f6565,f6688,f6717,f6751,f6800,f6952,f6973,f7046,f7090,f7173,f7204,f7285,f7294,f7336,f7655])).
% 14.02/2.20  fof(f7655,plain,(
% 14.02/2.20    ~spl5_90 | spl5_16 | spl5_18),
% 14.02/2.20    inference(avatar_split_clause,[],[f6294,f523,f482,f4140])).
% 14.02/2.20  fof(f4140,plain,(
% 14.02/2.20    spl5_90 <=> r2_hidden(sK1,k5_xboole_0(k1_xboole_0,sK2))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).
% 14.02/2.20  fof(f482,plain,(
% 14.02/2.20    spl5_16 <=> r2_hidden(sK1,k1_xboole_0)),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 14.02/2.20  fof(f523,plain,(
% 14.02/2.20    spl5_18 <=> r2_hidden(sK1,sK2)),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 14.02/2.20  fof(f6294,plain,(
% 14.02/2.20    ~r2_hidden(sK1,k5_xboole_0(k1_xboole_0,sK2)) | (spl5_16 | spl5_18)),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f483,f1325,f82])).
% 14.02/2.20  fof(f82,plain,(
% 14.02/2.20    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 14.02/2.20    inference(cnf_transformation,[],[f52])).
% 14.02/2.20  fof(f52,plain,(
% 14.02/2.20    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 14.02/2.20    inference(nnf_transformation,[],[f34])).
% 14.02/2.20  fof(f34,plain,(
% 14.02/2.20    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 14.02/2.20    inference(ennf_transformation,[],[f6])).
% 14.02/2.20  fof(f6,axiom,(
% 14.02/2.20    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 14.02/2.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 14.02/2.20  fof(f1325,plain,(
% 14.02/2.20    ~r2_hidden(sK1,sK2) | spl5_18),
% 14.02/2.20    inference(avatar_component_clause,[],[f523])).
% 14.02/2.20  fof(f483,plain,(
% 14.02/2.20    ~r2_hidden(sK1,k1_xboole_0) | spl5_16),
% 14.02/2.20    inference(avatar_component_clause,[],[f482])).
% 14.02/2.20  fof(f7336,plain,(
% 14.02/2.20    ~spl5_149 | spl5_115),
% 14.02/2.20    inference(avatar_split_clause,[],[f5099,f5091,f7334])).
% 14.02/2.20  fof(f7334,plain,(
% 14.02/2.20    spl5_149 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(sK1))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_149])])).
% 14.02/2.20  fof(f5091,plain,(
% 14.02/2.20    spl5_115 <=> k1_xboole_0 = k5_xboole_0(k1_tarski(sK1),k1_xboole_0)),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_115])])).
% 14.02/2.20  fof(f5099,plain,(
% 14.02/2.20    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_tarski(sK1)) | spl5_115),
% 14.02/2.20    inference(superposition,[],[f5092,f91])).
% 14.02/2.20  fof(f91,plain,(
% 14.02/2.20    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 14.02/2.20    inference(cnf_transformation,[],[f2])).
% 14.02/2.20  fof(f2,axiom,(
% 14.02/2.20    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 14.02/2.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 14.02/2.20  fof(f5092,plain,(
% 14.02/2.20    k1_xboole_0 != k5_xboole_0(k1_tarski(sK1),k1_xboole_0) | spl5_115),
% 14.02/2.20    inference(avatar_component_clause,[],[f5091])).
% 14.02/2.20  fof(f7294,plain,(
% 14.02/2.20    ~spl5_148 | spl5_114),
% 14.02/2.20    inference(avatar_split_clause,[],[f5083,f5075,f7292])).
% 14.02/2.20  fof(f7292,plain,(
% 14.02/2.20    spl5_148 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(sK0))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_148])])).
% 14.02/2.20  fof(f5075,plain,(
% 14.02/2.20    spl5_114 <=> k1_xboole_0 = k5_xboole_0(k1_tarski(sK0),k1_xboole_0)),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).
% 14.02/2.20  fof(f5083,plain,(
% 14.02/2.20    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_tarski(sK0)) | spl5_114),
% 14.02/2.20    inference(superposition,[],[f5076,f91])).
% 14.02/2.20  fof(f5076,plain,(
% 14.02/2.20    k1_xboole_0 != k5_xboole_0(k1_tarski(sK0),k1_xboole_0) | spl5_114),
% 14.02/2.20    inference(avatar_component_clause,[],[f5075])).
% 14.02/2.20  fof(f7285,plain,(
% 14.02/2.20    ~spl5_71 | ~spl5_147 | spl5_2 | ~spl5_11 | spl5_18 | ~spl5_19),
% 14.02/2.20    inference(avatar_split_clause,[],[f6932,f527,f523,f257,f144,f7283,f2628])).
% 14.02/2.20  fof(f2628,plain,(
% 14.02/2.20    spl5_71 <=> r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).
% 14.02/2.20  fof(f7283,plain,(
% 14.02/2.20    spl5_147 <=> k5_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_147])])).
% 14.02/2.20  fof(f144,plain,(
% 14.02/2.20    spl5_2 <=> k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) = k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 14.02/2.20  fof(f257,plain,(
% 14.02/2.20    spl5_11 <=> r2_hidden(sK0,sK2)),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 14.02/2.20  fof(f527,plain,(
% 14.02/2.20    spl5_19 <=> r1_xboole_0(sK2,k1_tarski(sK1))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 14.02/2.20  fof(f6932,plain,(
% 14.02/2.20    k5_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) | ~r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | (spl5_2 | ~spl5_11 | spl5_18 | ~spl5_19)),
% 14.02/2.20    inference(forward_demodulation,[],[f6931,f91])).
% 14.02/2.20  fof(f6931,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k1_xboole_0) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) | ~r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | (spl5_2 | ~spl5_11 | spl5_18 | ~spl5_19)),
% 14.02/2.20    inference(forward_demodulation,[],[f6861,f102])).
% 14.02/2.20  fof(f102,plain,(
% 14.02/2.20    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 14.02/2.20    inference(cnf_transformation,[],[f13])).
% 14.02/2.20  fof(f13,axiom,(
% 14.02/2.20    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 14.02/2.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 14.02/2.20  fof(f6861,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0)) | ~r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | (spl5_2 | ~spl5_11 | spl5_18 | ~spl5_19)),
% 14.02/2.20    inference(backward_demodulation,[],[f6675,f6802])).
% 14.02/2.20  fof(f6802,plain,(
% 14.02/2.20    k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK1)) | ~spl5_19),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f2032,f86])).
% 14.02/2.20  fof(f86,plain,(
% 14.02/2.20    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 14.02/2.20    inference(cnf_transformation,[],[f53])).
% 14.02/2.20  fof(f53,plain,(
% 14.02/2.20    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 14.02/2.20    inference(nnf_transformation,[],[f4])).
% 14.02/2.20  fof(f4,axiom,(
% 14.02/2.20    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 14.02/2.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 14.02/2.20  fof(f2032,plain,(
% 14.02/2.20    r1_xboole_0(sK2,k1_tarski(sK1)) | ~spl5_19),
% 14.02/2.20    inference(avatar_component_clause,[],[f527])).
% 14.02/2.20  fof(f6675,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) | ~r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | (spl5_2 | ~spl5_11 | spl5_18)),
% 14.02/2.20    inference(forward_demodulation,[],[f6575,f91])).
% 14.02/2.20  fof(f6575,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))) | ~r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | (spl5_2 | ~spl5_11 | spl5_18)),
% 14.02/2.20    inference(backward_demodulation,[],[f6536,f6426])).
% 14.02/2.20  fof(f6426,plain,(
% 14.02/2.20    k1_tarski(sK0) = k3_xboole_0(sK2,k1_tarski(sK0)) | ~spl5_11),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f326,f80])).
% 14.02/2.20  fof(f80,plain,(
% 14.02/2.20    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 14.02/2.20    inference(cnf_transformation,[],[f32])).
% 14.02/2.20  fof(f32,plain,(
% 14.02/2.20    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 14.02/2.20    inference(ennf_transformation,[],[f24])).
% 14.02/2.20  fof(f24,axiom,(
% 14.02/2.20    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 14.02/2.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 14.02/2.20  fof(f326,plain,(
% 14.02/2.20    r2_hidden(sK0,sK2) | ~spl5_11),
% 14.02/2.20    inference(avatar_component_clause,[],[f257])).
% 14.02/2.20  fof(f6536,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) | ~r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | (spl5_2 | ~spl5_11 | spl5_18)),
% 14.02/2.20    inference(forward_demodulation,[],[f6535,f91])).
% 14.02/2.20  fof(f6535,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k1_xboole_0)) | ~r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | (spl5_2 | ~spl5_11 | spl5_18)),
% 14.02/2.20    inference(forward_demodulation,[],[f6534,f6457])).
% 14.02/2.20  fof(f6457,plain,(
% 14.02/2.20    k1_xboole_0 = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))) | ~spl5_11),
% 14.02/2.20    inference(forward_demodulation,[],[f6448,f94])).
% 14.02/2.20  fof(f94,plain,(
% 14.02/2.20    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 14.02/2.20    inference(cnf_transformation,[],[f1])).
% 14.02/2.20  fof(f1,axiom,(
% 14.02/2.20    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 14.02/2.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 14.02/2.20  fof(f6448,plain,(
% 14.02/2.20    k1_xboole_0 = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2)) | ~spl5_11),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f326,f118])).
% 14.02/2.20  fof(f118,plain,(
% 14.02/2.20    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(k1_tarski(X0),k3_xboole_0(k1_tarski(X0),X1)) | ~r2_hidden(X0,X1)) )),
% 14.02/2.20    inference(definition_unfolding,[],[f101,f73])).
% 14.02/2.20  fof(f73,plain,(
% 14.02/2.20    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 14.02/2.20    inference(cnf_transformation,[],[f9])).
% 14.02/2.20  fof(f9,axiom,(
% 14.02/2.20    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 14.02/2.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 14.02/2.20  fof(f101,plain,(
% 14.02/2.20    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 14.02/2.20    inference(cnf_transformation,[],[f57])).
% 14.02/2.20  fof(f57,plain,(
% 14.02/2.20    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)))),
% 14.02/2.20    inference(nnf_transformation,[],[f25])).
% 14.02/2.20  fof(f25,axiom,(
% 14.02/2.20    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 14.02/2.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).
% 14.02/2.20  fof(f6534,plain,(
% 14.02/2.20    ~r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) | (spl5_2 | ~spl5_11 | spl5_18)),
% 14.02/2.20    inference(forward_demodulation,[],[f6482,f91])).
% 14.02/2.20  fof(f6482,plain,(
% 14.02/2.20    ~r1_tarski(k1_tarski(sK1),k5_xboole_0(sK2,k1_xboole_0)) | k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) | (spl5_2 | ~spl5_11 | spl5_18)),
% 14.02/2.20    inference(backward_demodulation,[],[f6364,f6457])).
% 14.02/2.20  fof(f6364,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) | ~r1_tarski(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) | (spl5_2 | spl5_18)),
% 14.02/2.20    inference(forward_demodulation,[],[f6320,f94])).
% 14.02/2.20  fof(f6320,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2)))) | ~r1_tarski(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) | (spl5_2 | spl5_18)),
% 14.02/2.20    inference(backward_demodulation,[],[f176,f6307])).
% 14.02/2.20  fof(f6307,plain,(
% 14.02/2.20    sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))) | spl5_18),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f1325,f113])).
% 14.02/2.20  fof(f113,plain,(
% 14.02/2.20    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_tarski(X1))) = X0 | r2_hidden(X1,X0)) )),
% 14.02/2.20    inference(definition_unfolding,[],[f70,f73])).
% 14.02/2.20  fof(f70,plain,(
% 14.02/2.20    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 14.02/2.20    inference(cnf_transformation,[],[f46])).
% 14.02/2.20  fof(f46,plain,(
% 14.02/2.20    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 14.02/2.20    inference(nnf_transformation,[],[f28])).
% 14.02/2.20  fof(f28,axiom,(
% 14.02/2.20    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 14.02/2.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 14.02/2.20  fof(f176,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(sK2,k1_tarski(sK0))))) | ~r1_tarski(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) | spl5_2),
% 14.02/2.20    inference(forward_demodulation,[],[f175,f91])).
% 14.02/2.20  fof(f175,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)))) | ~r1_tarski(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) | spl5_2),
% 14.02/2.20    inference(forward_demodulation,[],[f174,f90])).
% 14.02/2.20  fof(f90,plain,(
% 14.02/2.20    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 14.02/2.20    inference(cnf_transformation,[],[f15])).
% 14.02/2.20  fof(f15,axiom,(
% 14.02/2.20    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 14.02/2.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 14.02/2.20  fof(f174,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))),k1_tarski(sK1))) | ~r1_tarski(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) | spl5_2),
% 14.02/2.20    inference(forward_demodulation,[],[f154,f90])).
% 14.02/2.20  fof(f154,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))),k1_tarski(sK1)) | ~r1_tarski(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) | spl5_2),
% 14.02/2.20    inference(superposition,[],[f145,f93])).
% 14.02/2.20  fof(f93,plain,(
% 14.02/2.20    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 14.02/2.20    inference(cnf_transformation,[],[f36])).
% 14.02/2.20  fof(f36,plain,(
% 14.02/2.20    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 14.02/2.20    inference(ennf_transformation,[],[f11])).
% 14.02/2.20  fof(f11,axiom,(
% 14.02/2.20    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 14.02/2.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 14.02/2.20  fof(f145,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))) | spl5_2),
% 14.02/2.20    inference(avatar_component_clause,[],[f144])).
% 14.02/2.20  fof(f7204,plain,(
% 14.02/2.20    ~spl5_71 | ~spl5_146 | ~spl5_19 | spl5_138),
% 14.02/2.20    inference(avatar_split_clause,[],[f6944,f6686,f527,f7202,f2628])).
% 14.02/2.20  fof(f7202,plain,(
% 14.02/2.20    spl5_146 <=> k5_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_tarski(sK1)))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_146])])).
% 14.02/2.20  fof(f6686,plain,(
% 14.02/2.20    spl5_138 <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_138])])).
% 14.02/2.20  fof(f6944,plain,(
% 14.02/2.20    k5_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_tarski(sK1))) | ~r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | (~spl5_19 | spl5_138)),
% 14.02/2.20    inference(forward_demodulation,[],[f6943,f91])).
% 14.02/2.20  fof(f6943,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k1_xboole_0) != k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_tarski(sK1))) | ~r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | (~spl5_19 | spl5_138)),
% 14.02/2.20    inference(forward_demodulation,[],[f6867,f102])).
% 14.02/2.20  fof(f6867,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_tarski(sK1))) | ~r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | (~spl5_19 | spl5_138)),
% 14.02/2.20    inference(backward_demodulation,[],[f6701,f6802])).
% 14.02/2.20  fof(f6701,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k1_tarski(sK1))) | ~r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | spl5_138),
% 14.02/2.20    inference(forward_demodulation,[],[f6693,f90])).
% 14.02/2.20  fof(f6693,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k1_tarski(sK1)) | ~r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | spl5_138),
% 14.02/2.20    inference(superposition,[],[f6687,f93])).
% 14.02/2.20  fof(f6687,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))) | spl5_138),
% 14.02/2.20    inference(avatar_component_clause,[],[f6686])).
% 14.02/2.20  fof(f7173,plain,(
% 14.02/2.20    spl5_123 | spl5_135),
% 14.02/2.20    inference(avatar_contradiction_clause,[],[f7172])).
% 14.02/2.20  fof(f7172,plain,(
% 14.02/2.20    $false | (spl5_123 | spl5_135)),
% 14.02/2.20    inference(subsumption_resolution,[],[f7116,f6260])).
% 14.02/2.20  fof(f6260,plain,(
% 14.02/2.20    ~r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))) | spl5_135),
% 14.02/2.20    inference(trivial_inequality_removal,[],[f6259])).
% 14.02/2.20  fof(f6259,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) | ~r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))) | spl5_135),
% 14.02/2.20    inference(forward_demodulation,[],[f6258,f91])).
% 14.02/2.20  fof(f6258,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_xboole_0)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) | ~r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))) | spl5_135),
% 14.02/2.20    inference(forward_demodulation,[],[f6113,f102])).
% 14.02/2.20  fof(f6113,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_xboole_0))) | ~r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))) | spl5_135),
% 14.02/2.20    inference(superposition,[],[f6106,f86])).
% 14.02/2.20  fof(f6106,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))) | spl5_135),
% 14.02/2.20    inference(avatar_component_clause,[],[f6105])).
% 14.02/2.20  fof(f6105,plain,(
% 14.02/2.20    spl5_135 <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_135])])).
% 14.02/2.20  fof(f7116,plain,(
% 14.02/2.20    r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))) | spl5_123),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f5136,f81])).
% 14.02/2.20  fof(f81,plain,(
% 14.02/2.20    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 14.02/2.20    inference(cnf_transformation,[],[f33])).
% 14.02/2.20  fof(f33,plain,(
% 14.02/2.20    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 14.02/2.20    inference(ennf_transformation,[],[f23])).
% 14.02/2.20  fof(f23,axiom,(
% 14.02/2.20    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 14.02/2.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 14.02/2.20  fof(f5136,plain,(
% 14.02/2.20    ~r2_hidden(sK1,k5_xboole_0(sK2,k1_tarski(sK0))) | spl5_123),
% 14.02/2.20    inference(avatar_component_clause,[],[f5135])).
% 14.02/2.20  fof(f5135,plain,(
% 14.02/2.20    spl5_123 <=> r2_hidden(sK1,k5_xboole_0(sK2,k1_tarski(sK0)))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_123])])).
% 14.02/2.20  fof(f7090,plain,(
% 14.02/2.20    ~spl5_145 | ~spl5_19 | spl5_138),
% 14.02/2.20    inference(avatar_split_clause,[],[f6942,f6686,f527,f7088])).
% 14.02/2.20  fof(f7088,plain,(
% 14.02/2.20    spl5_145 <=> r2_hidden(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),k1_tarski(k5_xboole_0(k1_xboole_0,sK2)))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_145])])).
% 14.02/2.20  fof(f6942,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),k1_tarski(k5_xboole_0(k1_xboole_0,sK2))) | (~spl5_19 | spl5_138)),
% 14.02/2.20    inference(forward_demodulation,[],[f6941,f91])).
% 14.02/2.20  fof(f6941,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),k1_tarski(k5_xboole_0(sK2,k1_xboole_0))) | (~spl5_19 | spl5_138)),
% 14.02/2.20    inference(forward_demodulation,[],[f6866,f102])).
% 14.02/2.20  fof(f6866,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0)))) | (~spl5_19 | spl5_138)),
% 14.02/2.20    inference(backward_demodulation,[],[f6700,f6802])).
% 14.02/2.20  fof(f6700,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))))) | spl5_138),
% 14.02/2.20    inference(forward_demodulation,[],[f6689,f90])).
% 14.02/2.20  fof(f6689,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))))) | spl5_138),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f6687,f126])).
% 14.02/2.20  fof(f126,plain,(
% 14.02/2.20    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 14.02/2.20    inference(equality_resolution,[],[f76])).
% 14.02/2.20  fof(f76,plain,(
% 14.02/2.20    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 14.02/2.20    inference(cnf_transformation,[],[f51])).
% 14.02/2.20  fof(f51,plain,(
% 14.02/2.20    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 14.02/2.20    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f50])).
% 14.02/2.20  fof(f50,plain,(
% 14.02/2.20    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 14.02/2.20    introduced(choice_axiom,[])).
% 14.02/2.20  fof(f49,plain,(
% 14.02/2.20    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 14.02/2.20    inference(rectify,[],[f48])).
% 14.02/2.20  fof(f48,plain,(
% 14.02/2.20    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 14.02/2.20    inference(nnf_transformation,[],[f17])).
% 14.02/2.20  fof(f17,axiom,(
% 14.02/2.20    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 14.02/2.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 14.02/2.20  fof(f7046,plain,(
% 14.02/2.20    ~spl5_144 | ~spl5_19 | spl5_138),
% 14.02/2.20    inference(avatar_split_clause,[],[f6938,f6686,f527,f7044])).
% 14.02/2.20  fof(f7044,plain,(
% 14.02/2.20    spl5_144 <=> r2_hidden(k5_xboole_0(k1_xboole_0,sK2),k1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_144])])).
% 14.02/2.20  fof(f6938,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(k1_xboole_0,sK2),k1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))))) | (~spl5_19 | spl5_138)),
% 14.02/2.20    inference(forward_demodulation,[],[f6937,f91])).
% 14.02/2.20  fof(f6937,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k1_xboole_0),k1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))))) | (~spl5_19 | spl5_138)),
% 14.02/2.20    inference(forward_demodulation,[],[f6864,f102])).
% 14.02/2.20  fof(f6864,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0)),k1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))))) | (~spl5_19 | spl5_138)),
% 14.02/2.20    inference(backward_demodulation,[],[f6698,f6802])).
% 14.02/2.20  fof(f6698,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))),k1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))))) | spl5_138),
% 14.02/2.20    inference(forward_demodulation,[],[f6691,f90])).
% 14.02/2.20  fof(f6691,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))),k1_tarski(k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))) | spl5_138),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f6687,f126])).
% 14.02/2.20  fof(f6973,plain,(
% 14.02/2.20    ~spl5_143 | ~spl5_19 | spl5_141),
% 14.02/2.20    inference(avatar_split_clause,[],[f6948,f6798,f527,f6971])).
% 14.02/2.20  fof(f6971,plain,(
% 14.02/2.20    spl5_143 <=> k5_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_143])])).
% 14.02/2.20  fof(f6798,plain,(
% 14.02/2.20    spl5_141 <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_141])])).
% 14.02/2.20  fof(f6948,plain,(
% 14.02/2.20    k5_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | (~spl5_19 | spl5_141)),
% 14.02/2.20    inference(forward_demodulation,[],[f6947,f91])).
% 14.02/2.20  fof(f6947,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k1_xboole_0) != k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | (~spl5_19 | spl5_141)),
% 14.02/2.20    inference(forward_demodulation,[],[f6870,f102])).
% 14.02/2.20  fof(f6870,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | (~spl5_19 | spl5_141)),
% 14.02/2.20    inference(backward_demodulation,[],[f6799,f6802])).
% 14.02/2.20  fof(f6799,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | spl5_141),
% 14.02/2.20    inference(avatar_component_clause,[],[f6798])).
% 14.02/2.20  fof(f6952,plain,(
% 14.02/2.20    ~spl5_142 | ~spl5_19 | spl5_138),
% 14.02/2.20    inference(avatar_split_clause,[],[f6934,f6686,f527,f6950])).
% 14.02/2.20  fof(f6950,plain,(
% 14.02/2.20    spl5_142 <=> k5_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_142])])).
% 14.02/2.20  fof(f6934,plain,(
% 14.02/2.20    k5_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))) | (~spl5_19 | spl5_138)),
% 14.02/2.20    inference(forward_demodulation,[],[f6933,f91])).
% 14.02/2.20  fof(f6933,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k1_xboole_0) != k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))) | (~spl5_19 | spl5_138)),
% 14.02/2.20    inference(forward_demodulation,[],[f6862,f102])).
% 14.02/2.20  fof(f6862,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))) | (~spl5_19 | spl5_138)),
% 14.02/2.20    inference(backward_demodulation,[],[f6687,f6802])).
% 14.02/2.20  fof(f6800,plain,(
% 14.02/2.20    ~spl5_141 | spl5_138),
% 14.02/2.20    inference(avatar_split_clause,[],[f6695,f6686,f6798])).
% 14.02/2.20  fof(f6695,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | spl5_138),
% 14.02/2.20    inference(superposition,[],[f6687,f90])).
% 14.02/2.20  fof(f6751,plain,(
% 14.02/2.20    ~spl5_140 | ~spl5_11 | spl5_92),
% 14.02/2.20    inference(avatar_split_clause,[],[f6510,f4412,f257,f6749])).
% 14.02/2.20  fof(f6749,plain,(
% 14.02/2.20    spl5_140 <=> r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),k1_tarski(k5_xboole_0(k1_xboole_0,sK2)))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_140])])).
% 14.02/2.20  fof(f4412,plain,(
% 14.02/2.20    spl5_92 <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).
% 14.02/2.20  fof(f6510,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),k1_tarski(k5_xboole_0(k1_xboole_0,sK2))) | (~spl5_11 | spl5_92)),
% 14.02/2.20    inference(forward_demodulation,[],[f6509,f91])).
% 14.02/2.20  fof(f6509,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),k1_tarski(k5_xboole_0(sK2,k1_xboole_0))) | (~spl5_11 | spl5_92)),
% 14.02/2.20    inference(forward_demodulation,[],[f6467,f102])).
% 14.02/2.20  fof(f6467,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0)))) | (~spl5_11 | spl5_92)),
% 14.02/2.20    inference(backward_demodulation,[],[f4417,f6457])).
% 14.02/2.20  fof(f4417,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))))) | spl5_92),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f4413,f126])).
% 14.02/2.20  fof(f4413,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) | spl5_92),
% 14.02/2.20    inference(avatar_component_clause,[],[f4412])).
% 14.02/2.20  fof(f6717,plain,(
% 14.02/2.20    ~spl5_139 | ~spl5_11 | spl5_92),
% 14.02/2.20    inference(avatar_split_clause,[],[f6505,f4412,f257,f6715])).
% 14.02/2.20  fof(f6715,plain,(
% 14.02/2.20    spl5_139 <=> r2_hidden(k5_xboole_0(k1_xboole_0,sK2),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_139])])).
% 14.02/2.20  fof(f6505,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(k1_xboole_0,sK2),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))))) | (~spl5_11 | spl5_92)),
% 14.02/2.20    inference(forward_demodulation,[],[f6504,f91])).
% 14.02/2.20  fof(f6504,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k1_xboole_0),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))))) | (~spl5_11 | spl5_92)),
% 14.02/2.20    inference(forward_demodulation,[],[f6465,f102])).
% 14.02/2.20  fof(f6465,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0)),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))))) | (~spl5_11 | spl5_92)),
% 14.02/2.20    inference(backward_demodulation,[],[f4415,f6457])).
% 14.02/2.20  fof(f4415,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))))) | spl5_92),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f4413,f126])).
% 14.02/2.20  fof(f6688,plain,(
% 14.02/2.20    ~spl5_138 | spl5_2 | ~spl5_11 | spl5_18),
% 14.02/2.20    inference(avatar_split_clause,[],[f6527,f523,f257,f144,f6686])).
% 14.02/2.20  fof(f6527,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))) | (spl5_2 | ~spl5_11 | spl5_18)),
% 14.02/2.20    inference(forward_demodulation,[],[f6526,f91])).
% 14.02/2.20  fof(f6526,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k1_xboole_0)) != k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))) | (spl5_2 | ~spl5_11 | spl5_18)),
% 14.02/2.20    inference(forward_demodulation,[],[f6478,f91])).
% 14.02/2.20  fof(f6478,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k1_xboole_0)) != k5_xboole_0(k5_xboole_0(sK2,k1_xboole_0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_xboole_0))) | (spl5_2 | ~spl5_11 | spl5_18)),
% 14.02/2.20    inference(backward_demodulation,[],[f6360,f6457])).
% 14.02/2.20  fof(f6360,plain,(
% 14.02/2.20    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))) != k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) | (spl5_2 | spl5_18)),
% 14.02/2.20    inference(forward_demodulation,[],[f6316,f94])).
% 14.02/2.20  fof(f6316,plain,(
% 14.02/2.20    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))) != k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2)))) | (spl5_2 | spl5_18)),
% 14.02/2.20    inference(backward_demodulation,[],[f145,f6307])).
% 14.02/2.20  fof(f6565,plain,(
% 14.02/2.20    ~spl5_11 | spl5_32 | spl5_98),
% 14.02/2.20    inference(avatar_contradiction_clause,[],[f6564])).
% 14.02/2.20  fof(f6564,plain,(
% 14.02/2.20    $false | (~spl5_11 | spl5_32 | spl5_98)),
% 14.02/2.20    inference(subsumption_resolution,[],[f6563,f6053])).
% 14.02/2.20  fof(f6053,plain,(
% 14.02/2.20    ~r2_hidden(sK0,k5_xboole_0(k1_xboole_0,sK2)) | spl5_98),
% 14.02/2.20    inference(resolution,[],[f4542,f96])).
% 14.02/2.20  fof(f96,plain,(
% 14.02/2.20    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 14.02/2.20    inference(cnf_transformation,[],[f54])).
% 14.02/2.20  fof(f54,plain,(
% 14.02/2.20    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 14.02/2.20    inference(nnf_transformation,[],[f22])).
% 14.02/2.20  fof(f22,axiom,(
% 14.02/2.20    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 14.02/2.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 14.02/2.20  fof(f4542,plain,(
% 14.02/2.20    ~r1_tarski(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2)) | spl5_98),
% 14.02/2.20    inference(avatar_component_clause,[],[f4541])).
% 14.02/2.20  fof(f4541,plain,(
% 14.02/2.20    spl5_98 <=> r1_tarski(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).
% 14.02/2.20  fof(f6563,plain,(
% 14.02/2.20    r2_hidden(sK0,k5_xboole_0(k1_xboole_0,sK2)) | (~spl5_11 | spl5_32)),
% 14.02/2.20    inference(forward_demodulation,[],[f6434,f91])).
% 14.02/2.20  fof(f6434,plain,(
% 14.02/2.20    r2_hidden(sK0,k5_xboole_0(sK2,k1_xboole_0)) | (~spl5_11 | spl5_32)),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f989,f326,f84])).
% 14.02/2.20  fof(f84,plain,(
% 14.02/2.20    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 14.02/2.20    inference(cnf_transformation,[],[f52])).
% 14.02/2.20  fof(f989,plain,(
% 14.02/2.20    ~r2_hidden(sK0,k1_xboole_0) | spl5_32),
% 14.02/2.20    inference(avatar_component_clause,[],[f988])).
% 14.02/2.20  fof(f988,plain,(
% 14.02/2.20    spl5_32 <=> r2_hidden(sK0,k1_xboole_0)),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 14.02/2.20  fof(f6561,plain,(
% 14.02/2.20    ~spl5_11 | spl5_32 | spl5_98),
% 14.02/2.20    inference(avatar_contradiction_clause,[],[f6560])).
% 14.02/2.20  fof(f6560,plain,(
% 14.02/2.20    $false | (~spl5_11 | spl5_32 | spl5_98)),
% 14.02/2.20    inference(subsumption_resolution,[],[f6440,f6053])).
% 14.02/2.20  fof(f6440,plain,(
% 14.02/2.20    r2_hidden(sK0,k5_xboole_0(k1_xboole_0,sK2)) | (~spl5_11 | spl5_32)),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f989,f326,f85])).
% 14.02/2.20  fof(f85,plain,(
% 14.02/2.20    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 14.02/2.20    inference(cnf_transformation,[],[f52])).
% 14.02/2.20  fof(f6276,plain,(
% 14.02/2.20    spl5_4 | ~spl5_11 | spl5_132),
% 14.02/2.20    inference(avatar_contradiction_clause,[],[f6275])).
% 14.02/2.20  fof(f6275,plain,(
% 14.02/2.20    $false | (spl5_4 | ~spl5_11 | spl5_132)),
% 14.02/2.20    inference(subsumption_resolution,[],[f6274,f326])).
% 14.02/2.20  fof(f6274,plain,(
% 14.02/2.20    ~r2_hidden(sK0,sK2) | (spl5_4 | spl5_132)),
% 14.02/2.20    inference(subsumption_resolution,[],[f5838,f187])).
% 14.02/2.20  fof(f187,plain,(
% 14.02/2.20    ~r2_hidden(sK0,k1_tarski(sK1)) | spl5_4),
% 14.02/2.20    inference(avatar_component_clause,[],[f186])).
% 14.02/2.20  fof(f186,plain,(
% 14.02/2.20    spl5_4 <=> r2_hidden(sK0,k1_tarski(sK1))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 14.02/2.20  fof(f5838,plain,(
% 14.02/2.20    r2_hidden(sK0,k1_tarski(sK1)) | ~r2_hidden(sK0,sK2) | spl5_132),
% 14.02/2.20    inference(resolution,[],[f5809,f84])).
% 14.02/2.20  fof(f5809,plain,(
% 14.02/2.20    ~r2_hidden(sK0,k5_xboole_0(sK2,k1_tarski(sK1))) | spl5_132),
% 14.02/2.20    inference(avatar_component_clause,[],[f5808])).
% 14.02/2.20  fof(f5808,plain,(
% 14.02/2.20    spl5_132 <=> r2_hidden(sK0,k5_xboole_0(sK2,k1_tarski(sK1)))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_132])])).
% 14.02/2.20  fof(f6273,plain,(
% 14.02/2.20    spl5_4 | ~spl5_11 | spl5_132),
% 14.02/2.20    inference(avatar_contradiction_clause,[],[f6272])).
% 14.02/2.20  fof(f6272,plain,(
% 14.02/2.20    $false | (spl5_4 | ~spl5_11 | spl5_132)),
% 14.02/2.20    inference(subsumption_resolution,[],[f5811,f326])).
% 14.02/2.20  fof(f5811,plain,(
% 14.02/2.20    ~r2_hidden(sK0,sK2) | (spl5_4 | spl5_132)),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f187,f5809,f84])).
% 14.02/2.20  fof(f6266,plain,(
% 14.02/2.20    ~spl5_11 | spl5_32 | spl5_95),
% 14.02/2.20    inference(avatar_contradiction_clause,[],[f6265])).
% 14.02/2.20  fof(f6265,plain,(
% 14.02/2.20    $false | (~spl5_11 | spl5_32 | spl5_95)),
% 14.02/2.20    inference(subsumption_resolution,[],[f326,f6239])).
% 14.02/2.20  fof(f6239,plain,(
% 14.02/2.20    ~r2_hidden(sK0,sK2) | (spl5_32 | spl5_95)),
% 14.02/2.20    inference(subsumption_resolution,[],[f6017,f989])).
% 14.02/2.20  fof(f6017,plain,(
% 14.02/2.20    r2_hidden(sK0,k1_xboole_0) | ~r2_hidden(sK0,sK2) | spl5_95),
% 14.02/2.20    inference(resolution,[],[f4494,f85])).
% 14.02/2.20  fof(f4494,plain,(
% 14.02/2.20    ~r2_hidden(sK0,k5_xboole_0(k1_xboole_0,sK2)) | spl5_95),
% 14.02/2.20    inference(avatar_component_clause,[],[f4493])).
% 14.02/2.20  fof(f4493,plain,(
% 14.02/2.20    spl5_95 <=> r2_hidden(sK0,k5_xboole_0(k1_xboole_0,sK2))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_95])])).
% 14.02/2.20  fof(f6262,plain,(
% 14.02/2.20    ~spl5_19 | spl5_130),
% 14.02/2.20    inference(avatar_contradiction_clause,[],[f6261])).
% 14.02/2.20  fof(f6261,plain,(
% 14.02/2.20    $false | (~spl5_19 | spl5_130)),
% 14.02/2.20    inference(subsumption_resolution,[],[f2032,f5795])).
% 14.02/2.20  fof(f5795,plain,(
% 14.02/2.20    ~r1_xboole_0(sK2,k1_tarski(sK1)) | spl5_130),
% 14.02/2.20    inference(trivial_inequality_removal,[],[f5794])).
% 14.02/2.20  fof(f5794,plain,(
% 14.02/2.20    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(sK2,k1_tarski(sK1)) | spl5_130),
% 14.02/2.20    inference(superposition,[],[f5734,f86])).
% 14.02/2.20  fof(f5734,plain,(
% 14.02/2.20    k1_xboole_0 != k3_xboole_0(sK2,k1_tarski(sK1)) | spl5_130),
% 14.02/2.20    inference(avatar_component_clause,[],[f5733])).
% 14.02/2.20  fof(f5733,plain,(
% 14.02/2.20    spl5_130 <=> k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK1))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_130])])).
% 14.02/2.20  fof(f6233,plain,(
% 14.02/2.20    ~spl5_74 | ~spl5_18 | spl5_25 | spl5_132),
% 14.02/2.20    inference(avatar_split_clause,[],[f6221,f5808,f632,f523,f3441])).
% 14.02/2.20  fof(f3441,plain,(
% 14.02/2.20    spl5_74 <=> k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).
% 14.02/2.20  fof(f632,plain,(
% 14.02/2.20    spl5_25 <=> k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 14.02/2.20  fof(f6221,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | (~spl5_18 | spl5_25 | spl5_132)),
% 14.02/2.20    inference(subsumption_resolution,[],[f6220,f5813])).
% 14.02/2.20  fof(f5813,plain,(
% 14.02/2.20    r1_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_tarski(sK1))) | spl5_132),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f5809,f81])).
% 14.02/2.20  fof(f6220,plain,(
% 14.02/2.20    ~r1_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_tarski(sK1))) | k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | (~spl5_18 | spl5_25)),
% 14.02/2.20    inference(forward_demodulation,[],[f6219,f5292])).
% 14.02/2.20  fof(f5292,plain,(
% 14.02/2.20    k1_tarski(sK1) = k3_xboole_0(sK2,k1_tarski(sK1)) | ~spl5_18),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f524,f80])).
% 14.02/2.20  fof(f524,plain,(
% 14.02/2.20    r2_hidden(sK1,sK2) | ~spl5_18),
% 14.02/2.20    inference(avatar_component_clause,[],[f523])).
% 14.02/2.20  fof(f6219,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | ~r1_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))) | (~spl5_18 | spl5_25)),
% 14.02/2.20    inference(forward_demodulation,[],[f931,f5292])).
% 14.02/2.20  fof(f931,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | ~r1_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))) | spl5_25),
% 14.02/2.20    inference(forward_demodulation,[],[f918,f91])).
% 14.02/2.20  fof(f918,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | ~r1_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))) | spl5_25),
% 14.02/2.20    inference(superposition,[],[f633,f116])).
% 14.02/2.20  fof(f116,plain,(
% 14.02/2.20    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 14.02/2.20    inference(definition_unfolding,[],[f71,f73])).
% 14.02/2.20  fof(f71,plain,(
% 14.02/2.20    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 14.02/2.20    inference(cnf_transformation,[],[f47])).
% 14.02/2.20  fof(f47,plain,(
% 14.02/2.20    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 14.02/2.20    inference(nnf_transformation,[],[f14])).
% 14.02/2.20  fof(f14,axiom,(
% 14.02/2.20    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 14.02/2.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 14.02/2.20  fof(f633,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | spl5_25),
% 14.02/2.20    inference(avatar_component_clause,[],[f632])).
% 14.02/2.20  fof(f6218,plain,(
% 14.02/2.20    spl5_3 | ~spl5_18 | spl5_120),
% 14.02/2.20    inference(avatar_contradiction_clause,[],[f6217])).
% 14.02/2.20  fof(f6217,plain,(
% 14.02/2.20    $false | (spl5_3 | ~spl5_18 | spl5_120)),
% 14.02/2.20    inference(subsumption_resolution,[],[f6214,f5323])).
% 14.02/2.20  fof(f5323,plain,(
% 14.02/2.20    r2_hidden(sK1,k5_xboole_0(sK2,k1_tarski(sK0))) | (spl5_3 | ~spl5_18)),
% 14.02/2.20    inference(forward_demodulation,[],[f5303,f91])).
% 14.02/2.20  fof(f5303,plain,(
% 14.02/2.20    r2_hidden(sK1,k5_xboole_0(k1_tarski(sK0),sK2)) | (spl5_3 | ~spl5_18)),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f183,f524,f85])).
% 14.02/2.20  fof(f183,plain,(
% 14.02/2.20    ~r2_hidden(sK1,k1_tarski(sK0)) | spl5_3),
% 14.02/2.20    inference(avatar_component_clause,[],[f182])).
% 14.02/2.20  fof(f182,plain,(
% 14.02/2.20    spl5_3 <=> r2_hidden(sK1,k1_tarski(sK0))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 14.02/2.20  fof(f6214,plain,(
% 14.02/2.20    ~r2_hidden(sK1,k5_xboole_0(sK2,k1_tarski(sK0))) | spl5_120),
% 14.02/2.20    inference(resolution,[],[f5124,f96])).
% 14.02/2.20  fof(f5124,plain,(
% 14.02/2.20    ~r1_tarski(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))) | spl5_120),
% 14.02/2.20    inference(avatar_component_clause,[],[f5123])).
% 14.02/2.20  fof(f5123,plain,(
% 14.02/2.20    spl5_120 <=> r1_tarski(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_120])])).
% 14.02/2.20  fof(f6216,plain,(
% 14.02/2.20    spl5_3 | ~spl5_18 | spl5_120),
% 14.02/2.20    inference(avatar_contradiction_clause,[],[f6215])).
% 14.02/2.20  fof(f6215,plain,(
% 14.02/2.20    $false | (spl5_3 | ~spl5_18 | spl5_120)),
% 14.02/2.20    inference(subsumption_resolution,[],[f6213,f5323])).
% 14.02/2.20  fof(f6213,plain,(
% 14.02/2.20    ~r2_hidden(sK1,k5_xboole_0(sK2,k1_tarski(sK0))) | spl5_120),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f5124,f96])).
% 14.02/2.20  fof(f6212,plain,(
% 14.02/2.20    ~spl5_137 | spl5_99),
% 14.02/2.20    inference(avatar_split_clause,[],[f4585,f4555,f6210])).
% 14.02/2.20  fof(f6210,plain,(
% 14.02/2.20    spl5_137 <=> r1_tarski(k1_tarski(sK0),k5_xboole_0(sK2,sK2))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_137])])).
% 14.02/2.20  fof(f4555,plain,(
% 14.02/2.20    spl5_99 <=> r2_hidden(sK0,k5_xboole_0(sK2,sK2))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_99])])).
% 14.02/2.20  fof(f4585,plain,(
% 14.02/2.20    ~r1_tarski(k1_tarski(sK0),k5_xboole_0(sK2,sK2)) | spl5_99),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f4556,f95])).
% 14.02/2.20  fof(f95,plain,(
% 14.02/2.20    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 14.02/2.20    inference(cnf_transformation,[],[f54])).
% 14.02/2.20  fof(f4556,plain,(
% 14.02/2.20    ~r2_hidden(sK0,k5_xboole_0(sK2,sK2)) | spl5_99),
% 14.02/2.20    inference(avatar_component_clause,[],[f4555])).
% 14.02/2.20  fof(f6120,plain,(
% 14.02/2.20    spl5_136 | spl5_99),
% 14.02/2.20    inference(avatar_split_clause,[],[f4571,f4555,f6118])).
% 14.02/2.20  fof(f6118,plain,(
% 14.02/2.20    spl5_136 <=> r1_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,sK2))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_136])])).
% 14.02/2.20  fof(f4571,plain,(
% 14.02/2.20    r1_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,sK2)) | spl5_99),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f4556,f81])).
% 14.02/2.20  fof(f6107,plain,(
% 14.02/2.20    ~spl5_135 | spl5_100 | ~spl5_133),
% 14.02/2.20    inference(avatar_split_clause,[],[f6068,f6048,f4559,f6105])).
% 14.02/2.20  fof(f4559,plain,(
% 14.02/2.20    spl5_100 <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).
% 14.02/2.20  fof(f6048,plain,(
% 14.02/2.20    spl5_133 <=> r1_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_133])])).
% 14.02/2.20  fof(f6068,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))) | (spl5_100 | ~spl5_133)),
% 14.02/2.20    inference(backward_demodulation,[],[f4560,f6056])).
% 14.02/2.20  fof(f6056,plain,(
% 14.02/2.20    k1_tarski(sK0) = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))) | ~spl5_133),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f6049,f116])).
% 14.02/2.20  fof(f6049,plain,(
% 14.02/2.20    r1_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2)) | ~spl5_133),
% 14.02/2.20    inference(avatar_component_clause,[],[f6048])).
% 14.02/2.20  fof(f4560,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))) | spl5_100),
% 14.02/2.20    inference(avatar_component_clause,[],[f4559])).
% 14.02/2.20  fof(f6103,plain,(
% 14.02/2.20    spl5_134 | ~spl5_10),
% 14.02/2.20    inference(avatar_split_clause,[],[f4462,f253,f6101])).
% 14.02/2.20  fof(f6101,plain,(
% 14.02/2.20    spl5_134 <=> k1_xboole_0 = k3_xboole_0(k1_tarski(sK0),sK2)),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_134])])).
% 14.02/2.20  fof(f253,plain,(
% 14.02/2.20    spl5_10 <=> r1_xboole_0(k1_tarski(sK0),sK2)),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 14.02/2.20  fof(f4462,plain,(
% 14.02/2.20    k1_xboole_0 = k3_xboole_0(k1_tarski(sK0),sK2) | ~spl5_10),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f587,f86])).
% 14.02/2.20  fof(f587,plain,(
% 14.02/2.20    r1_xboole_0(k1_tarski(sK0),sK2) | ~spl5_10),
% 14.02/2.20    inference(avatar_component_clause,[],[f253])).
% 14.02/2.20  fof(f6051,plain,(
% 14.02/2.20    ~spl5_98 | spl5_95),
% 14.02/2.20    inference(avatar_split_clause,[],[f6009,f4493,f4541])).
% 14.02/2.20  fof(f6009,plain,(
% 14.02/2.20    ~r1_tarski(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2)) | spl5_95),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f4494,f95])).
% 14.02/2.20  fof(f6050,plain,(
% 14.02/2.20    spl5_133 | spl5_95),
% 14.02/2.20    inference(avatar_split_clause,[],[f5989,f4493,f6048])).
% 14.02/2.20  fof(f5989,plain,(
% 14.02/2.20    r1_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2)) | spl5_95),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f4494,f81])).
% 14.02/2.20  fof(f5986,plain,(
% 14.02/2.20    ~spl5_95 | spl5_11 | spl5_32),
% 14.02/2.20    inference(avatar_split_clause,[],[f4430,f988,f257,f4493])).
% 14.02/2.20  fof(f4430,plain,(
% 14.02/2.20    ~r2_hidden(sK0,k5_xboole_0(k1_xboole_0,sK2)) | (spl5_11 | spl5_32)),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f989,f258,f82])).
% 14.02/2.20  fof(f258,plain,(
% 14.02/2.20    ~r2_hidden(sK0,sK2) | spl5_11),
% 14.02/2.20    inference(avatar_component_clause,[],[f257])).
% 14.02/2.20  fof(f5810,plain,(
% 14.02/2.20    ~spl5_132 | spl5_4 | spl5_11),
% 14.02/2.20    inference(avatar_split_clause,[],[f4448,f257,f186,f5808])).
% 14.02/2.20  fof(f4448,plain,(
% 14.02/2.20    ~r2_hidden(sK0,k5_xboole_0(sK2,k1_tarski(sK1))) | (spl5_4 | spl5_11)),
% 14.02/2.20    inference(forward_demodulation,[],[f4431,f91])).
% 14.02/2.20  fof(f4431,plain,(
% 14.02/2.20    ~r2_hidden(sK0,k5_xboole_0(k1_tarski(sK1),sK2)) | (spl5_4 | spl5_11)),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f187,f258,f82])).
% 14.02/2.20  fof(f5806,plain,(
% 14.02/2.20    spl5_131 | spl5_11),
% 14.02/2.20    inference(avatar_split_clause,[],[f4442,f257,f5804])).
% 14.02/2.20  fof(f5804,plain,(
% 14.02/2.20    spl5_131 <=> ! [X0] : ~r2_hidden(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0)))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_131])])).
% 14.02/2.20  fof(f4442,plain,(
% 14.02/2.20    ( ! [X0] : (~r2_hidden(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0)))) ) | spl5_11),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f258,f123])).
% 14.02/2.20  fof(f123,plain,(
% 14.02/2.20    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X0)) )),
% 14.02/2.20    inference(equality_resolution,[],[f112])).
% 14.02/2.20  fof(f112,plain,(
% 14.02/2.20    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 14.02/2.20    inference(definition_unfolding,[],[f63,f73])).
% 14.02/2.20  fof(f63,plain,(
% 14.02/2.20    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 14.02/2.20    inference(cnf_transformation,[],[f45])).
% 14.02/2.20  fof(f45,plain,(
% 14.02/2.20    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 14.02/2.20    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).
% 14.02/2.20  fof(f44,plain,(
% 14.02/2.20    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 14.02/2.20    introduced(choice_axiom,[])).
% 14.02/2.20  fof(f43,plain,(
% 14.02/2.20    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 14.02/2.20    inference(rectify,[],[f42])).
% 14.02/2.20  fof(f42,plain,(
% 14.02/2.20    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 14.02/2.20    inference(flattening,[],[f41])).
% 14.02/2.20  fof(f41,plain,(
% 14.02/2.20    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 14.02/2.20    inference(nnf_transformation,[],[f3])).
% 14.02/2.20  fof(f3,axiom,(
% 14.02/2.20    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 14.02/2.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 14.02/2.20  fof(f5735,plain,(
% 14.02/2.20    ~spl5_130 | spl5_19),
% 14.02/2.20    inference(avatar_split_clause,[],[f5446,f527,f5733])).
% 14.02/2.20  fof(f5446,plain,(
% 14.02/2.20    k1_xboole_0 != k3_xboole_0(sK2,k1_tarski(sK1)) | spl5_19),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f528,f87])).
% 14.02/2.20  fof(f87,plain,(
% 14.02/2.20    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 14.02/2.20    inference(cnf_transformation,[],[f53])).
% 14.02/2.20  fof(f528,plain,(
% 14.02/2.20    ~r1_xboole_0(sK2,k1_tarski(sK1)) | spl5_19),
% 14.02/2.20    inference(avatar_component_clause,[],[f527])).
% 14.02/2.20  fof(f5731,plain,(
% 14.02/2.20    ~spl5_129 | ~spl5_18),
% 14.02/2.20    inference(avatar_split_clause,[],[f5407,f523,f5729])).
% 14.02/2.20  fof(f5729,plain,(
% 14.02/2.20    spl5_129 <=> sK2 = k5_xboole_0(sK2,k1_tarski(sK1))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_129])])).
% 14.02/2.20  fof(f5407,plain,(
% 14.02/2.20    sK2 != k5_xboole_0(sK2,k1_tarski(sK1)) | ~spl5_18),
% 14.02/2.20    inference(backward_demodulation,[],[f5309,f5292])).
% 14.02/2.20  fof(f5309,plain,(
% 14.02/2.20    sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))) | ~spl5_18),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f524,f114])).
% 14.02/2.20  fof(f114,plain,(
% 14.02/2.20    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_tarski(X1))) != X0 | ~r2_hidden(X1,X0)) )),
% 14.02/2.20    inference(definition_unfolding,[],[f69,f73])).
% 14.02/2.20  fof(f69,plain,(
% 14.02/2.20    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 14.02/2.20    inference(cnf_transformation,[],[f46])).
% 14.02/2.20  fof(f5712,plain,(
% 14.02/2.20    ~spl5_72 | ~spl5_18),
% 14.02/2.20    inference(avatar_split_clause,[],[f5325,f523,f2632])).
% 14.02/2.20  fof(f2632,plain,(
% 14.02/2.20    spl5_72 <=> r2_hidden(sK1,k5_xboole_0(sK2,k1_tarski(sK1)))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).
% 14.02/2.20  fof(f5325,plain,(
% 14.02/2.20    ~r2_hidden(sK1,k5_xboole_0(sK2,k1_tarski(sK1))) | ~spl5_18),
% 14.02/2.20    inference(forward_demodulation,[],[f5296,f91])).
% 14.02/2.20  fof(f5296,plain,(
% 14.02/2.20    ~r2_hidden(sK1,k5_xboole_0(k1_tarski(sK1),sK2)) | ~spl5_18),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f125,f524,f83])).
% 14.02/2.20  fof(f83,plain,(
% 14.02/2.20    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 14.02/2.20    inference(cnf_transformation,[],[f52])).
% 14.02/2.20  fof(f125,plain,(
% 14.02/2.20    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 14.02/2.20    inference(equality_resolution,[],[f124])).
% 14.02/2.20  fof(f124,plain,(
% 14.02/2.20    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 14.02/2.20    inference(equality_resolution,[],[f77])).
% 14.02/2.20  fof(f77,plain,(
% 14.02/2.20    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 14.02/2.20    inference(cnf_transformation,[],[f51])).
% 14.02/2.20  fof(f5598,plain,(
% 14.02/2.20    ~spl5_128 | ~spl5_8 | spl5_93),
% 14.02/2.20    inference(avatar_split_clause,[],[f5198,f4451,f242,f5596])).
% 14.02/2.20  fof(f5596,plain,(
% 14.02/2.20    spl5_128 <=> r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_128])])).
% 14.02/2.20  fof(f242,plain,(
% 14.02/2.20    spl5_8 <=> r1_xboole_0(sK2,k1_tarski(sK0))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 14.02/2.20  fof(f4451,plain,(
% 14.02/2.20    spl5_93 <=> k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).
% 14.02/2.20  fof(f5198,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))))) | (~spl5_8 | spl5_93)),
% 14.02/2.20    inference(forward_demodulation,[],[f5197,f91])).
% 14.02/2.20  fof(f5197,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k1_xboole_0))))) | (~spl5_8 | spl5_93)),
% 14.02/2.20    inference(forward_demodulation,[],[f4456,f4524])).
% 14.02/2.20  fof(f4524,plain,(
% 14.02/2.20    k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK0)) | ~spl5_8),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f932,f86])).
% 14.02/2.20  fof(f932,plain,(
% 14.02/2.20    r1_xboole_0(sK2,k1_tarski(sK0)) | ~spl5_8),
% 14.02/2.20    inference(avatar_component_clause,[],[f242])).
% 14.02/2.20  fof(f4456,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))))) | spl5_93),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f4452,f126])).
% 14.02/2.20  fof(f4452,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) | spl5_93),
% 14.02/2.20    inference(avatar_component_clause,[],[f4451])).
% 14.02/2.20  fof(f5537,plain,(
% 14.02/2.20    ~spl5_127 | ~spl5_8 | spl5_93),
% 14.02/2.20    inference(avatar_split_clause,[],[f5194,f4451,f242,f5535])).
% 14.02/2.20  fof(f5535,plain,(
% 14.02/2.20    spl5_127 <=> r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_127])])).
% 14.02/2.20  fof(f5194,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))))) | (~spl5_8 | spl5_93)),
% 14.02/2.20    inference(forward_demodulation,[],[f5193,f91])).
% 14.02/2.20  fof(f5193,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k1_xboole_0))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))))) | (~spl5_8 | spl5_93)),
% 14.02/2.20    inference(forward_demodulation,[],[f4454,f4524])).
% 14.02/2.20  fof(f4454,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))))) | spl5_93),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f4452,f126])).
% 14.02/2.20  fof(f5508,plain,(
% 14.02/2.20    ~spl5_16 | spl5_3 | ~spl5_61),
% 14.02/2.20    inference(avatar_split_clause,[],[f2504,f2382,f182,f482])).
% 14.02/2.20  fof(f2382,plain,(
% 14.02/2.20    spl5_61 <=> r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).
% 14.02/2.20  fof(f2504,plain,(
% 14.02/2.20    ~r2_hidden(sK1,k1_xboole_0) | (spl5_3 | ~spl5_61)),
% 14.02/2.20    inference(backward_demodulation,[],[f196,f2499])).
% 14.02/2.20  fof(f2499,plain,(
% 14.02/2.20    k1_xboole_0 = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~spl5_61),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f2383,f86])).
% 14.02/2.20  fof(f2383,plain,(
% 14.02/2.20    r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~spl5_61),
% 14.02/2.20    inference(avatar_component_clause,[],[f2382])).
% 14.02/2.20  fof(f196,plain,(
% 14.02/2.20    ~r2_hidden(sK1,k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | spl5_3),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f120,f183,f85])).
% 14.02/2.20  fof(f120,plain,(
% 14.02/2.20    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(X1,k3_xboole_0(X1,k1_tarski(X2))))) )),
% 14.02/2.20    inference(equality_resolution,[],[f105])).
% 14.02/2.20  fof(f105,plain,(
% 14.02/2.20    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k1_tarski(X2))))) )),
% 14.02/2.20    inference(definition_unfolding,[],[f61,f73])).
% 14.02/2.20  fof(f61,plain,(
% 14.02/2.20    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 14.02/2.20    inference(cnf_transformation,[],[f40])).
% 14.02/2.20  fof(f40,plain,(
% 14.02/2.20    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 14.02/2.20    inference(flattening,[],[f39])).
% 14.02/2.20  fof(f39,plain,(
% 14.02/2.20    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 14.02/2.20    inference(nnf_transformation,[],[f27])).
% 14.02/2.20  fof(f27,axiom,(
% 14.02/2.20    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 14.02/2.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 14.02/2.20  fof(f5507,plain,(
% 14.02/2.20    ~spl5_126 | ~spl5_8 | spl5_92),
% 14.02/2.20    inference(avatar_split_clause,[],[f5207,f4412,f242,f5505])).
% 14.02/2.20  fof(f5505,plain,(
% 14.02/2.20    spl5_126 <=> r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_126])])).
% 14.02/2.20  fof(f5207,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))))) | (~spl5_8 | spl5_92)),
% 14.02/2.20    inference(forward_demodulation,[],[f5206,f91])).
% 14.02/2.20  fof(f5206,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k1_xboole_0))))) | (~spl5_8 | spl5_92)),
% 14.02/2.20    inference(forward_demodulation,[],[f4417,f4524])).
% 14.02/2.20  fof(f5475,plain,(
% 14.02/2.20    ~spl5_125 | ~spl5_8 | spl5_92),
% 14.02/2.20    inference(avatar_split_clause,[],[f5202,f4412,f242,f5473])).
% 14.02/2.20  fof(f5473,plain,(
% 14.02/2.20    spl5_125 <=> r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_125])])).
% 14.02/2.20  fof(f5202,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))))) | (~spl5_8 | spl5_92)),
% 14.02/2.20    inference(forward_demodulation,[],[f5201,f91])).
% 14.02/2.20  fof(f5201,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k1_xboole_0))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))))) | (~spl5_8 | spl5_92)),
% 14.02/2.20    inference(forward_demodulation,[],[f4415,f4524])).
% 14.02/2.20  fof(f5453,plain,(
% 14.02/2.20    ~spl5_124 | ~spl5_8 | spl5_92),
% 14.02/2.20    inference(avatar_split_clause,[],[f4424,f4412,f242,f5451])).
% 14.02/2.20  fof(f5451,plain,(
% 14.02/2.20    spl5_124 <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_124])])).
% 14.02/2.20  fof(f4424,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))) | (~spl5_8 | spl5_92)),
% 14.02/2.20    inference(forward_demodulation,[],[f4423,f91])).
% 14.02/2.20  fof(f4423,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k1_xboole_0))) | (~spl5_8 | spl5_92)),
% 14.02/2.20    inference(subsumption_resolution,[],[f4421,f932])).
% 14.02/2.20  fof(f4421,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k1_xboole_0))) | ~r1_xboole_0(sK2,k1_tarski(sK0)) | spl5_92),
% 14.02/2.20    inference(superposition,[],[f4413,f86])).
% 14.02/2.20  fof(f5289,plain,(
% 14.02/2.20    spl5_3 | ~spl5_18 | ~spl5_61 | spl5_90),
% 14.02/2.20    inference(avatar_contradiction_clause,[],[f5288])).
% 14.02/2.20  fof(f5288,plain,(
% 14.02/2.20    $false | (spl5_3 | ~spl5_18 | ~spl5_61 | spl5_90)),
% 14.02/2.20    inference(subsumption_resolution,[],[f2504,f5287])).
% 14.02/2.20  fof(f5287,plain,(
% 14.02/2.20    r2_hidden(sK1,k1_xboole_0) | (~spl5_18 | spl5_90)),
% 14.02/2.20    inference(subsumption_resolution,[],[f4186,f524])).
% 14.02/2.20  fof(f4186,plain,(
% 14.02/2.20    r2_hidden(sK1,k1_xboole_0) | ~r2_hidden(sK1,sK2) | spl5_90),
% 14.02/2.20    inference(resolution,[],[f4141,f85])).
% 14.02/2.20  fof(f4141,plain,(
% 14.02/2.20    ~r2_hidden(sK1,k5_xboole_0(k1_xboole_0,sK2)) | spl5_90),
% 14.02/2.20    inference(avatar_component_clause,[],[f4140])).
% 14.02/2.20  fof(f5284,plain,(
% 14.02/2.20    ~spl5_18 | spl5_48 | spl5_90),
% 14.02/2.20    inference(avatar_contradiction_clause,[],[f5283])).
% 14.02/2.20  fof(f5283,plain,(
% 14.02/2.20    $false | (~spl5_18 | spl5_48 | spl5_90)),
% 14.02/2.20    inference(subsumption_resolution,[],[f524,f5223])).
% 14.02/2.20  fof(f5223,plain,(
% 14.02/2.20    ~r2_hidden(sK1,sK2) | (spl5_48 | spl5_90)),
% 14.02/2.20    inference(subsumption_resolution,[],[f4186,f3430])).
% 14.02/2.20  fof(f3430,plain,(
% 14.02/2.20    ~r2_hidden(sK1,k1_xboole_0) | spl5_48),
% 14.02/2.20    inference(resolution,[],[f1989,f96])).
% 14.02/2.20  fof(f1989,plain,(
% 14.02/2.20    ~r1_tarski(k1_tarski(sK1),k1_xboole_0) | spl5_48),
% 14.02/2.20    inference(avatar_component_clause,[],[f1988])).
% 14.02/2.20  fof(f1988,plain,(
% 14.02/2.20    spl5_48 <=> r1_tarski(k1_tarski(sK1),k1_xboole_0)),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 14.02/2.20  fof(f5192,plain,(
% 14.02/2.20    spl5_117 | spl5_123),
% 14.02/2.20    inference(avatar_contradiction_clause,[],[f5191])).
% 14.02/2.20  fof(f5191,plain,(
% 14.02/2.20    $false | (spl5_117 | spl5_123)),
% 14.02/2.20    inference(subsumption_resolution,[],[f5140,f5112])).
% 14.02/2.20  fof(f5112,plain,(
% 14.02/2.20    ~r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))) | spl5_117),
% 14.02/2.20    inference(avatar_component_clause,[],[f5111])).
% 14.02/2.20  fof(f5111,plain,(
% 14.02/2.20    spl5_117 <=> r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_117])])).
% 14.02/2.20  fof(f5140,plain,(
% 14.02/2.20    r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))) | spl5_123),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f5136,f81])).
% 14.02/2.20  fof(f5137,plain,(
% 14.02/2.20    ~spl5_123 | spl5_3 | spl5_18),
% 14.02/2.20    inference(avatar_split_clause,[],[f3935,f523,f182,f5135])).
% 14.02/2.20  fof(f3935,plain,(
% 14.02/2.20    ~r2_hidden(sK1,k5_xboole_0(sK2,k1_tarski(sK0))) | (spl5_3 | spl5_18)),
% 14.02/2.20    inference(forward_demodulation,[],[f3796,f91])).
% 14.02/2.20  fof(f3796,plain,(
% 14.02/2.20    ~r2_hidden(sK1,k5_xboole_0(k1_tarski(sK0),sK2)) | (spl5_3 | spl5_18)),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f183,f1325,f82])).
% 14.02/2.20  fof(f5133,plain,(
% 14.02/2.20    ~spl5_122 | spl5_66),
% 14.02/2.20    inference(avatar_split_clause,[],[f2599,f2458,f5131])).
% 14.02/2.20  fof(f5131,plain,(
% 14.02/2.20    spl5_122 <=> r1_tarski(k1_tarski(sK1),k5_xboole_0(sK2,sK2))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_122])])).
% 14.02/2.20  fof(f2458,plain,(
% 14.02/2.20    spl5_66 <=> r2_hidden(sK1,k5_xboole_0(sK2,sK2))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).
% 14.02/2.20  fof(f2599,plain,(
% 14.02/2.20    ~r1_tarski(k1_tarski(sK1),k5_xboole_0(sK2,sK2)) | spl5_66),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f2459,f95])).
% 14.02/2.20  fof(f2459,plain,(
% 14.02/2.20    ~r2_hidden(sK1,k5_xboole_0(sK2,sK2)) | spl5_66),
% 14.02/2.20    inference(avatar_component_clause,[],[f2458])).
% 14.02/2.20  fof(f5129,plain,(
% 14.02/2.20    spl5_121 | spl5_18),
% 14.02/2.20    inference(avatar_split_clause,[],[f3809,f523,f5127])).
% 14.02/2.20  fof(f5127,plain,(
% 14.02/2.20    spl5_121 <=> ! [X0] : ~r2_hidden(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,X0)))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_121])])).
% 14.02/2.20  fof(f3809,plain,(
% 14.02/2.20    ( ! [X0] : (~r2_hidden(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,X0)))) ) | spl5_18),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f1325,f123])).
% 14.02/2.20  fof(f5125,plain,(
% 14.02/2.20    ~spl5_120 | spl5_74),
% 14.02/2.20    inference(avatar_split_clause,[],[f3454,f3441,f5123])).
% 14.02/2.20  fof(f3454,plain,(
% 14.02/2.20    ~r1_tarski(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))) | spl5_74),
% 14.02/2.20    inference(trivial_inequality_removal,[],[f3452])).
% 14.02/2.20  fof(f3452,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | ~r1_tarski(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))) | spl5_74),
% 14.02/2.20    inference(superposition,[],[f3442,f93])).
% 14.02/2.20  fof(f3442,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | spl5_74),
% 14.02/2.20    inference(avatar_component_clause,[],[f3441])).
% 14.02/2.20  fof(f5121,plain,(
% 14.02/2.20    spl5_119 | spl5_66),
% 14.02/2.20    inference(avatar_split_clause,[],[f2585,f2458,f5119])).
% 14.02/2.20  fof(f5119,plain,(
% 14.02/2.20    spl5_119 <=> r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,sK2))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_119])])).
% 14.02/2.20  fof(f2585,plain,(
% 14.02/2.20    r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,sK2)) | spl5_66),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f2459,f81])).
% 14.02/2.20  fof(f5117,plain,(
% 14.02/2.20    ~spl5_118 | spl5_4),
% 14.02/2.20    inference(avatar_split_clause,[],[f3316,f186,f5115])).
% 14.02/2.20  fof(f5115,plain,(
% 14.02/2.20    spl5_118 <=> r2_hidden(sK0,k5_xboole_0(k1_tarski(sK1),k1_tarski(sK1)))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).
% 14.02/2.20  fof(f3316,plain,(
% 14.02/2.20    ~r2_hidden(sK0,k5_xboole_0(k1_tarski(sK1),k1_tarski(sK1))) | spl5_4),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f187,f187,f82])).
% 14.02/2.20  fof(f5113,plain,(
% 14.02/2.20    ~spl5_117 | spl5_57),
% 14.02/2.20    inference(avatar_split_clause,[],[f3264,f2327,f5111])).
% 14.02/2.20  fof(f2327,plain,(
% 14.02/2.20    spl5_57 <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).
% 14.02/2.20  fof(f3264,plain,(
% 14.02/2.20    ~r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))) | spl5_57),
% 14.02/2.20    inference(trivial_inequality_removal,[],[f3263])).
% 14.02/2.20  fof(f3263,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) | ~r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))) | spl5_57),
% 14.02/2.20    inference(forward_demodulation,[],[f2335,f91])).
% 14.02/2.20  fof(f2335,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_xboole_0)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) | ~r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))) | spl5_57),
% 14.02/2.20    inference(superposition,[],[f2328,f86])).
% 14.02/2.20  fof(f2328,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | spl5_57),
% 14.02/2.20    inference(avatar_component_clause,[],[f2327])).
% 14.02/2.20  fof(f5109,plain,(
% 14.02/2.20    spl5_116 | spl5_32),
% 14.02/2.20    inference(avatar_split_clause,[],[f2560,f988,f5107])).
% 14.02/2.20  fof(f5107,plain,(
% 14.02/2.20    spl5_116 <=> r2_hidden(sK0,k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_116])])).
% 14.02/2.20  fof(f2560,plain,(
% 14.02/2.20    r2_hidden(sK0,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) | spl5_32),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f125,f989,f85])).
% 14.02/2.20  fof(f5093,plain,(
% 14.02/2.20    ~spl5_115 | spl5_3 | ~spl5_61),
% 14.02/2.20    inference(avatar_split_clause,[],[f2506,f2382,f182,f5091])).
% 14.02/2.20  fof(f2506,plain,(
% 14.02/2.20    k1_xboole_0 != k5_xboole_0(k1_tarski(sK1),k1_xboole_0) | (spl5_3 | ~spl5_61)),
% 14.02/2.20    inference(backward_demodulation,[],[f204,f2499])).
% 14.02/2.20  fof(f204,plain,(
% 14.02/2.20    k1_xboole_0 != k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | spl5_3),
% 14.02/2.20    inference(forward_demodulation,[],[f200,f94])).
% 14.02/2.20  fof(f200,plain,(
% 14.02/2.20    k1_xboole_0 != k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) | spl5_3),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f183,f119])).
% 14.02/2.20  fof(f119,plain,(
% 14.02/2.20    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(k1_tarski(X0),k3_xboole_0(k1_tarski(X0),X1)) | r2_hidden(X0,X1)) )),
% 14.02/2.20    inference(definition_unfolding,[],[f100,f73])).
% 14.02/2.20  fof(f100,plain,(
% 14.02/2.20    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) )),
% 14.02/2.20    inference(cnf_transformation,[],[f57])).
% 14.02/2.20  fof(f5077,plain,(
% 14.02/2.20    ~spl5_114 | spl5_4 | ~spl5_61),
% 14.02/2.20    inference(avatar_split_clause,[],[f2503,f2382,f186,f5075])).
% 14.02/2.20  fof(f2503,plain,(
% 14.02/2.20    k1_xboole_0 != k5_xboole_0(k1_tarski(sK0),k1_xboole_0) | (spl5_4 | ~spl5_61)),
% 14.02/2.20    inference(backward_demodulation,[],[f220,f2499])).
% 14.02/2.20  fof(f220,plain,(
% 14.02/2.20    k1_xboole_0 != k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | spl5_4),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f187,f119])).
% 14.02/2.20  fof(f5073,plain,(
% 14.02/2.20    spl5_113 | spl5_4),
% 14.02/2.20    inference(avatar_split_clause,[],[f227,f186,f5071])).
% 14.02/2.20  fof(f5071,plain,(
% 14.02/2.20    spl5_113 <=> r2_hidden(sK0,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_113])])).
% 14.02/2.20  fof(f227,plain,(
% 14.02/2.20    r2_hidden(sK0,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | spl5_4),
% 14.02/2.20    inference(forward_demodulation,[],[f215,f91])).
% 14.02/2.20  fof(f215,plain,(
% 14.02/2.20    r2_hidden(sK0,k5_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) | spl5_4),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f125,f187,f85])).
% 14.02/2.20  fof(f5069,plain,(
% 14.02/2.20    spl5_112 | spl5_16),
% 14.02/2.20    inference(avatar_split_clause,[],[f1113,f482,f5067])).
% 14.02/2.20  fof(f5067,plain,(
% 14.02/2.20    spl5_112 <=> r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k1_tarski(sK1)))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_112])])).
% 14.02/2.20  fof(f1113,plain,(
% 14.02/2.20    r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k1_tarski(sK1))) | spl5_16),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f125,f483,f85])).
% 14.02/2.20  fof(f5065,plain,(
% 14.02/2.20    spl5_111 | spl5_3),
% 14.02/2.20    inference(avatar_split_clause,[],[f195,f182,f5063])).
% 14.02/2.20  fof(f5063,plain,(
% 14.02/2.20    spl5_111 <=> r2_hidden(sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_111])])).
% 14.02/2.20  fof(f195,plain,(
% 14.02/2.20    r2_hidden(sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | spl5_3),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f125,f183,f85])).
% 14.02/2.20  fof(f5061,plain,(
% 14.02/2.20    ~spl5_110 | spl5_3),
% 14.02/2.20    inference(avatar_split_clause,[],[f192,f182,f5059])).
% 14.02/2.20  fof(f5059,plain,(
% 14.02/2.20    spl5_110 <=> r2_hidden(sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).
% 14.02/2.20  fof(f192,plain,(
% 14.02/2.20    ~r2_hidden(sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))) | spl5_3),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f183,f183,f82])).
% 14.02/2.20  fof(f5000,plain,(
% 14.02/2.20    spl5_109 | spl5_11),
% 14.02/2.20    inference(avatar_split_clause,[],[f4435,f257,f4998])).
% 14.02/2.20  fof(f4998,plain,(
% 14.02/2.20    spl5_109 <=> r2_hidden(sK0,k5_xboole_0(sK2,k1_tarski(sK0)))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_109])])).
% 14.02/2.20  fof(f4435,plain,(
% 14.02/2.20    r2_hidden(sK0,k5_xboole_0(sK2,k1_tarski(sK0))) | spl5_11),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f125,f258,f85])).
% 14.02/2.20  fof(f4726,plain,(
% 14.02/2.20    ~spl5_108 | spl5_87),
% 14.02/2.20    inference(avatar_split_clause,[],[f3735,f3711,f4724])).
% 14.02/2.20  fof(f4724,plain,(
% 14.02/2.20    spl5_108 <=> r2_hidden(k1_xboole_0,k1_tarski(k1_tarski(sK1)))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_108])])).
% 14.02/2.20  fof(f3711,plain,(
% 14.02/2.20    spl5_87 <=> k1_xboole_0 = k1_tarski(sK1)),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).
% 14.02/2.20  fof(f3735,plain,(
% 14.02/2.20    ~r2_hidden(k1_xboole_0,k1_tarski(k1_tarski(sK1))) | spl5_87),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f3712,f126])).
% 14.02/2.20  fof(f3712,plain,(
% 14.02/2.20    k1_xboole_0 != k1_tarski(sK1) | spl5_87),
% 14.02/2.20    inference(avatar_component_clause,[],[f3711])).
% 14.02/2.20  fof(f4709,plain,(
% 14.02/2.20    spl5_107 | ~spl5_19 | ~spl5_51),
% 14.02/2.20    inference(avatar_split_clause,[],[f4040,f2061,f527,f4707])).
% 14.02/2.20  fof(f4707,plain,(
% 14.02/2.20    spl5_107 <=> ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,X0)) | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),k1_tarski(sK0)) | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),X0))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_107])])).
% 14.02/2.20  fof(f2061,plain,(
% 14.02/2.20    spl5_51 <=> ! [X0] : (r2_hidden(sK3(k1_tarski(sK0),sK2,X0),X0) | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),k1_tarski(sK0)) | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X0)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 14.02/2.20  fof(f4040,plain,(
% 14.02/2.20    ( ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,X0)) | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),k1_tarski(sK0)) | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),X0)) ) | (~spl5_19 | ~spl5_51)),
% 14.02/2.20    inference(backward_demodulation,[],[f2062,f3992])).
% 14.02/2.20  fof(f3992,plain,(
% 14.02/2.20    k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK1)) | ~spl5_19),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f2032,f86])).
% 14.02/2.20  fof(f2062,plain,(
% 14.02/2.20    ( ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X0)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),k1_tarski(sK0)) | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),X0)) ) | ~spl5_51),
% 14.02/2.20    inference(avatar_component_clause,[],[f2061])).
% 14.02/2.20  fof(f4705,plain,(
% 14.02/2.20    ~spl5_106 | spl5_87),
% 14.02/2.20    inference(avatar_split_clause,[],[f3733,f3711,f4703])).
% 14.02/2.20  fof(f4703,plain,(
% 14.02/2.20    spl5_106 <=> r2_hidden(k1_tarski(sK1),k1_tarski(k1_xboole_0))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_106])])).
% 14.02/2.20  fof(f3733,plain,(
% 14.02/2.20    ~r2_hidden(k1_tarski(sK1),k1_tarski(k1_xboole_0)) | spl5_87),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f3712,f126])).
% 14.02/2.20  fof(f4688,plain,(
% 14.02/2.20    spl5_105 | ~spl5_19 | ~spl5_50),
% 14.02/2.20    inference(avatar_split_clause,[],[f4039,f2029,f527,f4686])).
% 14.02/2.20  fof(f4686,plain,(
% 14.02/2.20    spl5_105 <=> ! [X1] : (k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,X1)) | ~r2_hidden(sK3(k1_tarski(sK0),sK2,X1),sK2) | r2_hidden(sK3(k1_tarski(sK0),sK2,X1),X1))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_105])])).
% 14.02/2.20  fof(f2029,plain,(
% 14.02/2.20    spl5_50 <=> ! [X1] : (r2_hidden(sK3(k1_tarski(sK0),sK2,X1),X1) | ~r2_hidden(sK3(k1_tarski(sK0),sK2,X1),sK2) | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X1)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).
% 14.02/2.20  fof(f4039,plain,(
% 14.02/2.20    ( ! [X1] : (k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,X1)) | ~r2_hidden(sK3(k1_tarski(sK0),sK2,X1),sK2) | r2_hidden(sK3(k1_tarski(sK0),sK2,X1),X1)) ) | (~spl5_19 | ~spl5_50)),
% 14.02/2.20    inference(backward_demodulation,[],[f2030,f3992])).
% 14.02/2.20  fof(f2030,plain,(
% 14.02/2.20    ( ! [X1] : (k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X1)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | ~r2_hidden(sK3(k1_tarski(sK0),sK2,X1),sK2) | r2_hidden(sK3(k1_tarski(sK0),sK2,X1),X1)) ) | ~spl5_50),
% 14.02/2.20    inference(avatar_component_clause,[],[f2029])).
% 14.02/2.20  fof(f4684,plain,(
% 14.02/2.20    ~spl5_104 | spl5_84),
% 14.02/2.20    inference(avatar_split_clause,[],[f3688,f3664,f4682])).
% 14.02/2.20  fof(f4682,plain,(
% 14.02/2.20    spl5_104 <=> r2_hidden(k1_xboole_0,k1_tarski(k1_tarski(sK0)))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).
% 14.02/2.20  fof(f3664,plain,(
% 14.02/2.20    spl5_84 <=> k1_xboole_0 = k1_tarski(sK0)),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).
% 14.02/2.20  fof(f3688,plain,(
% 14.02/2.20    ~r2_hidden(k1_xboole_0,k1_tarski(k1_tarski(sK0))) | spl5_84),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f3665,f126])).
% 14.02/2.20  fof(f3665,plain,(
% 14.02/2.20    k1_xboole_0 != k1_tarski(sK0) | spl5_84),
% 14.02/2.20    inference(avatar_component_clause,[],[f3664])).
% 14.02/2.20  fof(f4649,plain,(
% 14.02/2.20    ~spl5_103 | spl5_2 | ~spl5_8 | ~spl5_10 | ~spl5_19),
% 14.02/2.20    inference(avatar_split_clause,[],[f4534,f527,f253,f242,f144,f4647])).
% 14.02/2.20  fof(f4647,plain,(
% 14.02/2.20    spl5_103 <=> r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2)))))))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_103])])).
% 14.02/2.20  fof(f4534,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))))))) | (spl5_2 | ~spl5_8 | ~spl5_10 | ~spl5_19)),
% 14.02/2.20    inference(backward_demodulation,[],[f4479,f4524])).
% 14.02/2.20  fof(f4479,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))))))) | (spl5_2 | ~spl5_10 | ~spl5_19)),
% 14.02/2.20    inference(backward_demodulation,[],[f4338,f4464])).
% 14.02/2.20  fof(f4464,plain,(
% 14.02/2.20    k1_tarski(sK0) = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))) | ~spl5_10),
% 14.02/2.20    inference(forward_demodulation,[],[f4463,f94])).
% 14.02/2.20  fof(f4463,plain,(
% 14.02/2.20    k1_tarski(sK0) = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2)) | ~spl5_10),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f587,f116])).
% 14.02/2.20  fof(f4338,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))))))) | (spl5_2 | ~spl5_19)),
% 14.02/2.20    inference(forward_demodulation,[],[f4337,f91])).
% 14.02/2.20  fof(f4337,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_xboole_0))))))) | (spl5_2 | ~spl5_19)),
% 14.02/2.20    inference(forward_demodulation,[],[f165,f3992])).
% 14.02/2.20  fof(f165,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))))) | spl5_2),
% 14.02/2.20    inference(forward_demodulation,[],[f164,f90])).
% 14.02/2.20  fof(f164,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))))) | spl5_2),
% 14.02/2.20    inference(forward_demodulation,[],[f147,f90])).
% 14.02/2.20  fof(f147,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))))) | spl5_2),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f145,f126])).
% 14.02/2.20  fof(f4645,plain,(
% 14.02/2.20    ~spl5_102 | spl5_84),
% 14.02/2.20    inference(avatar_split_clause,[],[f3686,f3664,f4643])).
% 14.02/2.20  fof(f4643,plain,(
% 14.02/2.20    spl5_102 <=> r2_hidden(k1_tarski(sK0),k1_tarski(k1_xboole_0))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).
% 14.02/2.20  fof(f3686,plain,(
% 14.02/2.20    ~r2_hidden(k1_tarski(sK0),k1_tarski(k1_xboole_0)) | spl5_84),
% 14.02/2.20    inference(unit_resulting_resolution,[],[f3665,f126])).
% 14.02/2.20  fof(f4611,plain,(
% 14.02/2.20    ~spl5_101 | ~spl5_8 | ~spl5_10 | spl5_14 | ~spl5_19),
% 14.02/2.20    inference(avatar_split_clause,[],[f4532,f527,f341,f253,f242,f4609])).
% 14.02/2.20  fof(f4609,plain,(
% 14.02/2.20    spl5_101 <=> r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))))))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_101])])).
% 14.02/2.20  fof(f341,plain,(
% 14.02/2.20    spl5_14 <=> r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))))))))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 14.02/2.20  fof(f4532,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))))) | (~spl5_8 | ~spl5_10 | spl5_14 | ~spl5_19)),
% 14.02/2.20    inference(backward_demodulation,[],[f4474,f4524])).
% 14.02/2.20  fof(f4474,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))))) | (~spl5_10 | spl5_14 | ~spl5_19)),
% 14.02/2.20    inference(backward_demodulation,[],[f4326,f4464])).
% 14.02/2.20  fof(f4326,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))))))) | (spl5_14 | ~spl5_19)),
% 14.02/2.20    inference(forward_demodulation,[],[f4325,f91])).
% 14.02/2.20  fof(f4325,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_xboole_0))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))))))) | (spl5_14 | ~spl5_19)),
% 14.02/2.20    inference(forward_demodulation,[],[f342,f3992])).
% 14.02/2.20  fof(f342,plain,(
% 14.02/2.20    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))))))) | spl5_14),
% 14.02/2.20    inference(avatar_component_clause,[],[f341])).
% 14.02/2.20  fof(f4561,plain,(
% 14.02/2.20    ~spl5_100 | ~spl5_8 | ~spl5_10 | spl5_13 | ~spl5_19),
% 14.02/2.20    inference(avatar_split_clause,[],[f4533,f527,f323,f253,f242,f4559])).
% 14.02/2.20  fof(f323,plain,(
% 14.02/2.20    spl5_13 <=> k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))))))),
% 14.02/2.20    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 14.02/2.20  fof(f4533,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))) | (~spl5_8 | ~spl5_10 | spl5_13 | ~spl5_19)),
% 14.02/2.20    inference(backward_demodulation,[],[f4475,f4524])).
% 14.02/2.20  fof(f4475,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))) | (~spl5_10 | spl5_13 | ~spl5_19)),
% 14.02/2.20    inference(backward_demodulation,[],[f4328,f4464])).
% 14.02/2.20  fof(f4328,plain,(
% 14.02/2.20    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))))) | (spl5_13 | ~spl5_19)),
% 14.02/2.20    inference(forward_demodulation,[],[f4327,f91])).
% 14.02/2.21  fof(f4327,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_xboole_0))))) | (spl5_13 | ~spl5_19)),
% 14.02/2.21    inference(forward_demodulation,[],[f324,f3992])).
% 14.02/2.21  fof(f324,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))))) | spl5_13),
% 14.02/2.21    inference(avatar_component_clause,[],[f323])).
% 14.02/2.21  fof(f4557,plain,(
% 14.02/2.21    ~spl5_99 | spl5_11),
% 14.02/2.21    inference(avatar_split_clause,[],[f4432,f257,f4555])).
% 14.02/2.21  fof(f4432,plain,(
% 14.02/2.21    ~r2_hidden(sK0,k5_xboole_0(sK2,sK2)) | spl5_11),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f258,f258,f82])).
% 14.02/2.21  fof(f4543,plain,(
% 14.02/2.21    ~spl5_97 | ~spl5_98 | spl5_15 | ~spl5_19),
% 14.02/2.21    inference(avatar_split_clause,[],[f4227,f527,f443,f4541,f4538])).
% 14.02/2.21  fof(f4538,plain,(
% 14.02/2.21    spl5_97 <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).
% 14.02/2.21  fof(f443,plain,(
% 14.02/2.21    spl5_15 <=> k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 14.02/2.21  fof(f4227,plain,(
% 14.02/2.21    ~r1_tarski(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2)) | k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))) | (spl5_15 | ~spl5_19)),
% 14.02/2.21    inference(forward_demodulation,[],[f4226,f91])).
% 14.02/2.21  fof(f4226,plain,(
% 14.02/2.21    ~r1_tarski(k1_tarski(sK0),k5_xboole_0(sK2,k1_xboole_0)) | k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))) | (spl5_15 | ~spl5_19)),
% 14.02/2.21    inference(forward_demodulation,[],[f4225,f3992])).
% 14.02/2.21  fof(f4225,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))) | ~r1_tarski(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))) | (spl5_15 | ~spl5_19)),
% 14.02/2.21    inference(forward_demodulation,[],[f3764,f3992])).
% 14.02/2.21  fof(f3764,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | ~r1_tarski(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))) | spl5_15),
% 14.02/2.21    inference(superposition,[],[f444,f93])).
% 14.02/2.21  fof(f444,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | spl5_15),
% 14.02/2.21    inference(avatar_component_clause,[],[f443])).
% 14.02/2.21  fof(f4527,plain,(
% 14.02/2.21    ~spl5_8 | spl5_88),
% 14.02/2.21    inference(avatar_contradiction_clause,[],[f4526])).
% 14.02/2.21  fof(f4526,plain,(
% 14.02/2.21    $false | (~spl5_8 | spl5_88)),
% 14.02/2.21    inference(subsumption_resolution,[],[f4524,f3731])).
% 14.02/2.21  fof(f3731,plain,(
% 14.02/2.21    k1_xboole_0 != k3_xboole_0(sK2,k1_tarski(sK0)) | spl5_88),
% 14.02/2.21    inference(avatar_component_clause,[],[f3730])).
% 14.02/2.21  fof(f3730,plain,(
% 14.02/2.21    spl5_88 <=> k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK0))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).
% 14.02/2.21  fof(f4512,plain,(
% 14.02/2.21    ~spl5_96 | spl5_9 | ~spl5_10 | spl5_18 | ~spl5_19),
% 14.02/2.21    inference(avatar_split_clause,[],[f4473,f527,f523,f253,f245,f4510])).
% 14.02/2.21  fof(f4510,plain,(
% 14.02/2.21    spl5_96 <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))))))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).
% 14.02/2.21  fof(f245,plain,(
% 14.02/2.21    spl5_9 <=> k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))))))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 14.02/2.21  fof(f4473,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) | (spl5_9 | ~spl5_10 | spl5_18 | ~spl5_19)),
% 14.02/2.21    inference(backward_demodulation,[],[f4218,f4464])).
% 14.02/2.21  fof(f4218,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) | (spl5_9 | spl5_18 | ~spl5_19)),
% 14.02/2.21    inference(forward_demodulation,[],[f3843,f3992])).
% 14.02/2.21  fof(f3843,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) != k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) | (spl5_9 | spl5_18)),
% 14.02/2.21    inference(forward_demodulation,[],[f3812,f94])).
% 14.02/2.21  fof(f3812,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) != k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2)))) | (spl5_9 | spl5_18)),
% 14.02/2.21    inference(backward_demodulation,[],[f246,f3806])).
% 14.02/2.21  fof(f3806,plain,(
% 14.02/2.21    sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))) | spl5_18),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f1325,f113])).
% 14.02/2.21  fof(f246,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) | spl5_9),
% 14.02/2.21    inference(avatar_component_clause,[],[f245])).
% 14.02/2.21  fof(f4506,plain,(
% 14.02/2.21    spl5_90 | spl5_94),
% 14.02/2.21    inference(avatar_contradiction_clause,[],[f4505])).
% 14.02/2.21  fof(f4505,plain,(
% 14.02/2.21    $false | (spl5_90 | spl5_94)),
% 14.02/2.21    inference(subsumption_resolution,[],[f4504,f91])).
% 14.02/2.21  fof(f4504,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k1_xboole_0) != k5_xboole_0(k1_xboole_0,sK2) | (spl5_90 | spl5_94)),
% 14.02/2.21    inference(forward_demodulation,[],[f4503,f102])).
% 14.02/2.21  fof(f4503,plain,(
% 14.02/2.21    k5_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0)) | (spl5_90 | spl5_94)),
% 14.02/2.21    inference(subsumption_resolution,[],[f4501,f4163])).
% 14.02/2.21  fof(f4163,plain,(
% 14.02/2.21    r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | spl5_90),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f4141,f81])).
% 14.02/2.21  fof(f4501,plain,(
% 14.02/2.21    k5_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0)) | ~r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | spl5_94),
% 14.02/2.21    inference(superposition,[],[f4491,f86])).
% 14.02/2.21  fof(f4491,plain,(
% 14.02/2.21    k5_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | spl5_94),
% 14.02/2.21    inference(avatar_component_clause,[],[f4490])).
% 14.02/2.21  fof(f4490,plain,(
% 14.02/2.21    spl5_94 <=> k5_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).
% 14.02/2.21  fof(f4495,plain,(
% 14.02/2.21    ~spl5_94 | ~spl5_95 | spl5_15 | ~spl5_19),
% 14.02/2.21    inference(avatar_split_clause,[],[f4385,f527,f443,f4493,f4490])).
% 14.02/2.21  fof(f4385,plain,(
% 14.02/2.21    ~r2_hidden(sK0,k5_xboole_0(k1_xboole_0,sK2)) | k5_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | (spl5_15 | ~spl5_19)),
% 14.02/2.21    inference(forward_demodulation,[],[f4384,f91])).
% 14.02/2.21  fof(f4384,plain,(
% 14.02/2.21    ~r2_hidden(sK0,k5_xboole_0(sK2,k1_xboole_0)) | k5_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | (spl5_15 | ~spl5_19)),
% 14.02/2.21    inference(forward_demodulation,[],[f4379,f3992])).
% 14.02/2.21  fof(f4379,plain,(
% 14.02/2.21    k5_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | ~r2_hidden(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))) | (spl5_15 | ~spl5_19)),
% 14.02/2.21    inference(forward_demodulation,[],[f4378,f91])).
% 14.02/2.21  fof(f4378,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k1_xboole_0) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | ~r2_hidden(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))) | (spl5_15 | ~spl5_19)),
% 14.02/2.21    inference(forward_demodulation,[],[f4377,f102])).
% 14.02/2.21  fof(f4377,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0)) | ~r2_hidden(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))) | (spl5_15 | ~spl5_19)),
% 14.02/2.21    inference(forward_demodulation,[],[f535,f3992])).
% 14.02/2.21  fof(f535,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | ~r2_hidden(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))) | spl5_15),
% 14.02/2.21    inference(forward_demodulation,[],[f460,f91])).
% 14.02/2.21  fof(f460,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k1_xboole_0)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | ~r2_hidden(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))) | spl5_15),
% 14.02/2.21    inference(superposition,[],[f444,f118])).
% 14.02/2.21  fof(f4453,plain,(
% 14.02/2.21    ~spl5_93 | spl5_18 | ~spl5_19 | spl5_25),
% 14.02/2.21    inference(avatar_split_clause,[],[f4214,f632,f527,f523,f4451])).
% 14.02/2.21  fof(f4214,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) | (spl5_18 | ~spl5_19 | spl5_25)),
% 14.02/2.21    inference(forward_demodulation,[],[f3865,f3992])).
% 14.02/2.21  fof(f3865,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | (spl5_18 | spl5_25)),
% 14.02/2.21    inference(forward_demodulation,[],[f3819,f94])).
% 14.02/2.21  fof(f3819,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | (spl5_18 | spl5_25)),
% 14.02/2.21    inference(backward_demodulation,[],[f633,f3806])).
% 14.02/2.21  fof(f4414,plain,(
% 14.02/2.21    ~spl5_92 | spl5_15 | spl5_18 | ~spl5_19),
% 14.02/2.21    inference(avatar_split_clause,[],[f4217,f527,f523,f443,f4412])).
% 14.02/2.21  fof(f4217,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) | (spl5_15 | spl5_18 | ~spl5_19)),
% 14.02/2.21    inference(forward_demodulation,[],[f3847,f3992])).
% 14.02/2.21  fof(f3847,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | (spl5_15 | spl5_18)),
% 14.02/2.21    inference(forward_demodulation,[],[f3813,f94])).
% 14.02/2.21  fof(f3813,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | (spl5_15 | spl5_18)),
% 14.02/2.21    inference(backward_demodulation,[],[f444,f3806])).
% 14.02/2.21  fof(f4383,plain,(
% 14.02/2.21    ~spl5_8 | spl5_18 | spl5_39),
% 14.02/2.21    inference(avatar_contradiction_clause,[],[f4382])).
% 14.02/2.21  fof(f4382,plain,(
% 14.02/2.21    $false | (~spl5_8 | spl5_18 | spl5_39)),
% 14.02/2.21    inference(subsumption_resolution,[],[f932,f3839])).
% 14.02/2.21  fof(f3839,plain,(
% 14.02/2.21    ~r1_xboole_0(sK2,k1_tarski(sK0)) | (spl5_18 | spl5_39)),
% 14.02/2.21    inference(backward_demodulation,[],[f1311,f3806])).
% 14.02/2.21  fof(f1311,plain,(
% 14.02/2.21    ~r1_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),k1_tarski(sK0)) | spl5_39),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f1300,f88])).
% 14.02/2.21  fof(f88,plain,(
% 14.02/2.21    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 14.02/2.21    inference(cnf_transformation,[],[f35])).
% 14.02/2.21  fof(f35,plain,(
% 14.02/2.21    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 14.02/2.21    inference(ennf_transformation,[],[f5])).
% 14.02/2.21  fof(f5,axiom,(
% 14.02/2.21    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 14.02/2.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 14.02/2.21  fof(f1300,plain,(
% 14.02/2.21    ~r1_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))) | spl5_39),
% 14.02/2.21    inference(avatar_component_clause,[],[f1299])).
% 14.02/2.21  fof(f1299,plain,(
% 14.02/2.21    spl5_39 <=> r1_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 14.02/2.21  fof(f4381,plain,(
% 14.02/2.21    ~spl5_10 | spl5_18 | spl5_39),
% 14.02/2.21    inference(avatar_contradiction_clause,[],[f4380])).
% 14.02/2.21  fof(f4380,plain,(
% 14.02/2.21    $false | (~spl5_10 | spl5_18 | spl5_39)),
% 14.02/2.21    inference(subsumption_resolution,[],[f587,f3838])).
% 14.02/2.21  fof(f3838,plain,(
% 14.02/2.21    ~r1_xboole_0(k1_tarski(sK0),sK2) | (spl5_18 | spl5_39)),
% 14.02/2.21    inference(backward_demodulation,[],[f1300,f3806])).
% 14.02/2.21  fof(f4205,plain,(
% 14.02/2.21    spl5_17 | ~spl5_19 | spl5_90),
% 14.02/2.21    inference(avatar_contradiction_clause,[],[f4204])).
% 14.02/2.21  fof(f4204,plain,(
% 14.02/2.21    $false | (spl5_17 | ~spl5_19 | spl5_90)),
% 14.02/2.21    inference(subsumption_resolution,[],[f4163,f4066])).
% 14.02/2.21  fof(f4066,plain,(
% 14.02/2.21    ~r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | (spl5_17 | ~spl5_19)),
% 14.02/2.21    inference(subsumption_resolution,[],[f4065,f91])).
% 14.02/2.21  fof(f4065,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k1_xboole_0) != k5_xboole_0(k1_xboole_0,sK2) | ~r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | (spl5_17 | ~spl5_19)),
% 14.02/2.21    inference(forward_demodulation,[],[f4001,f102])).
% 14.02/2.21  fof(f4001,plain,(
% 14.02/2.21    k5_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0)) | ~r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | (spl5_17 | ~spl5_19)),
% 14.02/2.21    inference(backward_demodulation,[],[f497,f3992])).
% 14.02/2.21  fof(f497,plain,(
% 14.02/2.21    k5_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) | ~r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | spl5_17),
% 14.02/2.21    inference(forward_demodulation,[],[f496,f91])).
% 14.02/2.21  fof(f496,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k1_xboole_0) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) | ~r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | spl5_17),
% 14.02/2.21    inference(forward_demodulation,[],[f494,f102])).
% 14.02/2.21  fof(f494,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0)) | ~r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | spl5_17),
% 14.02/2.21    inference(superposition,[],[f487,f86])).
% 14.02/2.21  fof(f487,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | spl5_17),
% 14.02/2.21    inference(avatar_component_clause,[],[f486])).
% 14.02/2.21  fof(f486,plain,(
% 14.02/2.21    spl5_17 <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 14.02/2.21  fof(f4146,plain,(
% 14.02/2.21    spl5_91 | ~spl5_19 | ~spl5_49),
% 14.02/2.21    inference(avatar_split_clause,[],[f4038,f1992,f527,f4144])).
% 14.02/2.21  fof(f4144,plain,(
% 14.02/2.21    spl5_91 <=> ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,X0)) | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),k1_tarski(sK0)) | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),X0))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).
% 14.02/2.21  fof(f1992,plain,(
% 14.02/2.21    spl5_49 <=> ! [X0] : (r2_hidden(sK3(k1_tarski(sK0),sK2,X0),X0) | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),k1_tarski(sK0)) | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X0)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).
% 14.02/2.21  fof(f4038,plain,(
% 14.02/2.21    ( ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,X0)) | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),k1_tarski(sK0)) | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),X0)) ) | (~spl5_19 | ~spl5_49)),
% 14.02/2.21    inference(backward_demodulation,[],[f1993,f3992])).
% 14.02/2.21  fof(f1993,plain,(
% 14.02/2.21    ( ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X0)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),k1_tarski(sK0)) | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),X0)) ) | ~spl5_49),
% 14.02/2.21    inference(avatar_component_clause,[],[f1992])).
% 14.02/2.21  fof(f4142,plain,(
% 14.02/2.21    ~spl5_90 | spl5_71),
% 14.02/2.21    inference(avatar_split_clause,[],[f3739,f2628,f4140])).
% 14.02/2.21  fof(f3739,plain,(
% 14.02/2.21    ~r2_hidden(sK1,k5_xboole_0(k1_xboole_0,sK2)) | spl5_71),
% 14.02/2.21    inference(resolution,[],[f2629,f96])).
% 14.02/2.21  fof(f2629,plain,(
% 14.02/2.21    ~r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | spl5_71),
% 14.02/2.21    inference(avatar_component_clause,[],[f2628])).
% 14.02/2.21  fof(f4124,plain,(
% 14.02/2.21    spl5_89 | ~spl5_19 | ~spl5_47),
% 14.02/2.21    inference(avatar_split_clause,[],[f4037,f1957,f527,f4122])).
% 14.02/2.21  fof(f4122,plain,(
% 14.02/2.21    spl5_89 <=> ! [X1] : (k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,X1)) | ~r2_hidden(sK3(k1_tarski(sK0),sK2,X1),sK2) | r2_hidden(sK3(k1_tarski(sK0),sK2,X1),X1))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_89])])).
% 14.02/2.21  fof(f1957,plain,(
% 14.02/2.21    spl5_47 <=> ! [X1] : (r2_hidden(sK3(k1_tarski(sK0),sK2,X1),X1) | ~r2_hidden(sK3(k1_tarski(sK0),sK2,X1),sK2) | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X1)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).
% 14.02/2.21  fof(f4037,plain,(
% 14.02/2.21    ( ! [X1] : (k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,X1)) | ~r2_hidden(sK3(k1_tarski(sK0),sK2,X1),sK2) | r2_hidden(sK3(k1_tarski(sK0),sK2,X1),X1)) ) | (~spl5_19 | ~spl5_47)),
% 14.02/2.21    inference(backward_demodulation,[],[f1958,f3992])).
% 14.02/2.21  fof(f1958,plain,(
% 14.02/2.21    ( ! [X1] : (k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X1)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | ~r2_hidden(sK3(k1_tarski(sK0),sK2,X1),sK2) | r2_hidden(sK3(k1_tarski(sK0),sK2,X1),X1)) ) | ~spl5_47),
% 14.02/2.21    inference(avatar_component_clause,[],[f1957])).
% 14.02/2.21  fof(f3743,plain,(
% 14.02/2.21    spl5_16 | ~spl5_18 | spl5_71),
% 14.02/2.21    inference(avatar_contradiction_clause,[],[f3742])).
% 14.02/2.21  fof(f3742,plain,(
% 14.02/2.21    $false | (spl5_16 | ~spl5_18 | spl5_71)),
% 14.02/2.21    inference(subsumption_resolution,[],[f3739,f2759])).
% 14.02/2.21  fof(f2759,plain,(
% 14.02/2.21    r2_hidden(sK1,k5_xboole_0(k1_xboole_0,sK2)) | (spl5_16 | ~spl5_18)),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f483,f524,f85])).
% 14.02/2.21  fof(f3741,plain,(
% 14.02/2.21    spl5_16 | ~spl5_18 | spl5_71),
% 14.02/2.21    inference(avatar_contradiction_clause,[],[f3740])).
% 14.02/2.21  fof(f3740,plain,(
% 14.02/2.21    $false | (spl5_16 | ~spl5_18 | spl5_71)),
% 14.02/2.21    inference(subsumption_resolution,[],[f3738,f2759])).
% 14.02/2.21  fof(f3738,plain,(
% 14.02/2.21    ~r2_hidden(sK1,k5_xboole_0(k1_xboole_0,sK2)) | spl5_71),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f2629,f96])).
% 14.02/2.21  fof(f3732,plain,(
% 14.02/2.21    ~spl5_88 | spl5_8),
% 14.02/2.21    inference(avatar_split_clause,[],[f2024,f242,f3730])).
% 14.02/2.21  fof(f2024,plain,(
% 14.02/2.21    k1_xboole_0 != k3_xboole_0(sK2,k1_tarski(sK0)) | spl5_8),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f243,f87])).
% 14.02/2.21  fof(f243,plain,(
% 14.02/2.21    ~r1_xboole_0(sK2,k1_tarski(sK0)) | spl5_8),
% 14.02/2.21    inference(avatar_component_clause,[],[f242])).
% 14.02/2.21  fof(f3713,plain,(
% 14.02/2.21    ~spl5_87 | ~spl5_18 | spl5_27),
% 14.02/2.21    inference(avatar_split_clause,[],[f3378,f676,f523,f3711])).
% 14.02/2.21  fof(f676,plain,(
% 14.02/2.21    spl5_27 <=> r1_xboole_0(k1_tarski(sK1),sK2)),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 14.02/2.21  fof(f3378,plain,(
% 14.02/2.21    k1_xboole_0 != k1_tarski(sK1) | (~spl5_18 | spl5_27)),
% 14.02/2.21    inference(forward_demodulation,[],[f3377,f3209])).
% 14.02/2.21  fof(f3209,plain,(
% 14.02/2.21    k1_xboole_0 = k5_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) | ~spl5_18),
% 14.02/2.21    inference(forward_demodulation,[],[f2776,f2747])).
% 14.02/2.21  fof(f2747,plain,(
% 14.02/2.21    k1_tarski(sK1) = k3_xboole_0(sK2,k1_tarski(sK1)) | ~spl5_18),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f524,f80])).
% 14.02/2.21  fof(f2776,plain,(
% 14.02/2.21    k1_xboole_0 = k5_xboole_0(k1_tarski(sK1),k3_xboole_0(sK2,k1_tarski(sK1))) | ~spl5_18),
% 14.02/2.21    inference(forward_demodulation,[],[f2767,f94])).
% 14.02/2.21  fof(f2767,plain,(
% 14.02/2.21    k1_xboole_0 = k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),sK2)) | ~spl5_18),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f524,f118])).
% 14.02/2.21  fof(f3377,plain,(
% 14.02/2.21    k1_tarski(sK1) != k5_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) | (~spl5_18 | spl5_27)),
% 14.02/2.21    inference(forward_demodulation,[],[f3376,f2747])).
% 14.02/2.21  fof(f3376,plain,(
% 14.02/2.21    k1_tarski(sK1) != k5_xboole_0(k1_tarski(sK1),k3_xboole_0(sK2,k1_tarski(sK1))) | spl5_27),
% 14.02/2.21    inference(forward_demodulation,[],[f3373,f94])).
% 14.02/2.21  fof(f3373,plain,(
% 14.02/2.21    k1_tarski(sK1) != k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),sK2)) | spl5_27),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f677,f115])).
% 14.02/2.21  fof(f115,plain,(
% 14.02/2.21    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 | r1_xboole_0(X0,X1)) )),
% 14.02/2.21    inference(definition_unfolding,[],[f72,f73])).
% 14.02/2.21  fof(f72,plain,(
% 14.02/2.21    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 14.02/2.21    inference(cnf_transformation,[],[f47])).
% 14.02/2.21  fof(f677,plain,(
% 14.02/2.21    ~r1_xboole_0(k1_tarski(sK1),sK2) | spl5_27),
% 14.02/2.21    inference(avatar_component_clause,[],[f676])).
% 14.02/2.21  fof(f3709,plain,(
% 14.02/2.21    spl5_86 | ~spl5_18 | spl5_25),
% 14.02/2.21    inference(avatar_split_clause,[],[f3303,f632,f523,f3707])).
% 14.02/2.21  fof(f3707,plain,(
% 14.02/2.21    spl5_86 <=> ! [X2] : (k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X2)))) | r2_hidden(sK3(sK2,k1_tarski(sK1),X2),k1_tarski(sK1)) | ~r2_hidden(sK3(sK2,k1_tarski(sK1),X2),sK2) | ~r2_hidden(sK3(sK2,k1_tarski(sK1),X2),X2))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).
% 14.02/2.21  fof(f3303,plain,(
% 14.02/2.21    ( ! [X2] : (k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X2)))) | r2_hidden(sK3(sK2,k1_tarski(sK1),X2),k1_tarski(sK1)) | ~r2_hidden(sK3(sK2,k1_tarski(sK1),X2),sK2) | ~r2_hidden(sK3(sK2,k1_tarski(sK1),X2),X2)) ) | (~spl5_18 | spl5_25)),
% 14.02/2.21    inference(forward_demodulation,[],[f646,f2747])).
% 14.02/2.21  fof(f646,plain,(
% 14.02/2.21    ( ! [X2] : (k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | r2_hidden(sK3(sK2,k1_tarski(sK1),X2),k1_tarski(sK1)) | ~r2_hidden(sK3(sK2,k1_tarski(sK1),X2),sK2) | ~r2_hidden(sK3(sK2,k1_tarski(sK1),X2),X2)) ) | spl5_25),
% 14.02/2.21    inference(superposition,[],[f633,f107])).
% 14.02/2.21  fof(f107,plain,(
% 14.02/2.21    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 14.02/2.21    inference(definition_unfolding,[],[f68,f73])).
% 14.02/2.21  fof(f68,plain,(
% 14.02/2.21    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 14.02/2.21    inference(cnf_transformation,[],[f45])).
% 14.02/2.21  fof(f3685,plain,(
% 14.02/2.21    spl5_85 | spl5_15 | ~spl5_18),
% 14.02/2.21    inference(avatar_split_clause,[],[f3312,f523,f443,f3683])).
% 14.02/2.21  fof(f3683,plain,(
% 14.02/2.21    spl5_85 <=> ! [X2] : (k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X2)))) | r2_hidden(sK3(sK2,k1_tarski(sK1),X2),k1_tarski(sK1)) | ~r2_hidden(sK3(sK2,k1_tarski(sK1),X2),sK2) | ~r2_hidden(sK3(sK2,k1_tarski(sK1),X2),X2))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).
% 14.02/2.21  fof(f3312,plain,(
% 14.02/2.21    ( ! [X2] : (k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X2)))) | r2_hidden(sK3(sK2,k1_tarski(sK1),X2),k1_tarski(sK1)) | ~r2_hidden(sK3(sK2,k1_tarski(sK1),X2),sK2) | ~r2_hidden(sK3(sK2,k1_tarski(sK1),X2),X2)) ) | (spl5_15 | ~spl5_18)),
% 14.02/2.21    inference(forward_demodulation,[],[f457,f2747])).
% 14.02/2.21  fof(f457,plain,(
% 14.02/2.21    ( ! [X2] : (k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | r2_hidden(sK3(sK2,k1_tarski(sK1),X2),k1_tarski(sK1)) | ~r2_hidden(sK3(sK2,k1_tarski(sK1),X2),sK2) | ~r2_hidden(sK3(sK2,k1_tarski(sK1),X2),X2)) ) | spl5_15),
% 14.02/2.21    inference(superposition,[],[f444,f107])).
% 14.02/2.21  fof(f3666,plain,(
% 14.02/2.21    ~spl5_84 | spl5_10 | ~spl5_11),
% 14.02/2.21    inference(avatar_split_clause,[],[f1293,f257,f253,f3664])).
% 14.02/2.21  fof(f1293,plain,(
% 14.02/2.21    k1_xboole_0 != k1_tarski(sK0) | (spl5_10 | ~spl5_11)),
% 14.02/2.21    inference(forward_demodulation,[],[f1292,f1215])).
% 14.02/2.21  fof(f1215,plain,(
% 14.02/2.21    k1_xboole_0 = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) | ~spl5_11),
% 14.02/2.21    inference(backward_demodulation,[],[f1164,f1143])).
% 14.02/2.21  fof(f1143,plain,(
% 14.02/2.21    k1_tarski(sK0) = k3_xboole_0(sK2,k1_tarski(sK0)) | ~spl5_11),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f326,f80])).
% 14.02/2.21  fof(f1164,plain,(
% 14.02/2.21    k1_xboole_0 = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))) | ~spl5_11),
% 14.02/2.21    inference(forward_demodulation,[],[f1157,f94])).
% 14.02/2.21  fof(f1157,plain,(
% 14.02/2.21    k1_xboole_0 = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2)) | ~spl5_11),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f326,f118])).
% 14.02/2.21  fof(f1292,plain,(
% 14.02/2.21    k1_tarski(sK0) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) | (spl5_10 | ~spl5_11)),
% 14.02/2.21    inference(forward_demodulation,[],[f1291,f1143])).
% 14.02/2.21  fof(f1291,plain,(
% 14.02/2.21    k1_tarski(sK0) != k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))) | spl5_10),
% 14.02/2.21    inference(forward_demodulation,[],[f1288,f94])).
% 14.02/2.21  fof(f1288,plain,(
% 14.02/2.21    k1_tarski(sK0) != k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2)) | spl5_10),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f254,f115])).
% 14.02/2.21  fof(f254,plain,(
% 14.02/2.21    ~r1_xboole_0(k1_tarski(sK0),sK2) | spl5_10),
% 14.02/2.21    inference(avatar_component_clause,[],[f253])).
% 14.02/2.21  fof(f3662,plain,(
% 14.02/2.21    spl5_83 | ~spl5_18 | spl5_25),
% 14.02/2.21    inference(avatar_split_clause,[],[f3304,f632,f523,f3660])).
% 14.02/2.21  fof(f3660,plain,(
% 14.02/2.21    spl5_83 <=> ! [X1] : (k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1)))) | ~r2_hidden(sK3(sK2,k1_tarski(sK1),X1),k1_tarski(sK1)) | r2_hidden(sK3(sK2,k1_tarski(sK1),X1),X1))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).
% 14.02/2.21  fof(f3304,plain,(
% 14.02/2.21    ( ! [X1] : (k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1)))) | ~r2_hidden(sK3(sK2,k1_tarski(sK1),X1),k1_tarski(sK1)) | r2_hidden(sK3(sK2,k1_tarski(sK1),X1),X1)) ) | (~spl5_18 | spl5_25)),
% 14.02/2.21    inference(forward_demodulation,[],[f645,f2747])).
% 14.02/2.21  fof(f645,plain,(
% 14.02/2.21    ( ! [X1] : (k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | ~r2_hidden(sK3(sK2,k1_tarski(sK1),X1),k1_tarski(sK1)) | r2_hidden(sK3(sK2,k1_tarski(sK1),X1),X1)) ) | spl5_25),
% 14.02/2.21    inference(superposition,[],[f633,f108])).
% 14.02/2.21  fof(f108,plain,(
% 14.02/2.21    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 14.02/2.21    inference(definition_unfolding,[],[f67,f73])).
% 14.02/2.21  fof(f67,plain,(
% 14.02/2.21    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 14.02/2.21    inference(cnf_transformation,[],[f45])).
% 14.02/2.21  fof(f3641,plain,(
% 14.02/2.21    spl5_82 | ~spl5_18 | spl5_25),
% 14.02/2.21    inference(avatar_split_clause,[],[f3305,f632,f523,f3639])).
% 14.02/2.21  fof(f3639,plain,(
% 14.02/2.21    spl5_82 <=> ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0)))) | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),sK2) | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),X0))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).
% 14.02/2.21  fof(f3305,plain,(
% 14.02/2.21    ( ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0)))) | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),sK2) | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),X0)) ) | (~spl5_18 | spl5_25)),
% 14.02/2.21    inference(forward_demodulation,[],[f644,f2747])).
% 14.02/2.21  fof(f644,plain,(
% 14.02/2.21    ( ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),sK2) | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),X0)) ) | spl5_25),
% 14.02/2.21    inference(superposition,[],[f633,f109])).
% 14.02/2.21  fof(f109,plain,(
% 14.02/2.21    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 14.02/2.21    inference(definition_unfolding,[],[f66,f73])).
% 14.02/2.21  fof(f66,plain,(
% 14.02/2.21    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 14.02/2.21    inference(cnf_transformation,[],[f45])).
% 14.02/2.21  fof(f3618,plain,(
% 14.02/2.21    spl5_81 | spl5_15 | ~spl5_18),
% 14.02/2.21    inference(avatar_split_clause,[],[f3313,f523,f443,f3616])).
% 14.02/2.21  fof(f3616,plain,(
% 14.02/2.21    spl5_81 <=> ! [X1] : (k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1)))) | ~r2_hidden(sK3(sK2,k1_tarski(sK1),X1),k1_tarski(sK1)) | r2_hidden(sK3(sK2,k1_tarski(sK1),X1),X1))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).
% 14.02/2.21  fof(f3313,plain,(
% 14.02/2.21    ( ! [X1] : (k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1)))) | ~r2_hidden(sK3(sK2,k1_tarski(sK1),X1),k1_tarski(sK1)) | r2_hidden(sK3(sK2,k1_tarski(sK1),X1),X1)) ) | (spl5_15 | ~spl5_18)),
% 14.02/2.21    inference(forward_demodulation,[],[f456,f2747])).
% 14.02/2.21  fof(f456,plain,(
% 14.02/2.21    ( ! [X1] : (k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | ~r2_hidden(sK3(sK2,k1_tarski(sK1),X1),k1_tarski(sK1)) | r2_hidden(sK3(sK2,k1_tarski(sK1),X1),X1)) ) | spl5_15),
% 14.02/2.21    inference(superposition,[],[f444,f108])).
% 14.02/2.21  fof(f3597,plain,(
% 14.02/2.21    spl5_80 | ~spl5_18 | ~spl5_52),
% 14.02/2.21    inference(avatar_split_clause,[],[f3267,f2093,f523,f3595])).
% 14.02/2.21  fof(f3595,plain,(
% 14.02/2.21    spl5_80 <=> ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0)))) | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),sK2) | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),X0))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).
% 14.02/2.21  fof(f2093,plain,(
% 14.02/2.21    spl5_52 <=> ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),sK2) | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),X0))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 14.02/2.21  fof(f3267,plain,(
% 14.02/2.21    ( ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0)))) | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),sK2) | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),X0)) ) | (~spl5_18 | ~spl5_52)),
% 14.02/2.21    inference(forward_demodulation,[],[f2094,f2747])).
% 14.02/2.21  fof(f2094,plain,(
% 14.02/2.21    ( ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),sK2) | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),X0)) ) | ~spl5_52),
% 14.02/2.21    inference(avatar_component_clause,[],[f2093])).
% 14.02/2.21  fof(f3572,plain,(
% 14.02/2.21    ~spl5_42 | ~spl5_79 | spl5_2 | ~spl5_11 | ~spl5_18),
% 14.02/2.21    inference(avatar_split_clause,[],[f3242,f523,f257,f144,f3570,f1480])).
% 14.02/2.21  fof(f1480,plain,(
% 14.02/2.21    spl5_42 <=> r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 14.02/2.21  fof(f3570,plain,(
% 14.02/2.21    spl5_79 <=> k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_tarski(sK1)))))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).
% 14.02/2.21  fof(f3242,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_tarski(sK1)))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))) | ~r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | (spl5_2 | ~spl5_11 | ~spl5_18)),
% 14.02/2.21    inference(forward_demodulation,[],[f1219,f2747])).
% 14.02/2.21  fof(f1219,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))) | ~r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | (spl5_2 | ~spl5_11)),
% 14.02/2.21    inference(backward_demodulation,[],[f1192,f1143])).
% 14.02/2.21  fof(f1192,plain,(
% 14.02/2.21    ~r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK0))))) | (spl5_2 | ~spl5_11)),
% 14.02/2.21    inference(forward_demodulation,[],[f1170,f91])).
% 14.02/2.21  fof(f1170,plain,(
% 14.02/2.21    ~r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_xboole_0)) | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK0))))) | (spl5_2 | ~spl5_11)),
% 14.02/2.21    inference(backward_demodulation,[],[f179,f1164])).
% 14.02/2.21  fof(f179,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK0))))) | ~r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) | spl5_2),
% 14.02/2.21    inference(forward_demodulation,[],[f178,f91])).
% 14.02/2.21  fof(f178,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k1_xboole_0))) | ~r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) | spl5_2),
% 14.02/2.21    inference(forward_demodulation,[],[f177,f90])).
% 14.02/2.21  fof(f177,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))),k1_xboole_0)) | ~r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) | spl5_2),
% 14.02/2.21    inference(forward_demodulation,[],[f155,f90])).
% 14.02/2.21  fof(f155,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))),k1_xboole_0) | ~r1_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) | spl5_2),
% 14.02/2.21    inference(superposition,[],[f145,f86])).
% 14.02/2.21  fof(f3552,plain,(
% 14.02/2.21    ~spl5_78 | spl5_9 | ~spl5_18),
% 14.02/2.21    inference(avatar_split_clause,[],[f3211,f523,f245,f3550])).
% 14.02/2.21  fof(f3550,plain,(
% 14.02/2.21    spl5_78 <=> k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_tarski(sK1))))))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).
% 14.02/2.21  fof(f3211,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_tarski(sK1)))))) | (spl5_9 | ~spl5_18)),
% 14.02/2.21    inference(forward_demodulation,[],[f246,f2747])).
% 14.02/2.21  fof(f3532,plain,(
% 14.02/2.21    spl5_77 | ~spl5_35),
% 14.02/2.21    inference(avatar_split_clause,[],[f2622,f1055,f3530])).
% 14.02/2.21  fof(f3530,plain,(
% 14.02/2.21    spl5_77 <=> r1_xboole_0(k1_xboole_0,k1_tarski(sK0))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).
% 14.02/2.21  fof(f1055,plain,(
% 14.02/2.21    spl5_35 <=> r1_xboole_0(k1_tarski(sK0),k1_xboole_0)),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 14.02/2.21  fof(f2622,plain,(
% 14.02/2.21    r1_xboole_0(k1_xboole_0,k1_tarski(sK0)) | ~spl5_35),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f1056,f88])).
% 14.02/2.21  fof(f1056,plain,(
% 14.02/2.21    r1_xboole_0(k1_tarski(sK0),k1_xboole_0) | ~spl5_35),
% 14.02/2.21    inference(avatar_component_clause,[],[f1055])).
% 14.02/2.21  fof(f3480,plain,(
% 14.02/2.21    ~spl5_76 | ~spl5_18 | spl5_46),
% 14.02/2.21    inference(avatar_split_clause,[],[f3274,f1916,f523,f3478])).
% 14.02/2.21  fof(f3478,plain,(
% 14.02/2.21    spl5_76 <=> k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK1)))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).
% 14.02/2.21  fof(f1916,plain,(
% 14.02/2.21    spl5_46 <=> k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1))))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 14.02/2.21  fof(f3274,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK1))) | (~spl5_18 | spl5_46)),
% 14.02/2.21    inference(forward_demodulation,[],[f1917,f2747])).
% 14.02/2.21  fof(f1917,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) | spl5_46),
% 14.02/2.21    inference(avatar_component_clause,[],[f1916])).
% 14.02/2.21  fof(f3447,plain,(
% 14.02/2.21    ~spl5_75 | spl5_32),
% 14.02/2.21    inference(avatar_split_clause,[],[f2562,f988,f3445])).
% 14.02/2.21  fof(f3445,plain,(
% 14.02/2.21    spl5_75 <=> r1_tarski(k1_tarski(sK0),k1_xboole_0)),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).
% 14.02/2.21  fof(f2562,plain,(
% 14.02/2.21    ~r1_tarski(k1_tarski(sK0),k1_xboole_0) | spl5_32),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f989,f95])).
% 14.02/2.21  fof(f3443,plain,(
% 14.02/2.21    ~spl5_74 | ~spl5_18 | spl5_28),
% 14.02/2.21    inference(avatar_split_clause,[],[f3296,f680,f523,f3441])).
% 14.02/2.21  fof(f680,plain,(
% 14.02/2.21    spl5_28 <=> k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK1)))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 14.02/2.21  fof(f3296,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | (~spl5_18 | spl5_28)),
% 14.02/2.21    inference(forward_demodulation,[],[f681,f2747])).
% 14.02/2.21  fof(f681,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | spl5_28),
% 14.02/2.21    inference(avatar_component_clause,[],[f680])).
% 14.02/2.21  fof(f3391,plain,(
% 14.02/2.21    ~spl5_73 | ~spl5_18 | spl5_43),
% 14.02/2.21    inference(avatar_split_clause,[],[f3279,f1483,f523,f3389])).
% 14.02/2.21  fof(f3389,plain,(
% 14.02/2.21    spl5_73 <=> k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK1)))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).
% 14.02/2.21  fof(f1483,plain,(
% 14.02/2.21    spl5_43 <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 14.02/2.21  fof(f3279,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK1))) | (~spl5_18 | spl5_43)),
% 14.02/2.21    inference(forward_demodulation,[],[f1484,f2747])).
% 14.02/2.21  fof(f1484,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))) | spl5_43),
% 14.02/2.21    inference(avatar_component_clause,[],[f1483])).
% 14.02/2.21  fof(f3206,plain,(
% 14.02/2.21    spl5_16 | ~spl5_18 | ~spl5_19),
% 14.02/2.21    inference(avatar_contradiction_clause,[],[f3205])).
% 14.02/2.21  fof(f3205,plain,(
% 14.02/2.21    $false | (spl5_16 | ~spl5_18 | ~spl5_19)),
% 14.02/2.21    inference(subsumption_resolution,[],[f3204,f2759])).
% 14.02/2.21  fof(f3204,plain,(
% 14.02/2.21    ~r2_hidden(sK1,k5_xboole_0(k1_xboole_0,sK2)) | (~spl5_18 | ~spl5_19)),
% 14.02/2.21    inference(forward_demodulation,[],[f2989,f91])).
% 14.02/2.21  fof(f2989,plain,(
% 14.02/2.21    ~r2_hidden(sK1,k5_xboole_0(sK2,k1_xboole_0)) | (~spl5_18 | ~spl5_19)),
% 14.02/2.21    inference(backward_demodulation,[],[f2792,f2793])).
% 14.02/2.21  fof(f2793,plain,(
% 14.02/2.21    k1_xboole_0 = k1_tarski(sK1) | (~spl5_18 | ~spl5_19)),
% 14.02/2.21    inference(forward_demodulation,[],[f2747,f2097])).
% 14.02/2.21  fof(f2097,plain,(
% 14.02/2.21    k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK1)) | ~spl5_19),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f2032,f86])).
% 14.02/2.21  fof(f2792,plain,(
% 14.02/2.21    ~r2_hidden(sK1,k5_xboole_0(sK2,k1_tarski(sK1))) | ~spl5_18),
% 14.02/2.21    inference(forward_demodulation,[],[f2751,f91])).
% 14.02/2.21  fof(f2751,plain,(
% 14.02/2.21    ~r2_hidden(sK1,k5_xboole_0(k1_tarski(sK1),sK2)) | ~spl5_18),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f125,f524,f83])).
% 14.02/2.21  fof(f3201,plain,(
% 14.02/2.21    spl5_16 | ~spl5_18 | ~spl5_19 | spl5_66),
% 14.02/2.21    inference(avatar_contradiction_clause,[],[f3200])).
% 14.02/2.21  fof(f3200,plain,(
% 14.02/2.21    $false | (spl5_16 | ~spl5_18 | ~spl5_19 | spl5_66)),
% 14.02/2.21    inference(subsumption_resolution,[],[f3199,f2620])).
% 14.02/2.21  fof(f2620,plain,(
% 14.02/2.21    ~r2_hidden(sK1,k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,sK2))) | (spl5_16 | spl5_66)),
% 14.02/2.21    inference(forward_demodulation,[],[f2619,f91])).
% 14.02/2.21  fof(f2619,plain,(
% 14.02/2.21    ~r2_hidden(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,k1_xboole_0))) | (spl5_16 | spl5_66)),
% 14.02/2.21    inference(forward_demodulation,[],[f2587,f90])).
% 14.02/2.21  fof(f2587,plain,(
% 14.02/2.21    ~r2_hidden(sK1,k5_xboole_0(k5_xboole_0(sK2,sK2),k1_xboole_0)) | (spl5_16 | spl5_66)),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f483,f2459,f82])).
% 14.02/2.21  fof(f3199,plain,(
% 14.02/2.21    r2_hidden(sK1,k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,sK2))) | (~spl5_18 | ~spl5_19 | spl5_66)),
% 14.02/2.21    inference(forward_demodulation,[],[f2972,f91])).
% 14.02/2.21  fof(f2972,plain,(
% 14.02/2.21    r2_hidden(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,k1_xboole_0))) | (~spl5_18 | ~spl5_19 | spl5_66)),
% 14.02/2.21    inference(backward_demodulation,[],[f2611,f2793])).
% 14.02/2.21  fof(f2611,plain,(
% 14.02/2.21    r2_hidden(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,k1_tarski(sK1)))) | spl5_66),
% 14.02/2.21    inference(forward_demodulation,[],[f2597,f90])).
% 14.02/2.21  fof(f2597,plain,(
% 14.02/2.21    r2_hidden(sK1,k5_xboole_0(k5_xboole_0(sK2,sK2),k1_tarski(sK1))) | spl5_66),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f125,f2459,f85])).
% 14.02/2.21  fof(f3198,plain,(
% 14.02/2.21    spl5_16 | ~spl5_18 | ~spl5_19 | spl5_66),
% 14.02/2.21    inference(avatar_contradiction_clause,[],[f3197])).
% 14.02/2.21  fof(f3197,plain,(
% 14.02/2.21    $false | (spl5_16 | ~spl5_18 | ~spl5_19 | spl5_66)),
% 14.02/2.21    inference(subsumption_resolution,[],[f2969,f1120])).
% 14.02/2.21  fof(f1120,plain,(
% 14.02/2.21    ( ! [X0] : (~r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)))) ) | spl5_16),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f483,f123])).
% 14.02/2.21  fof(f2969,plain,(
% 14.02/2.21    r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(sK2,sK2)))) | (~spl5_18 | ~spl5_19 | spl5_66)),
% 14.02/2.21    inference(backward_demodulation,[],[f2603,f2793])).
% 14.02/2.21  fof(f2603,plain,(
% 14.02/2.21    r2_hidden(sK1,k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,sK2)))) | spl5_66),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f125,f2459,f121])).
% 14.02/2.21  fof(f121,plain,(
% 14.02/2.21    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 14.02/2.21    inference(equality_resolution,[],[f110])).
% 14.02/2.21  fof(f110,plain,(
% 14.02/2.21    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 14.02/2.21    inference(definition_unfolding,[],[f65,f73])).
% 14.02/2.21  fof(f65,plain,(
% 14.02/2.21    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 14.02/2.21    inference(cnf_transformation,[],[f45])).
% 14.02/2.21  fof(f3196,plain,(
% 14.02/2.21    spl5_16 | ~spl5_18 | ~spl5_19 | spl5_66),
% 14.02/2.21    inference(avatar_contradiction_clause,[],[f3195])).
% 14.02/2.21  fof(f3195,plain,(
% 14.02/2.21    $false | (spl5_16 | ~spl5_18 | ~spl5_19 | spl5_66)),
% 14.02/2.21    inference(subsumption_resolution,[],[f2966,f2592])).
% 14.02/2.21  fof(f2592,plain,(
% 14.02/2.21    ~r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,sK2))) | (spl5_16 | spl5_66)),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f483,f2459,f82])).
% 14.02/2.21  fof(f2966,plain,(
% 14.02/2.21    r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,sK2))) | (~spl5_18 | ~spl5_19 | spl5_66)),
% 14.02/2.21    inference(backward_demodulation,[],[f2596,f2793])).
% 14.02/2.21  fof(f2596,plain,(
% 14.02/2.21    r2_hidden(sK1,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,sK2))) | spl5_66),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f125,f2459,f84])).
% 14.02/2.21  fof(f3152,plain,(
% 14.02/2.21    spl5_3 | ~spl5_18 | ~spl5_19 | ~spl5_61),
% 14.02/2.21    inference(avatar_contradiction_clause,[],[f3151])).
% 14.02/2.21  fof(f3151,plain,(
% 14.02/2.21    $false | (spl5_3 | ~spl5_18 | ~spl5_19 | ~spl5_61)),
% 14.02/2.21    inference(subsumption_resolution,[],[f2950,f102])).
% 14.02/2.21  fof(f2950,plain,(
% 14.02/2.21    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) | (spl5_3 | ~spl5_18 | ~spl5_19 | ~spl5_61)),
% 14.02/2.21    inference(backward_demodulation,[],[f2506,f2793])).
% 14.02/2.21  fof(f3085,plain,(
% 14.02/2.21    ~spl5_18 | ~spl5_19 | spl5_48),
% 14.02/2.21    inference(avatar_contradiction_clause,[],[f3084])).
% 14.02/2.21  fof(f3084,plain,(
% 14.02/2.21    $false | (~spl5_18 | ~spl5_19 | spl5_48)),
% 14.02/2.21    inference(subsumption_resolution,[],[f2880,f128])).
% 14.02/2.21  fof(f128,plain,(
% 14.02/2.21    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 14.02/2.21    inference(equality_resolution,[],[f97])).
% 14.02/2.21  fof(f97,plain,(
% 14.02/2.21    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 14.02/2.21    inference(cnf_transformation,[],[f56])).
% 14.02/2.21  fof(f56,plain,(
% 14.02/2.21    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 14.02/2.21    inference(flattening,[],[f55])).
% 14.02/2.21  fof(f55,plain,(
% 14.02/2.21    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 14.02/2.21    inference(nnf_transformation,[],[f7])).
% 14.02/2.21  fof(f7,axiom,(
% 14.02/2.21    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 14.02/2.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 14.02/2.21  fof(f2880,plain,(
% 14.02/2.21    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl5_18 | ~spl5_19 | spl5_48)),
% 14.02/2.21    inference(backward_demodulation,[],[f1989,f2793])).
% 14.02/2.21  fof(f3031,plain,(
% 14.02/2.21    spl5_16 | ~spl5_18 | ~spl5_19),
% 14.02/2.21    inference(avatar_contradiction_clause,[],[f3030])).
% 14.02/2.21  fof(f3030,plain,(
% 14.02/2.21    $false | (spl5_16 | ~spl5_18 | ~spl5_19)),
% 14.02/2.21    inference(subsumption_resolution,[],[f3029,f483])).
% 14.02/2.21  fof(f3029,plain,(
% 14.02/2.21    r2_hidden(sK1,k1_xboole_0) | (spl5_16 | ~spl5_18 | ~spl5_19)),
% 14.02/2.21    inference(forward_demodulation,[],[f2844,f102])).
% 14.02/2.21  fof(f2844,plain,(
% 14.02/2.21    r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k1_xboole_0)) | (spl5_16 | ~spl5_18 | ~spl5_19)),
% 14.02/2.21    inference(backward_demodulation,[],[f1113,f2793])).
% 14.02/2.21  fof(f2992,plain,(
% 14.02/2.21    spl5_3 | spl5_16 | ~spl5_18 | ~spl5_19),
% 14.02/2.21    inference(avatar_contradiction_clause,[],[f2991])).
% 14.02/2.21  fof(f2991,plain,(
% 14.02/2.21    $false | (spl5_3 | spl5_16 | ~spl5_18 | ~spl5_19)),
% 14.02/2.21    inference(subsumption_resolution,[],[f2990,f1127])).
% 14.02/2.21  fof(f1127,plain,(
% 14.02/2.21    ~r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) | (spl5_3 | spl5_16)),
% 14.02/2.21    inference(forward_demodulation,[],[f1109,f91])).
% 14.02/2.21  fof(f1109,plain,(
% 14.02/2.21    ~r2_hidden(sK1,k5_xboole_0(k1_tarski(sK0),k1_xboole_0)) | (spl5_3 | spl5_16)),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f183,f483,f82])).
% 14.02/2.21  fof(f2990,plain,(
% 14.02/2.21    r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) | (spl5_3 | ~spl5_18 | ~spl5_19)),
% 14.02/2.21    inference(forward_demodulation,[],[f2796,f91])).
% 14.02/2.21  fof(f2796,plain,(
% 14.02/2.21    r2_hidden(sK1,k5_xboole_0(k1_tarski(sK0),k1_xboole_0)) | (spl5_3 | ~spl5_18 | ~spl5_19)),
% 14.02/2.21    inference(backward_demodulation,[],[f195,f2793])).
% 14.02/2.21  fof(f2790,plain,(
% 14.02/2.21    spl5_16 | ~spl5_18 | ~spl5_19),
% 14.02/2.21    inference(avatar_contradiction_clause,[],[f2789])).
% 14.02/2.21  fof(f2789,plain,(
% 14.02/2.21    $false | (spl5_16 | ~spl5_18 | ~spl5_19)),
% 14.02/2.21    inference(subsumption_resolution,[],[f2788,f483])).
% 14.02/2.21  fof(f2788,plain,(
% 14.02/2.21    r2_hidden(sK1,k1_xboole_0) | (~spl5_18 | ~spl5_19)),
% 14.02/2.21    inference(forward_demodulation,[],[f2757,f2097])).
% 14.02/2.21  fof(f2757,plain,(
% 14.02/2.21    r2_hidden(sK1,k3_xboole_0(sK2,k1_tarski(sK1))) | ~spl5_18),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f120,f524,f84])).
% 14.02/2.21  fof(f2782,plain,(
% 14.02/2.21    ~spl5_18 | ~spl5_19),
% 14.02/2.21    inference(avatar_contradiction_clause,[],[f2781])).
% 14.02/2.21  fof(f2781,plain,(
% 14.02/2.21    $false | (~spl5_18 | ~spl5_19)),
% 14.02/2.21    inference(subsumption_resolution,[],[f2780,f102])).
% 14.02/2.21  fof(f2780,plain,(
% 14.02/2.21    sK2 != k5_xboole_0(sK2,k1_xboole_0) | (~spl5_18 | ~spl5_19)),
% 14.02/2.21    inference(forward_demodulation,[],[f2766,f2097])).
% 14.02/2.21  fof(f2766,plain,(
% 14.02/2.21    sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))) | ~spl5_18),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f524,f114])).
% 14.02/2.21  fof(f2779,plain,(
% 14.02/2.21    spl5_3 | ~spl5_18 | ~spl5_19 | ~spl5_61),
% 14.02/2.21    inference(avatar_contradiction_clause,[],[f2778])).
% 14.02/2.21  fof(f2778,plain,(
% 14.02/2.21    $false | (spl5_3 | ~spl5_18 | ~spl5_19 | ~spl5_61)),
% 14.02/2.21    inference(subsumption_resolution,[],[f2777,f2506])).
% 14.02/2.21  fof(f2777,plain,(
% 14.02/2.21    k1_xboole_0 = k5_xboole_0(k1_tarski(sK1),k1_xboole_0) | (~spl5_18 | ~spl5_19)),
% 14.02/2.21    inference(forward_demodulation,[],[f2776,f2097])).
% 14.02/2.21  fof(f2634,plain,(
% 14.02/2.21    spl5_72 | spl5_18),
% 14.02/2.21    inference(avatar_split_clause,[],[f1737,f523,f2632])).
% 14.02/2.21  fof(f1737,plain,(
% 14.02/2.21    r2_hidden(sK1,k5_xboole_0(sK2,k1_tarski(sK1))) | spl5_18),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f125,f1325,f85])).
% 14.02/2.21  fof(f2630,plain,(
% 14.02/2.21    ~spl5_71 | spl5_30),
% 14.02/2.21    inference(avatar_split_clause,[],[f940,f861,f2628])).
% 14.02/2.21  fof(f861,plain,(
% 14.02/2.21    spl5_30 <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK1)))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 14.02/2.21  fof(f940,plain,(
% 14.02/2.21    ~r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | spl5_30),
% 14.02/2.21    inference(trivial_inequality_removal,[],[f938])).
% 14.02/2.21  fof(f938,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK1))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK1))) | ~r1_tarski(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | spl5_30),
% 14.02/2.21    inference(superposition,[],[f862,f93])).
% 14.02/2.21  fof(f862,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK1))) | spl5_30),
% 14.02/2.21    inference(avatar_component_clause,[],[f861])).
% 14.02/2.21  fof(f2531,plain,(
% 14.02/2.21    spl5_70 | ~spl5_19 | spl5_25),
% 14.02/2.21    inference(avatar_split_clause,[],[f2109,f632,f527,f2529])).
% 14.02/2.21  fof(f2529,plain,(
% 14.02/2.21    spl5_70 <=> ! [X2] : (k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X2)))) | r2_hidden(sK3(sK2,k1_tarski(sK1),X2),k1_tarski(sK1)) | ~r2_hidden(sK3(sK2,k1_tarski(sK1),X2),sK2) | ~r2_hidden(sK3(sK2,k1_tarski(sK1),X2),X2))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).
% 14.02/2.21  fof(f2109,plain,(
% 14.02/2.21    ( ! [X2] : (k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X2)))) | r2_hidden(sK3(sK2,k1_tarski(sK1),X2),k1_tarski(sK1)) | ~r2_hidden(sK3(sK2,k1_tarski(sK1),X2),sK2) | ~r2_hidden(sK3(sK2,k1_tarski(sK1),X2),X2)) ) | (~spl5_19 | spl5_25)),
% 14.02/2.21    inference(backward_demodulation,[],[f646,f2097])).
% 14.02/2.21  fof(f2527,plain,(
% 14.02/2.21    ~spl5_32 | spl5_4 | ~spl5_61),
% 14.02/2.21    inference(avatar_split_clause,[],[f2501,f2382,f186,f988])).
% 14.02/2.21  fof(f2501,plain,(
% 14.02/2.21    ~r2_hidden(sK0,k1_xboole_0) | (spl5_4 | ~spl5_61)),
% 14.02/2.21    inference(backward_demodulation,[],[f226,f2499])).
% 14.02/2.21  fof(f226,plain,(
% 14.02/2.21    ~r2_hidden(sK0,k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | spl5_4),
% 14.02/2.21    inference(forward_demodulation,[],[f216,f94])).
% 14.02/2.21  fof(f216,plain,(
% 14.02/2.21    ~r2_hidden(sK0,k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) | spl5_4),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f120,f187,f85])).
% 14.02/2.21  fof(f2510,plain,(
% 14.02/2.21    spl5_69 | spl5_15 | ~spl5_19),
% 14.02/2.21    inference(avatar_split_clause,[],[f2100,f527,f443,f2508])).
% 14.02/2.21  fof(f2508,plain,(
% 14.02/2.21    spl5_69 <=> ! [X2] : (k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X2)))) | r2_hidden(sK3(sK2,k1_tarski(sK1),X2),k1_tarski(sK1)) | ~r2_hidden(sK3(sK2,k1_tarski(sK1),X2),sK2) | ~r2_hidden(sK3(sK2,k1_tarski(sK1),X2),X2))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).
% 14.02/2.21  fof(f2100,plain,(
% 14.02/2.21    ( ! [X2] : (k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X2)))) | r2_hidden(sK3(sK2,k1_tarski(sK1),X2),k1_tarski(sK1)) | ~r2_hidden(sK3(sK2,k1_tarski(sK1),X2),sK2) | ~r2_hidden(sK3(sK2,k1_tarski(sK1),X2),X2)) ) | (spl5_15 | ~spl5_19)),
% 14.02/2.21    inference(backward_demodulation,[],[f457,f2097])).
% 14.02/2.21  fof(f2484,plain,(
% 14.02/2.21    spl5_68 | spl5_18 | ~spl5_19 | spl5_25),
% 14.02/2.21    inference(avatar_split_clause,[],[f2139,f632,f527,f523,f2482])).
% 14.02/2.21  fof(f2482,plain,(
% 14.02/2.21    spl5_68 <=> ! [X2] : (k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,X2)) | ~r2_hidden(sK3(k1_tarski(sK0),sK2,X2),X2) | ~r2_hidden(sK3(k1_tarski(sK0),sK2,X2),k1_tarski(sK0)) | r2_hidden(sK3(k1_tarski(sK0),sK2,X2),sK2))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).
% 14.02/2.21  fof(f2139,plain,(
% 14.02/2.21    ( ! [X2] : (k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,X2)) | ~r2_hidden(sK3(k1_tarski(sK0),sK2,X2),X2) | ~r2_hidden(sK3(k1_tarski(sK0),sK2,X2),k1_tarski(sK0)) | r2_hidden(sK3(k1_tarski(sK0),sK2,X2),sK2)) ) | (spl5_18 | ~spl5_19 | spl5_25)),
% 14.02/2.21    inference(backward_demodulation,[],[f1820,f2097])).
% 14.02/2.21  fof(f1820,plain,(
% 14.02/2.21    ( ! [X2] : (~r2_hidden(sK3(k1_tarski(sK0),sK2,X2),X2) | ~r2_hidden(sK3(k1_tarski(sK0),sK2,X2),k1_tarski(sK0)) | r2_hidden(sK3(k1_tarski(sK0),sK2,X2),sK2) | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X2)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))) ) | (spl5_18 | spl5_25)),
% 14.02/2.21    inference(forward_demodulation,[],[f1819,f1741])).
% 14.02/2.21  fof(f1741,plain,(
% 14.02/2.21    sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))) | spl5_18),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f1325,f113])).
% 14.02/2.21  fof(f1819,plain,(
% 14.02/2.21    ( ! [X2] : (~r2_hidden(sK3(k1_tarski(sK0),sK2,X2),k1_tarski(sK0)) | r2_hidden(sK3(k1_tarski(sK0),sK2,X2),sK2) | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X2)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | ~r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X2),X2)) ) | (spl5_18 | spl5_25)),
% 14.02/2.21    inference(forward_demodulation,[],[f1760,f1741])).
% 14.02/2.21  fof(f1760,plain,(
% 14.02/2.21    ( ! [X2] : (r2_hidden(sK3(k1_tarski(sK0),sK2,X2),sK2) | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X2)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | ~r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X2),k1_tarski(sK0)) | ~r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X2),X2)) ) | (spl5_18 | spl5_25)),
% 14.02/2.21    inference(backward_demodulation,[],[f653,f1741])).
% 14.02/2.21  fof(f653,plain,(
% 14.02/2.21    ( ! [X2] : (k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X2)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X2),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))) | ~r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X2),k1_tarski(sK0)) | ~r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X2),X2)) ) | spl5_25),
% 14.02/2.21    inference(superposition,[],[f633,f107])).
% 14.02/2.21  fof(f2464,plain,(
% 14.02/2.21    spl5_67 | spl5_15 | spl5_18 | ~spl5_19),
% 14.02/2.21    inference(avatar_split_clause,[],[f2138,f527,f523,f443,f2462])).
% 14.02/2.21  fof(f2462,plain,(
% 14.02/2.21    spl5_67 <=> ! [X2] : (k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,X2)) | ~r2_hidden(sK3(k1_tarski(sK0),sK2,X2),X2) | ~r2_hidden(sK3(k1_tarski(sK0),sK2,X2),k1_tarski(sK0)) | r2_hidden(sK3(k1_tarski(sK0),sK2,X2),sK2))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).
% 14.02/2.21  fof(f2138,plain,(
% 14.02/2.21    ( ! [X2] : (k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,X2)) | ~r2_hidden(sK3(k1_tarski(sK0),sK2,X2),X2) | ~r2_hidden(sK3(k1_tarski(sK0),sK2,X2),k1_tarski(sK0)) | r2_hidden(sK3(k1_tarski(sK0),sK2,X2),sK2)) ) | (spl5_15 | spl5_18 | ~spl5_19)),
% 14.02/2.21    inference(backward_demodulation,[],[f1794,f2097])).
% 14.02/2.21  fof(f1794,plain,(
% 14.02/2.21    ( ! [X2] : (~r2_hidden(sK3(k1_tarski(sK0),sK2,X2),X2) | ~r2_hidden(sK3(k1_tarski(sK0),sK2,X2),k1_tarski(sK0)) | r2_hidden(sK3(k1_tarski(sK0),sK2,X2),sK2) | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X2)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))) ) | (spl5_15 | spl5_18)),
% 14.02/2.21    inference(forward_demodulation,[],[f1793,f1741])).
% 14.02/2.21  fof(f1793,plain,(
% 14.02/2.21    ( ! [X2] : (~r2_hidden(sK3(k1_tarski(sK0),sK2,X2),k1_tarski(sK0)) | r2_hidden(sK3(k1_tarski(sK0),sK2,X2),sK2) | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X2)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | ~r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X2),X2)) ) | (spl5_15 | spl5_18)),
% 14.02/2.21    inference(forward_demodulation,[],[f1752,f1741])).
% 14.02/2.21  fof(f1752,plain,(
% 14.02/2.21    ( ! [X2] : (r2_hidden(sK3(k1_tarski(sK0),sK2,X2),sK2) | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X2)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | ~r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X2),k1_tarski(sK0)) | ~r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X2),X2)) ) | (spl5_15 | spl5_18)),
% 14.02/2.21    inference(backward_demodulation,[],[f464,f1741])).
% 14.02/2.21  fof(f464,plain,(
% 14.02/2.21    ( ! [X2] : (k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X2)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X2),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))) | ~r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X2),k1_tarski(sK0)) | ~r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X2),X2)) ) | spl5_15),
% 14.02/2.21    inference(superposition,[],[f444,f107])).
% 14.02/2.21  fof(f2460,plain,(
% 14.02/2.21    ~spl5_66 | spl5_18),
% 14.02/2.21    inference(avatar_split_clause,[],[f1734,f523,f2458])).
% 14.02/2.21  fof(f1734,plain,(
% 14.02/2.21    ~r2_hidden(sK1,k5_xboole_0(sK2,sK2)) | spl5_18),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f1325,f1325,f82])).
% 14.02/2.21  fof(f2438,plain,(
% 14.02/2.21    spl5_65 | ~spl5_19 | spl5_25),
% 14.02/2.21    inference(avatar_split_clause,[],[f2108,f632,f527,f2436])).
% 14.02/2.21  fof(f2436,plain,(
% 14.02/2.21    spl5_65 <=> ! [X1] : (k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1)))) | ~r2_hidden(sK3(sK2,k1_tarski(sK1),X1),k1_tarski(sK1)) | r2_hidden(sK3(sK2,k1_tarski(sK1),X1),X1))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).
% 14.02/2.21  fof(f2108,plain,(
% 14.02/2.21    ( ! [X1] : (k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1)))) | ~r2_hidden(sK3(sK2,k1_tarski(sK1),X1),k1_tarski(sK1)) | r2_hidden(sK3(sK2,k1_tarski(sK1),X1),X1)) ) | (~spl5_19 | spl5_25)),
% 14.02/2.21    inference(backward_demodulation,[],[f645,f2097])).
% 14.02/2.21  fof(f2412,plain,(
% 14.02/2.21    spl5_64 | ~spl5_19 | spl5_25),
% 14.02/2.21    inference(avatar_split_clause,[],[f2107,f632,f527,f2410])).
% 14.02/2.21  fof(f2410,plain,(
% 14.02/2.21    spl5_64 <=> ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0)))) | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),sK2) | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),X0))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).
% 14.02/2.21  fof(f2107,plain,(
% 14.02/2.21    ( ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0)))) | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),sK2) | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),X0)) ) | (~spl5_19 | spl5_25)),
% 14.02/2.21    inference(backward_demodulation,[],[f644,f2097])).
% 14.02/2.21  fof(f2408,plain,(
% 14.02/2.21    ~spl5_63 | spl5_4),
% 14.02/2.21    inference(avatar_split_clause,[],[f217,f186,f2406])).
% 14.02/2.21  fof(f2406,plain,(
% 14.02/2.21    spl5_63 <=> r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).
% 14.02/2.21  fof(f217,plain,(
% 14.02/2.21    ~r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) | spl5_4),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f187,f95])).
% 14.02/2.21  fof(f2388,plain,(
% 14.02/2.21    spl5_62 | spl5_15 | ~spl5_19),
% 14.02/2.21    inference(avatar_split_clause,[],[f2099,f527,f443,f2386])).
% 14.02/2.21  fof(f2386,plain,(
% 14.02/2.21    spl5_62 <=> ! [X1] : (k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1)))) | ~r2_hidden(sK3(sK2,k1_tarski(sK1),X1),k1_tarski(sK1)) | r2_hidden(sK3(sK2,k1_tarski(sK1),X1),X1))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).
% 14.02/2.21  fof(f2099,plain,(
% 14.02/2.21    ( ! [X1] : (k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1)))) | ~r2_hidden(sK3(sK2,k1_tarski(sK1),X1),k1_tarski(sK1)) | r2_hidden(sK3(sK2,k1_tarski(sK1),X1),X1)) ) | (spl5_15 | ~spl5_19)),
% 14.02/2.21    inference(backward_demodulation,[],[f456,f2097])).
% 14.02/2.21  fof(f2384,plain,(
% 14.02/2.21    spl5_61 | spl5_4),
% 14.02/2.21    inference(avatar_split_clause,[],[f209,f186,f2382])).
% 14.02/2.21  fof(f209,plain,(
% 14.02/2.21    r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | spl5_4),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f187,f81])).
% 14.02/2.21  fof(f2364,plain,(
% 14.02/2.21    spl5_60 | ~spl5_19 | ~spl5_52),
% 14.02/2.21    inference(avatar_split_clause,[],[f2193,f2093,f527,f2362])).
% 14.02/2.21  fof(f2362,plain,(
% 14.02/2.21    spl5_60 <=> ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0)))) | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),sK2) | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),X0))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).
% 14.02/2.21  fof(f2193,plain,(
% 14.02/2.21    ( ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0)))) | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),sK2) | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),X0)) ) | (~spl5_19 | ~spl5_52)),
% 14.02/2.21    inference(backward_demodulation,[],[f2094,f2097])).
% 14.02/2.21  fof(f2360,plain,(
% 14.02/2.21    ~spl5_59 | spl5_3),
% 14.02/2.21    inference(avatar_split_clause,[],[f197,f182,f2358])).
% 14.02/2.21  fof(f2358,plain,(
% 14.02/2.21    spl5_59 <=> r1_tarski(k1_tarski(sK1),k1_tarski(sK0))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).
% 14.02/2.21  fof(f197,plain,(
% 14.02/2.21    ~r1_tarski(k1_tarski(sK1),k1_tarski(sK0)) | spl5_3),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f183,f95])).
% 14.02/2.21  fof(f2347,plain,(
% 14.02/2.21    ~spl5_58 | ~spl5_19 | spl5_46),
% 14.02/2.21    inference(avatar_split_clause,[],[f2252,f1916,f527,f2345])).
% 14.02/2.21  fof(f2345,plain,(
% 14.02/2.21    spl5_58 <=> k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) = k5_xboole_0(k1_xboole_0,sK2)),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).
% 14.02/2.21  fof(f2252,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) != k5_xboole_0(k1_xboole_0,sK2) | (~spl5_19 | spl5_46)),
% 14.02/2.21    inference(forward_demodulation,[],[f2251,f91])).
% 14.02/2.21  fof(f2251,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) != k5_xboole_0(sK2,k1_xboole_0) | (~spl5_19 | spl5_46)),
% 14.02/2.21    inference(forward_demodulation,[],[f2151,f102])).
% 14.02/2.21  fof(f2151,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0)) | (~spl5_19 | spl5_46)),
% 14.02/2.21    inference(backward_demodulation,[],[f1917,f2097])).
% 14.02/2.21  fof(f2329,plain,(
% 14.02/2.21    ~spl5_57 | ~spl5_19 | spl5_28),
% 14.02/2.21    inference(avatar_split_clause,[],[f2211,f680,f527,f2327])).
% 14.02/2.21  fof(f2211,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | (~spl5_19 | spl5_28)),
% 14.02/2.21    inference(forward_demodulation,[],[f2116,f91])).
% 14.02/2.21  fof(f2116,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_xboole_0)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | (~spl5_19 | spl5_28)),
% 14.02/2.21    inference(backward_demodulation,[],[f681,f2097])).
% 14.02/2.21  fof(f2314,plain,(
% 14.02/2.21    ~spl5_56 | ~spl5_19 | spl5_26),
% 14.02/2.21    inference(avatar_split_clause,[],[f2206,f663,f527,f2312])).
% 14.02/2.21  fof(f2312,plain,(
% 14.02/2.21    spl5_56 <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).
% 14.02/2.21  fof(f663,plain,(
% 14.02/2.21    spl5_26 <=> k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK1)))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 14.02/2.21  fof(f2206,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | (~spl5_19 | spl5_26)),
% 14.02/2.21    inference(forward_demodulation,[],[f2110,f91])).
% 14.02/2.21  fof(f2110,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_xboole_0)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | (~spl5_19 | spl5_26)),
% 14.02/2.21    inference(backward_demodulation,[],[f664,f2097])).
% 14.02/2.21  fof(f664,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | spl5_26),
% 14.02/2.21    inference(avatar_component_clause,[],[f663])).
% 14.02/2.21  fof(f2310,plain,(
% 14.02/2.21    spl5_55 | ~spl5_20),
% 14.02/2.21    inference(avatar_split_clause,[],[f1305,f531,f2308])).
% 14.02/2.21  fof(f2308,plain,(
% 14.02/2.21    spl5_55 <=> r1_xboole_0(k1_xboole_0,k1_tarski(sK1))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).
% 14.02/2.21  fof(f531,plain,(
% 14.02/2.21    spl5_20 <=> r1_xboole_0(k1_tarski(sK1),k1_xboole_0)),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 14.02/2.21  fof(f1305,plain,(
% 14.02/2.21    r1_xboole_0(k1_xboole_0,k1_tarski(sK1)) | ~spl5_20),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f532,f88])).
% 14.02/2.21  fof(f532,plain,(
% 14.02/2.21    r1_xboole_0(k1_tarski(sK1),k1_xboole_0) | ~spl5_20),
% 14.02/2.21    inference(avatar_component_clause,[],[f531])).
% 14.02/2.21  fof(f2299,plain,(
% 14.02/2.21    ~spl5_54 | ~spl5_19 | spl5_37),
% 14.02/2.21    inference(avatar_split_clause,[],[f2222,f1274,f527,f2297])).
% 14.02/2.21  fof(f2297,plain,(
% 14.02/2.21    spl5_54 <=> k5_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).
% 14.02/2.21  fof(f1274,plain,(
% 14.02/2.21    spl5_37 <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 14.02/2.21  fof(f2222,plain,(
% 14.02/2.21    k5_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | (~spl5_19 | spl5_37)),
% 14.02/2.21    inference(forward_demodulation,[],[f2221,f91])).
% 14.02/2.21  fof(f2221,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k1_xboole_0) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | (~spl5_19 | spl5_37)),
% 14.02/2.21    inference(forward_demodulation,[],[f2127,f102])).
% 14.02/2.21  fof(f2127,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | (~spl5_19 | spl5_37)),
% 14.02/2.21    inference(backward_demodulation,[],[f1275,f2097])).
% 14.02/2.21  fof(f1275,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | spl5_37),
% 14.02/2.21    inference(avatar_component_clause,[],[f1274])).
% 14.02/2.21  fof(f2295,plain,(
% 14.02/2.21    spl5_23 | ~spl5_11),
% 14.02/2.21    inference(avatar_split_clause,[],[f1153,f257,f597])).
% 14.02/2.21  fof(f597,plain,(
% 14.02/2.21    spl5_23 <=> r1_tarski(k1_tarski(sK0),sK2)),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 14.02/2.21  fof(f1153,plain,(
% 14.02/2.21    r1_tarski(k1_tarski(sK0),sK2) | ~spl5_11),
% 14.02/2.21    inference(unit_resulting_resolution,[],[f326,f96])).
% 14.02/2.21  fof(f2288,plain,(
% 14.02/2.21    ~spl5_53 | ~spl5_19 | spl5_43),
% 14.02/2.21    inference(avatar_split_clause,[],[f2234,f1483,f527,f2286])).
% 14.02/2.21  fof(f2286,plain,(
% 14.02/2.21    spl5_53 <=> k5_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))),
% 14.02/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).
% 14.02/2.21  fof(f2234,plain,(
% 14.02/2.21    k5_xboole_0(k1_xboole_0,sK2) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))) | (~spl5_19 | spl5_43)),
% 14.02/2.21    inference(forward_demodulation,[],[f2233,f91])).
% 14.02/2.21  fof(f2233,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k1_xboole_0) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))) | (~spl5_19 | spl5_43)),
% 14.02/2.21    inference(forward_demodulation,[],[f2134,f102])).
% 14.02/2.21  fof(f2134,plain,(
% 14.02/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_xboole_0)) | (~spl5_19 | spl5_43)),
% 14.02/2.21    inference(backward_demodulation,[],[f1484,f2097])).
% 14.02/2.21  fof(f2095,plain,(
% 14.02/2.21    spl5_52 | spl5_15),
% 14.02/2.21    inference(avatar_split_clause,[],[f455,f443,f2093])).
% 14.02/2.21  fof(f455,plain,(
% 14.02/2.21    ( ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),sK2) | r2_hidden(sK3(sK2,k1_tarski(sK1),X0),X0)) ) | spl5_15),
% 14.02/2.21    inference(superposition,[],[f444,f109])).
% 14.02/2.21  fof(f2063,plain,(
% 14.02/2.21    spl5_51 | spl5_18 | spl5_25),
% 14.02/2.21    inference(avatar_split_clause,[],[f1817,f632,f523,f2061])).
% 14.02/2.21  fof(f1817,plain,(
% 14.02/2.21    ( ! [X0] : (r2_hidden(sK3(k1_tarski(sK0),sK2,X0),X0) | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),k1_tarski(sK0)) | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X0)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))) ) | (spl5_18 | spl5_25)),
% 14.02/2.21    inference(forward_demodulation,[],[f1758,f1741])).
% 14.69/2.21  fof(f1758,plain,(
% 14.69/2.21    ( ! [X0] : (r2_hidden(sK3(k1_tarski(sK0),sK2,X0),k1_tarski(sK0)) | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X0)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X0),X0)) ) | (spl5_18 | spl5_25)),
% 14.69/2.21    inference(backward_demodulation,[],[f651,f1741])).
% 14.69/2.21  fof(f651,plain,(
% 14.69/2.21    ( ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X0)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X0),k1_tarski(sK0)) | r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X0),X0)) ) | spl5_25),
% 14.69/2.21    inference(superposition,[],[f633,f109])).
% 14.69/2.21  fof(f2033,plain,(
% 14.69/2.21    spl5_19 | ~spl5_27),
% 14.69/2.21    inference(avatar_split_clause,[],[f1919,f676,f527])).
% 14.69/2.21  fof(f1919,plain,(
% 14.69/2.21    r1_xboole_0(sK2,k1_tarski(sK1)) | ~spl5_27),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f1886,f88])).
% 14.69/2.21  fof(f1886,plain,(
% 14.69/2.21    r1_xboole_0(k1_tarski(sK1),sK2) | ~spl5_27),
% 14.69/2.21    inference(avatar_component_clause,[],[f676])).
% 14.69/2.21  fof(f2031,plain,(
% 14.69/2.21    spl5_50 | spl5_18 | spl5_25),
% 14.69/2.21    inference(avatar_split_clause,[],[f1818,f632,f523,f2029])).
% 14.69/2.21  fof(f1818,plain,(
% 14.69/2.21    ( ! [X1] : (r2_hidden(sK3(k1_tarski(sK0),sK2,X1),X1) | ~r2_hidden(sK3(k1_tarski(sK0),sK2,X1),sK2) | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X1)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))) ) | (spl5_18 | spl5_25)),
% 14.69/2.21    inference(forward_demodulation,[],[f1759,f1741])).
% 14.69/2.21  fof(f1759,plain,(
% 14.69/2.21    ( ! [X1] : (~r2_hidden(sK3(k1_tarski(sK0),sK2,X1),sK2) | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X1)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X1),X1)) ) | (spl5_18 | spl5_25)),
% 14.69/2.21    inference(backward_demodulation,[],[f652,f1741])).
% 14.69/2.21  fof(f652,plain,(
% 14.69/2.21    ( ! [X1] : (k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X1)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | ~r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X1),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))) | r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X1),X1)) ) | spl5_25),
% 14.69/2.21    inference(superposition,[],[f633,f108])).
% 14.69/2.21  fof(f2022,plain,(
% 14.69/2.21    ~spl5_8 | spl5_10),
% 14.69/2.21    inference(avatar_split_clause,[],[f1286,f253,f242])).
% 14.69/2.21  fof(f1286,plain,(
% 14.69/2.21    ~r1_xboole_0(sK2,k1_tarski(sK0)) | spl5_10),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f254,f88])).
% 14.69/2.21  fof(f1994,plain,(
% 14.69/2.21    spl5_49 | spl5_15 | spl5_18),
% 14.69/2.21    inference(avatar_split_clause,[],[f1791,f523,f443,f1992])).
% 14.69/2.21  fof(f1791,plain,(
% 14.69/2.21    ( ! [X0] : (r2_hidden(sK3(k1_tarski(sK0),sK2,X0),X0) | r2_hidden(sK3(k1_tarski(sK0),sK2,X0),k1_tarski(sK0)) | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X0)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))) ) | (spl5_15 | spl5_18)),
% 14.69/2.21    inference(forward_demodulation,[],[f1750,f1741])).
% 14.69/2.21  fof(f1750,plain,(
% 14.69/2.21    ( ! [X0] : (r2_hidden(sK3(k1_tarski(sK0),sK2,X0),k1_tarski(sK0)) | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X0)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X0),X0)) ) | (spl5_15 | spl5_18)),
% 14.69/2.21    inference(backward_demodulation,[],[f462,f1741])).
% 14.69/2.21  fof(f462,plain,(
% 14.69/2.21    ( ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X0)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X0),k1_tarski(sK0)) | r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X0),X0)) ) | spl5_15),
% 14.69/2.21    inference(superposition,[],[f444,f109])).
% 14.69/2.21  fof(f1990,plain,(
% 14.69/2.21    ~spl5_48 | spl5_16),
% 14.69/2.21    inference(avatar_split_clause,[],[f1115,f482,f1988])).
% 14.69/2.21  fof(f1115,plain,(
% 14.69/2.21    ~r1_tarski(k1_tarski(sK1),k1_xboole_0) | spl5_16),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f483,f95])).
% 14.69/2.21  fof(f1959,plain,(
% 14.69/2.21    spl5_47 | spl5_15 | spl5_18),
% 14.69/2.21    inference(avatar_split_clause,[],[f1792,f523,f443,f1957])).
% 14.69/2.21  fof(f1792,plain,(
% 14.69/2.21    ( ! [X1] : (r2_hidden(sK3(k1_tarski(sK0),sK2,X1),X1) | ~r2_hidden(sK3(k1_tarski(sK0),sK2,X1),sK2) | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X1)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))) ) | (spl5_15 | spl5_18)),
% 14.69/2.21    inference(forward_demodulation,[],[f1751,f1741])).
% 14.69/2.21  fof(f1751,plain,(
% 14.69/2.21    ( ! [X1] : (~r2_hidden(sK3(k1_tarski(sK0),sK2,X1),sK2) | k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X1)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X1),X1)) ) | (spl5_15 | spl5_18)),
% 14.69/2.21    inference(backward_demodulation,[],[f463,f1741])).
% 14.69/2.21  fof(f463,plain,(
% 14.69/2.21    ( ! [X1] : (k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),X1)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | ~r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X1),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))) | r2_hidden(sK3(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),X1),X1)) ) | spl5_15),
% 14.69/2.21    inference(superposition,[],[f444,f108])).
% 14.69/2.21  fof(f1918,plain,(
% 14.69/2.21    ~spl5_46 | spl5_9 | ~spl5_11 | spl5_18),
% 14.69/2.21    inference(avatar_split_clause,[],[f1781,f523,f257,f245,f1916])).
% 14.69/2.21  fof(f1781,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) | (spl5_9 | ~spl5_11 | spl5_18)),
% 14.69/2.21    inference(forward_demodulation,[],[f1780,f91])).
% 14.69/2.21  fof(f1780,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) != k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k1_xboole_0)) | (spl5_9 | ~spl5_11 | spl5_18)),
% 14.69/2.21    inference(forward_demodulation,[],[f1779,f1215])).
% 14.69/2.21  fof(f1779,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) != k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))) | (spl5_9 | ~spl5_11 | spl5_18)),
% 14.69/2.21    inference(forward_demodulation,[],[f1778,f1143])).
% 14.69/2.21  fof(f1778,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) != k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) | (spl5_9 | spl5_18)),
% 14.69/2.21    inference(forward_demodulation,[],[f1747,f94])).
% 14.69/2.21  fof(f1747,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) != k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2)))) | (spl5_9 | spl5_18)),
% 14.69/2.21    inference(backward_demodulation,[],[f246,f1741])).
% 14.69/2.21  fof(f1906,plain,(
% 14.69/2.21    ~spl5_31 | spl5_18),
% 14.69/2.21    inference(avatar_split_clause,[],[f1739,f523,f865])).
% 14.69/2.21  fof(f865,plain,(
% 14.69/2.21    spl5_31 <=> r1_tarski(k1_tarski(sK1),sK2)),
% 14.69/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 14.69/2.21  fof(f1739,plain,(
% 14.69/2.21    ~r1_tarski(k1_tarski(sK1),sK2) | spl5_18),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f1325,f95])).
% 14.69/2.21  fof(f1887,plain,(
% 14.69/2.21    spl5_27 | spl5_18),
% 14.69/2.21    inference(avatar_split_clause,[],[f1727,f523,f676])).
% 14.69/2.21  fof(f1727,plain,(
% 14.69/2.21    r1_xboole_0(k1_tarski(sK1),sK2) | spl5_18),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f1325,f81])).
% 14.69/2.21  fof(f1658,plain,(
% 14.69/2.21    spl5_18 | ~spl5_31),
% 14.69/2.21    inference(avatar_contradiction_clause,[],[f1657])).
% 14.69/2.21  fof(f1657,plain,(
% 14.69/2.21    $false | (spl5_18 | ~spl5_31)),
% 14.69/2.21    inference(subsumption_resolution,[],[f1325,f1638])).
% 14.69/2.21  fof(f1638,plain,(
% 14.69/2.21    r2_hidden(sK1,sK2) | ~spl5_31),
% 14.69/2.21    inference(resolution,[],[f866,f95])).
% 14.69/2.21  fof(f866,plain,(
% 14.69/2.21    r1_tarski(k1_tarski(sK1),sK2) | ~spl5_31),
% 14.69/2.21    inference(avatar_component_clause,[],[f865])).
% 14.69/2.21  fof(f1652,plain,(
% 14.69/2.21    ~spl5_32 | spl5_4 | ~spl5_18),
% 14.69/2.21    inference(avatar_split_clause,[],[f1624,f523,f186,f988])).
% 14.69/2.21  fof(f1624,plain,(
% 14.69/2.21    ~r2_hidden(sK0,k1_xboole_0) | (spl5_4 | ~spl5_18)),
% 14.69/2.21    inference(backward_demodulation,[],[f212,f1600])).
% 14.69/2.21  fof(f1600,plain,(
% 14.69/2.21    k1_xboole_0 = k5_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) | ~spl5_18),
% 14.69/2.21    inference(backward_demodulation,[],[f1522,f1498])).
% 14.69/2.21  fof(f1498,plain,(
% 14.69/2.21    k1_tarski(sK1) = k3_xboole_0(sK2,k1_tarski(sK1)) | ~spl5_18),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f524,f80])).
% 14.69/2.21  fof(f1522,plain,(
% 14.69/2.21    k1_xboole_0 = k5_xboole_0(k1_tarski(sK1),k3_xboole_0(sK2,k1_tarski(sK1))) | ~spl5_18),
% 14.69/2.21    inference(forward_demodulation,[],[f1514,f94])).
% 14.69/2.21  fof(f1514,plain,(
% 14.69/2.21    k1_xboole_0 = k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),sK2)) | ~spl5_18),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f524,f118])).
% 14.69/2.21  fof(f212,plain,(
% 14.69/2.21    ~r2_hidden(sK0,k5_xboole_0(k1_tarski(sK1),k1_tarski(sK1))) | spl5_4),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f187,f187,f82])).
% 14.69/2.21  fof(f1643,plain,(
% 14.69/2.21    ~spl5_45 | ~spl5_18 | spl5_37),
% 14.69/2.21    inference(avatar_split_clause,[],[f1586,f1274,f523,f1641])).
% 14.69/2.21  fof(f1641,plain,(
% 14.69/2.21    spl5_45 <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK1))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))),
% 14.69/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 14.69/2.21  fof(f1586,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK1))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | (~spl5_18 | spl5_37)),
% 14.69/2.21    inference(backward_demodulation,[],[f1275,f1498])).
% 14.69/2.21  fof(f1628,plain,(
% 14.69/2.21    ~spl5_44 | ~spl5_18 | spl5_26),
% 14.69/2.21    inference(avatar_split_clause,[],[f1557,f663,f523,f1626])).
% 14.69/2.21  fof(f1626,plain,(
% 14.69/2.21    spl5_44 <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 14.69/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 14.69/2.21  fof(f1557,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | (~spl5_18 | spl5_26)),
% 14.69/2.21    inference(backward_demodulation,[],[f664,f1498])).
% 14.69/2.21  fof(f1495,plain,(
% 14.69/2.21    spl5_16 | spl5_18 | spl5_42),
% 14.69/2.21    inference(avatar_contradiction_clause,[],[f1494])).
% 14.69/2.21  fof(f1494,plain,(
% 14.69/2.21    $false | (spl5_16 | spl5_18 | spl5_42)),
% 14.69/2.21    inference(subsumption_resolution,[],[f1490,f1336])).
% 14.69/2.21  fof(f1336,plain,(
% 14.69/2.21    ~r2_hidden(sK1,k5_xboole_0(k1_xboole_0,sK2)) | (spl5_16 | spl5_18)),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f483,f1325,f82])).
% 14.69/2.21  fof(f1490,plain,(
% 14.69/2.21    r2_hidden(sK1,k5_xboole_0(k1_xboole_0,sK2)) | spl5_42),
% 14.69/2.21    inference(resolution,[],[f1481,f81])).
% 14.69/2.21  fof(f1481,plain,(
% 14.69/2.21    ~r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | spl5_42),
% 14.69/2.21    inference(avatar_component_clause,[],[f1480])).
% 14.69/2.21  fof(f1493,plain,(
% 14.69/2.21    spl5_16 | spl5_18 | spl5_42),
% 14.69/2.21    inference(avatar_contradiction_clause,[],[f1492])).
% 14.69/2.21  fof(f1492,plain,(
% 14.69/2.21    $false | (spl5_16 | spl5_18 | spl5_42)),
% 14.69/2.21    inference(subsumption_resolution,[],[f1486,f1336])).
% 14.69/2.21  fof(f1486,plain,(
% 14.69/2.21    r2_hidden(sK1,k5_xboole_0(k1_xboole_0,sK2)) | spl5_42),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f1481,f81])).
% 14.69/2.21  fof(f1485,plain,(
% 14.69/2.21    ~spl5_42 | ~spl5_43 | spl5_2 | ~spl5_11 | spl5_18),
% 14.69/2.21    inference(avatar_split_clause,[],[f1440,f523,f257,f144,f1483,f1480])).
% 14.69/2.21  fof(f1440,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))) | ~r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | (spl5_2 | ~spl5_11 | spl5_18)),
% 14.69/2.21    inference(forward_demodulation,[],[f1439,f91])).
% 14.69/2.21  fof(f1439,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k1_xboole_0)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))) | ~r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | (spl5_2 | ~spl5_11 | spl5_18)),
% 14.69/2.21    inference(forward_demodulation,[],[f1438,f1215])).
% 14.69/2.21  fof(f1438,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))) | ~r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | (spl5_2 | ~spl5_11 | spl5_18)),
% 14.69/2.21    inference(forward_demodulation,[],[f1437,f1143])).
% 14.69/2.21  fof(f1437,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))) | ~r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | (spl5_2 | ~spl5_11 | spl5_18)),
% 14.69/2.21    inference(forward_demodulation,[],[f1368,f94])).
% 14.69/2.21  fof(f1368,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))) | ~r1_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)) | (spl5_2 | ~spl5_11 | spl5_18)),
% 14.69/2.21    inference(backward_demodulation,[],[f1219,f1344])).
% 14.69/2.21  fof(f1344,plain,(
% 14.69/2.21    sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))) | spl5_18),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f1325,f113])).
% 14.69/2.21  fof(f1329,plain,(
% 14.69/2.21    ~spl5_18 | ~spl5_41 | spl5_25),
% 14.69/2.21    inference(avatar_split_clause,[],[f639,f632,f1327,f523])).
% 14.69/2.21  fof(f1327,plain,(
% 14.69/2.21    spl5_41 <=> k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_tarski(sK1)))))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))),
% 14.69/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 14.69/2.21  fof(f639,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_tarski(sK1)))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | ~r2_hidden(sK1,sK2) | spl5_25),
% 14.69/2.21    inference(superposition,[],[f633,f80])).
% 14.69/2.21  fof(f1304,plain,(
% 14.69/2.21    ~spl5_39 | ~spl5_40 | spl5_15),
% 14.69/2.21    inference(avatar_split_clause,[],[f477,f443,f1302,f1299])).
% 14.69/2.21  fof(f1302,plain,(
% 14.69/2.21    spl5_40 <=> k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))),
% 14.69/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 14.69/2.21  fof(f477,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_xboole_0,k1_tarski(sK0)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | ~r1_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))) | spl5_15),
% 14.69/2.21    inference(forward_demodulation,[],[f459,f91])).
% 14.69/2.21  fof(f459,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k1_xboole_0))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | ~r1_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))) | spl5_15),
% 14.69/2.21    inference(superposition,[],[f444,f86])).
% 14.69/2.21  fof(f1297,plain,(
% 14.69/2.21    ~spl5_38 | spl5_15),
% 14.69/2.21    inference(avatar_split_clause,[],[f448,f443,f1295])).
% 14.69/2.21  fof(f1295,plain,(
% 14.69/2.21    spl5_38 <=> r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))))),
% 14.69/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 14.69/2.21  fof(f448,plain,(
% 14.69/2.21    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))))) | spl5_15),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f444,f126])).
% 14.69/2.21  fof(f1276,plain,(
% 14.69/2.21    ~spl5_37 | spl5_4 | ~spl5_11 | spl5_25),
% 14.69/2.21    inference(avatar_split_clause,[],[f1163,f632,f257,f186,f1274])).
% 14.69/2.21  fof(f1163,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | (spl5_4 | ~spl5_11 | spl5_25)),
% 14.69/2.21    inference(subsumption_resolution,[],[f1060,f1158])).
% 14.69/2.21  fof(f1158,plain,(
% 14.69/2.21    r2_hidden(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))) | (spl5_4 | ~spl5_11)),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f187,f326,f121])).
% 14.69/2.21  fof(f1060,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | ~r2_hidden(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))) | spl5_25),
% 14.69/2.21    inference(forward_demodulation,[],[f917,f91])).
% 14.69/2.21  fof(f917,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k1_xboole_0)) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | ~r2_hidden(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))) | spl5_25),
% 14.69/2.21    inference(superposition,[],[f633,f118])).
% 14.69/2.21  fof(f1142,plain,(
% 14.69/2.21    ~spl5_19 | ~spl5_36 | spl5_15),
% 14.69/2.21    inference(avatar_split_clause,[],[f898,f443,f1102,f527])).
% 14.69/2.21  fof(f1102,plain,(
% 14.69/2.21    spl5_36 <=> k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))),
% 14.69/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 14.69/2.21  fof(f898,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | ~r1_xboole_0(sK2,k1_tarski(sK1)) | spl5_15),
% 14.69/2.21    inference(forward_demodulation,[],[f882,f94])).
% 14.69/2.21  fof(f882,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | ~r1_xboole_0(sK2,k1_tarski(sK1)) | spl5_15),
% 14.69/2.21    inference(superposition,[],[f444,f116])).
% 14.69/2.21  fof(f1104,plain,(
% 14.69/2.21    spl5_18 | ~spl5_36 | spl5_15),
% 14.69/2.21    inference(avatar_split_clause,[],[f895,f443,f1102,f523])).
% 14.69/2.21  fof(f895,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | r2_hidden(sK1,sK2) | spl5_15),
% 14.69/2.21    inference(forward_demodulation,[],[f881,f94])).
% 14.69/2.21  fof(f881,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | r2_hidden(sK1,sK2) | spl5_15),
% 14.69/2.21    inference(superposition,[],[f444,f113])).
% 14.69/2.21  fof(f1065,plain,(
% 14.69/2.21    ~spl5_11 | spl5_23),
% 14.69/2.21    inference(avatar_contradiction_clause,[],[f1064])).
% 14.69/2.21  fof(f1064,plain,(
% 14.69/2.21    $false | (~spl5_11 | spl5_23)),
% 14.69/2.21    inference(subsumption_resolution,[],[f326,f661])).
% 14.69/2.21  fof(f661,plain,(
% 14.69/2.21    ~r2_hidden(sK0,sK2) | spl5_23),
% 14.69/2.21    inference(resolution,[],[f598,f96])).
% 14.69/2.21  fof(f598,plain,(
% 14.69/2.21    ~r1_tarski(k1_tarski(sK0),sK2) | spl5_23),
% 14.69/2.21    inference(avatar_component_clause,[],[f597])).
% 14.69/2.21  fof(f1057,plain,(
% 14.69/2.21    spl5_35 | spl5_32),
% 14.69/2.21    inference(avatar_split_clause,[],[f1010,f988,f1055])).
% 14.69/2.21  fof(f1010,plain,(
% 14.69/2.21    r1_xboole_0(k1_tarski(sK0),k1_xboole_0) | spl5_32),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f989,f81])).
% 14.69/2.21  fof(f1053,plain,(
% 14.69/2.21    ~spl5_34 | spl5_15),
% 14.69/2.21    inference(avatar_split_clause,[],[f446,f443,f1051])).
% 14.69/2.21  fof(f1051,plain,(
% 14.69/2.21    spl5_34 <=> r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))))))))),
% 14.69/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 14.69/2.21  fof(f446,plain,(
% 14.69/2.21    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))))) | spl5_15),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f444,f126])).
% 14.69/2.21  fof(f1009,plain,(
% 14.69/2.21    ~spl5_19 | ~spl5_33 | spl5_25),
% 14.69/2.21    inference(avatar_split_clause,[],[f871,f632,f1007,f527])).
% 14.69/2.21  fof(f1007,plain,(
% 14.69/2.21    spl5_33 <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))))),
% 14.69/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 14.69/2.21  fof(f871,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | ~r1_xboole_0(sK2,k1_tarski(sK1)) | spl5_25),
% 14.69/2.21    inference(forward_demodulation,[],[f641,f91])).
% 14.69/2.21  fof(f641,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_xboole_0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | ~r1_xboole_0(sK2,k1_tarski(sK1)) | spl5_25),
% 14.69/2.21    inference(superposition,[],[f633,f86])).
% 14.69/2.21  fof(f990,plain,(
% 14.69/2.21    ~spl5_32 | ~spl5_8 | spl5_11),
% 14.69/2.21    inference(avatar_split_clause,[],[f956,f257,f242,f988])).
% 14.69/2.21  fof(f956,plain,(
% 14.69/2.21    ~r2_hidden(sK0,k1_xboole_0) | (~spl5_8 | spl5_11)),
% 14.69/2.21    inference(backward_demodulation,[],[f574,f954])).
% 14.69/2.21  fof(f954,plain,(
% 14.69/2.21    k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK0)) | ~spl5_8),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f932,f86])).
% 14.69/2.21  fof(f574,plain,(
% 14.69/2.21    ~r2_hidden(sK0,k3_xboole_0(sK2,k1_tarski(sK0))) | spl5_11),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f120,f258,f85])).
% 14.69/2.21  fof(f933,plain,(
% 14.69/2.21    spl5_8 | ~spl5_10),
% 14.69/2.21    inference(avatar_split_clause,[],[f608,f253,f242])).
% 14.69/2.21  fof(f608,plain,(
% 14.69/2.21    r1_xboole_0(sK2,k1_tarski(sK0)) | ~spl5_10),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f587,f88])).
% 14.69/2.21  fof(f867,plain,(
% 14.69/2.21    spl5_31 | ~spl5_18),
% 14.69/2.21    inference(avatar_split_clause,[],[f730,f523,f865])).
% 14.69/2.21  fof(f730,plain,(
% 14.69/2.21    r1_tarski(k1_tarski(sK1),sK2) | ~spl5_18),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f524,f96])).
% 14.69/2.21  fof(f863,plain,(
% 14.69/2.21    ~spl5_30 | spl5_17 | ~spl5_18),
% 14.69/2.21    inference(avatar_split_clause,[],[f777,f523,f486,f861])).
% 14.69/2.21  fof(f777,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK1))) | (spl5_17 | ~spl5_18)),
% 14.69/2.21    inference(backward_demodulation,[],[f487,f720])).
% 14.69/2.21  fof(f720,plain,(
% 14.69/2.21    k1_tarski(sK1) = k3_xboole_0(sK2,k1_tarski(sK1)) | ~spl5_18),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f524,f80])).
% 14.69/2.21  fof(f719,plain,(
% 14.69/2.21    spl5_18 | spl5_27),
% 14.69/2.21    inference(avatar_split_clause,[],[f691,f676,f523])).
% 14.69/2.21  fof(f691,plain,(
% 14.69/2.21    r2_hidden(sK1,sK2) | spl5_27),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f677,f81])).
% 14.69/2.21  fof(f704,plain,(
% 14.69/2.21    ~spl5_29 | spl5_15 | spl5_27),
% 14.69/2.21    inference(avatar_split_clause,[],[f700,f676,f443,f702])).
% 14.69/2.21  fof(f702,plain,(
% 14.69/2.21    spl5_29 <=> k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_tarski(sK1)))))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))),
% 14.69/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 14.69/2.21  fof(f700,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_tarski(sK1)))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | (spl5_15 | spl5_27)),
% 14.69/2.21    inference(subsumption_resolution,[],[f450,f691])).
% 14.69/2.21  fof(f450,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_tarski(sK1)))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | ~r2_hidden(sK1,sK2) | spl5_15),
% 14.69/2.21    inference(superposition,[],[f444,f80])).
% 14.69/2.21  fof(f682,plain,(
% 14.69/2.21    spl5_18 | ~spl5_28 | ~spl5_10 | spl5_25),
% 14.69/2.21    inference(avatar_split_clause,[],[f657,f632,f253,f680,f523])).
% 14.69/2.21  fof(f657,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | r2_hidden(sK1,sK2) | (~spl5_10 | spl5_25)),
% 14.69/2.21    inference(forward_demodulation,[],[f656,f91])).
% 14.69/2.21  fof(f656,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | r2_hidden(sK1,sK2) | (~spl5_10 | spl5_25)),
% 14.69/2.21    inference(forward_demodulation,[],[f655,f611])).
% 14.69/2.21  fof(f611,plain,(
% 14.69/2.21    k1_tarski(sK0) = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))) | ~spl5_10),
% 14.69/2.21    inference(forward_demodulation,[],[f610,f94])).
% 14.69/2.21  fof(f610,plain,(
% 14.69/2.21    k1_tarski(sK0) = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2)) | ~spl5_10),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f587,f116])).
% 14.69/2.21  fof(f655,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | r2_hidden(sK1,sK2) | spl5_25),
% 14.69/2.21    inference(forward_demodulation,[],[f642,f94])).
% 14.69/2.21  fof(f642,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | r2_hidden(sK1,sK2) | spl5_25),
% 14.69/2.21    inference(superposition,[],[f633,f113])).
% 14.69/2.21  fof(f678,plain,(
% 14.69/2.21    ~spl5_27 | spl5_19),
% 14.69/2.21    inference(avatar_split_clause,[],[f604,f527,f676])).
% 14.69/2.21  fof(f604,plain,(
% 14.69/2.21    ~r1_xboole_0(k1_tarski(sK1),sK2) | spl5_19),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f528,f88])).
% 14.69/2.21  fof(f665,plain,(
% 14.69/2.21    spl5_18 | ~spl5_26 | ~spl5_10 | spl5_15),
% 14.69/2.21    inference(avatar_split_clause,[],[f629,f443,f253,f663,f523])).
% 14.69/2.21  fof(f629,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | r2_hidden(sK1,sK2) | (~spl5_10 | spl5_15)),
% 14.69/2.21    inference(forward_demodulation,[],[f622,f91])).
% 14.69/2.21  fof(f622,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | r2_hidden(sK1,sK2) | (~spl5_10 | spl5_15)),
% 14.69/2.21    inference(backward_demodulation,[],[f467,f611])).
% 14.69/2.21  fof(f467,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | r2_hidden(sK1,sK2) | spl5_15),
% 14.69/2.21    inference(forward_demodulation,[],[f453,f94])).
% 14.69/2.21  fof(f453,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | r2_hidden(sK1,sK2) | spl5_15),
% 14.69/2.21    inference(superposition,[],[f444,f113])).
% 14.69/2.21  fof(f634,plain,(
% 14.69/2.21    ~spl5_25 | spl5_2 | ~spl5_10),
% 14.69/2.21    inference(avatar_split_clause,[],[f625,f253,f144,f632])).
% 14.69/2.21  fof(f625,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0))))) | (spl5_2 | ~spl5_10)),
% 14.69/2.21    inference(forward_demodulation,[],[f612,f90])).
% 14.69/2.21  fof(f612,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(k5_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_tarski(sK0)))) | (spl5_2 | ~spl5_10)),
% 14.69/2.21    inference(backward_demodulation,[],[f145,f611])).
% 14.69/2.21  fof(f603,plain,(
% 14.69/2.21    ~spl5_19 | ~spl5_24 | spl5_15),
% 14.69/2.21    inference(avatar_split_clause,[],[f466,f443,f601,f527])).
% 14.69/2.21  fof(f601,plain,(
% 14.69/2.21    spl5_24 <=> k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))),
% 14.69/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 14.69/2.21  fof(f466,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,sK2))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | ~r1_xboole_0(sK2,k1_tarski(sK1)) | spl5_15),
% 14.69/2.21    inference(forward_demodulation,[],[f452,f91])).
% 14.69/2.21  fof(f452,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k1_xboole_0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | ~r1_xboole_0(sK2,k1_tarski(sK1)) | spl5_15),
% 14.69/2.21    inference(superposition,[],[f444,f86])).
% 14.69/2.21  fof(f599,plain,(
% 14.69/2.21    ~spl5_23 | spl5_11),
% 14.69/2.21    inference(avatar_split_clause,[],[f575,f257,f597])).
% 14.69/2.21  fof(f575,plain,(
% 14.69/2.21    ~r1_tarski(k1_tarski(sK0),sK2) | spl5_11),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f258,f95])).
% 14.69/2.21  fof(f595,plain,(
% 14.69/2.21    ~spl5_21 | ~spl5_22 | spl5_15),
% 14.69/2.21    inference(avatar_split_clause,[],[f451,f443,f593,f590])).
% 14.69/2.21  fof(f590,plain,(
% 14.69/2.21    spl5_21 <=> r1_tarski(sK2,k1_tarski(sK1))),
% 14.69/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 14.69/2.21  fof(f593,plain,(
% 14.69/2.21    spl5_22 <=> k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,sK2))))) = k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2))))),
% 14.69/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 14.69/2.21  fof(f451,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,sK2))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | ~r1_tarski(sK2,k1_tarski(sK1)) | spl5_15),
% 14.69/2.21    inference(superposition,[],[f444,f93])).
% 14.69/2.21  fof(f588,plain,(
% 14.69/2.21    spl5_10 | spl5_11),
% 14.69/2.21    inference(avatar_split_clause,[],[f565,f257,f253])).
% 14.69/2.21  fof(f565,plain,(
% 14.69/2.21    r1_xboole_0(k1_tarski(sK0),sK2) | spl5_11),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f258,f81])).
% 14.69/2.21  fof(f533,plain,(
% 14.69/2.21    spl5_20 | spl5_16),
% 14.69/2.21    inference(avatar_split_clause,[],[f498,f482,f531])).
% 14.69/2.21  fof(f498,plain,(
% 14.69/2.21    r1_xboole_0(k1_tarski(sK1),k1_xboole_0) | spl5_16),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f483,f81])).
% 14.69/2.21  fof(f529,plain,(
% 14.69/2.21    ~spl5_19 | ~spl5_17 | ~spl5_11 | spl5_15),
% 14.69/2.21    inference(avatar_split_clause,[],[f474,f443,f257,f486,f527])).
% 14.69/2.21  fof(f474,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | ~r1_xboole_0(sK2,k1_tarski(sK1)) | (~spl5_11 | spl5_15)),
% 14.69/2.21    inference(forward_demodulation,[],[f473,f91])).
% 14.69/2.21  fof(f473,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k1_xboole_0)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | ~r1_xboole_0(sK2,k1_tarski(sK1)) | (~spl5_11 | spl5_15)),
% 14.69/2.21    inference(forward_demodulation,[],[f472,f395])).
% 14.69/2.21  fof(f395,plain,(
% 14.69/2.21    k1_xboole_0 = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) | ~spl5_11),
% 14.69/2.21    inference(backward_demodulation,[],[f364,f344])).
% 14.69/2.21  fof(f344,plain,(
% 14.69/2.21    k1_tarski(sK0) = k3_xboole_0(sK2,k1_tarski(sK0)) | ~spl5_11),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f326,f80])).
% 14.69/2.21  fof(f364,plain,(
% 14.69/2.21    k1_xboole_0 = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))) | ~spl5_11),
% 14.69/2.21    inference(forward_demodulation,[],[f358,f94])).
% 14.69/2.21  fof(f358,plain,(
% 14.69/2.21    k1_xboole_0 = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2)) | ~spl5_11),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f326,f118])).
% 14.69/2.21  fof(f472,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | ~r1_xboole_0(sK2,k1_tarski(sK1)) | (~spl5_11 | spl5_15)),
% 14.69/2.21    inference(forward_demodulation,[],[f471,f344])).
% 14.69/2.21  fof(f471,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | ~r1_xboole_0(sK2,k1_tarski(sK1)) | spl5_15),
% 14.69/2.21    inference(forward_demodulation,[],[f454,f94])).
% 14.69/2.21  fof(f454,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | ~r1_xboole_0(sK2,k1_tarski(sK1)) | spl5_15),
% 14.69/2.21    inference(superposition,[],[f444,f116])).
% 14.69/2.21  fof(f525,plain,(
% 14.69/2.21    spl5_18 | ~spl5_17 | ~spl5_11 | spl5_15),
% 14.69/2.21    inference(avatar_split_clause,[],[f470,f443,f257,f486,f523])).
% 14.69/2.21  fof(f470,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | r2_hidden(sK1,sK2) | (~spl5_11 | spl5_15)),
% 14.69/2.21    inference(forward_demodulation,[],[f469,f91])).
% 14.69/2.21  fof(f469,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k1_xboole_0)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | r2_hidden(sK1,sK2) | (~spl5_11 | spl5_15)),
% 14.69/2.21    inference(forward_demodulation,[],[f468,f395])).
% 14.69/2.21  fof(f468,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | r2_hidden(sK1,sK2) | (~spl5_11 | spl5_15)),
% 14.69/2.21    inference(forward_demodulation,[],[f467,f344])).
% 14.69/2.21  fof(f488,plain,(
% 14.69/2.21    ~spl5_17 | spl5_4 | ~spl5_11 | spl5_15),
% 14.69/2.21    inference(avatar_split_clause,[],[f479,f443,f257,f186,f486])).
% 14.69/2.21  fof(f479,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k1_tarski(sK1)))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | (spl5_4 | ~spl5_11 | spl5_15)),
% 14.69/2.21    inference(forward_demodulation,[],[f478,f91])).
% 14.69/2.21  fof(f478,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k1_xboole_0)) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | (spl5_4 | ~spl5_11 | spl5_15)),
% 14.69/2.21    inference(subsumption_resolution,[],[f460,f359])).
% 14.69/2.21  fof(f359,plain,(
% 14.69/2.21    r2_hidden(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))) | (spl5_4 | ~spl5_11)),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f187,f326,f121])).
% 14.69/2.21  fof(f484,plain,(
% 14.69/2.21    ~spl5_16 | spl5_3 | ~spl5_11),
% 14.69/2.21    inference(avatar_split_clause,[],[f403,f257,f182,f482])).
% 14.69/2.21  fof(f403,plain,(
% 14.69/2.21    ~r2_hidden(sK1,k1_xboole_0) | (spl5_3 | ~spl5_11)),
% 14.69/2.21    inference(backward_demodulation,[],[f192,f395])).
% 14.69/2.21  fof(f445,plain,(
% 14.69/2.21    ~spl5_15 | spl5_2 | ~spl5_11),
% 14.69/2.21    inference(avatar_split_clause,[],[f377,f257,f144,f443])).
% 14.69/2.21  fof(f377,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_xboole_0,sK2)))) | (spl5_2 | ~spl5_11)),
% 14.69/2.21    inference(forward_demodulation,[],[f376,f91])).
% 14.69/2.21  fof(f376,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_xboole_0)))) | (spl5_2 | ~spl5_11)),
% 14.69/2.21    inference(forward_demodulation,[],[f365,f90])).
% 14.69/2.21  fof(f365,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(k5_xboole_0(sK2,k1_xboole_0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k1_xboole_0))) | (spl5_2 | ~spl5_11)),
% 14.69/2.21    inference(backward_demodulation,[],[f145,f364])).
% 14.69/2.21  fof(f343,plain,(
% 14.69/2.21    ~spl5_14 | spl5_2),
% 14.69/2.21    inference(avatar_split_clause,[],[f161,f144,f341])).
% 14.69/2.21  fof(f161,plain,(
% 14.69/2.21    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))))))) | spl5_2),
% 14.69/2.21    inference(forward_demodulation,[],[f160,f90])).
% 14.69/2.21  fof(f160,plain,(
% 14.69/2.21    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))),k1_tarski(k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))))))) | spl5_2),
% 14.69/2.21    inference(forward_demodulation,[],[f149,f90])).
% 14.69/2.21  fof(f149,plain,(
% 14.69/2.21    ~r2_hidden(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))),k1_tarski(k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))))) | spl5_2),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f145,f126])).
% 14.69/2.21  fof(f327,plain,(
% 14.69/2.21    spl5_11 | spl5_10),
% 14.69/2.21    inference(avatar_split_clause,[],[f289,f253,f257])).
% 14.69/2.21  fof(f289,plain,(
% 14.69/2.21    r2_hidden(sK0,sK2) | spl5_10),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f254,f81])).
% 14.69/2.21  fof(f325,plain,(
% 14.69/2.21    ~spl5_13 | spl5_2),
% 14.69/2.21    inference(avatar_split_clause,[],[f180,f144,f323])).
% 14.69/2.21  fof(f180,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))))))) | spl5_2),
% 14.69/2.21    inference(forward_demodulation,[],[f156,f90])).
% 14.69/2.21  fof(f156,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))))) | spl5_2),
% 14.69/2.21    inference(superposition,[],[f145,f90])).
% 14.69/2.21  fof(f288,plain,(
% 14.69/2.21    spl5_10 | spl5_11),
% 14.69/2.21    inference(avatar_contradiction_clause,[],[f287])).
% 14.69/2.21  fof(f287,plain,(
% 14.69/2.21    $false | (spl5_10 | spl5_11)),
% 14.69/2.21    inference(subsumption_resolution,[],[f263,f254])).
% 14.69/2.21  fof(f263,plain,(
% 14.69/2.21    r1_xboole_0(k1_tarski(sK0),sK2) | spl5_11),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f258,f81])).
% 14.69/2.21  fof(f282,plain,(
% 14.69/2.21    spl5_8 | spl5_11),
% 14.69/2.21    inference(avatar_contradiction_clause,[],[f281])).
% 14.69/2.21  fof(f281,plain,(
% 14.69/2.21    $false | (spl5_8 | spl5_11)),
% 14.69/2.21    inference(subsumption_resolution,[],[f275,f250])).
% 14.69/2.21  fof(f250,plain,(
% 14.69/2.21    sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK0))) | spl5_8),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f243,f115])).
% 14.69/2.21  fof(f275,plain,(
% 14.69/2.21    sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK0))) | spl5_11),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f258,f113])).
% 14.69/2.21  fof(f262,plain,(
% 14.69/2.21    ~spl5_11 | ~spl5_12 | spl5_2),
% 14.69/2.21    inference(avatar_split_clause,[],[f167,f144,f260,f257])).
% 14.69/2.21  fof(f260,plain,(
% 14.69/2.21    spl5_12 <=> k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))))))),
% 14.69/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 14.69/2.21  fof(f167,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))))))) | ~r2_hidden(sK0,sK2) | spl5_2),
% 14.69/2.21    inference(forward_demodulation,[],[f166,f90])).
% 14.69/2.21  fof(f166,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))))) | ~r2_hidden(sK0,sK2) | spl5_2),
% 14.69/2.21    inference(forward_demodulation,[],[f151,f90])).
% 14.69/2.21  fof(f151,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))))) | ~r2_hidden(sK0,sK2) | spl5_2),
% 14.69/2.21    inference(superposition,[],[f145,f80])).
% 14.69/2.21  fof(f255,plain,(
% 14.69/2.21    ~spl5_10 | spl5_8),
% 14.69/2.21    inference(avatar_split_clause,[],[f248,f242,f253])).
% 14.69/2.21  fof(f248,plain,(
% 14.69/2.21    ~r1_xboole_0(k1_tarski(sK0),sK2) | spl5_8),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f243,f88])).
% 14.69/2.21  fof(f247,plain,(
% 14.69/2.21    ~spl5_8 | ~spl5_9 | spl5_2),
% 14.69/2.21    inference(avatar_split_clause,[],[f173,f144,f245,f242])).
% 14.69/2.21  fof(f173,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k1_tarski(sK0))))))) | ~r1_xboole_0(sK2,k1_tarski(sK0)) | spl5_2),
% 14.69/2.21    inference(forward_demodulation,[],[f172,f91])).
% 14.69/2.21  fof(f172,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_xboole_0)))))) | ~r1_xboole_0(sK2,k1_tarski(sK0)) | spl5_2),
% 14.69/2.21    inference(forward_demodulation,[],[f171,f90])).
% 14.69/2.21  fof(f171,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_xboole_0),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_xboole_0))))) | ~r1_xboole_0(sK2,k1_tarski(sK0)) | spl5_2),
% 14.69/2.21    inference(forward_demodulation,[],[f153,f90])).
% 14.69/2.21  fof(f153,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_xboole_0)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k1_xboole_0)))) | ~r1_xboole_0(sK2,k1_tarski(sK0)) | spl5_2),
% 14.69/2.21    inference(superposition,[],[f145,f86])).
% 14.69/2.21  fof(f240,plain,(
% 14.69/2.21    spl5_7 | spl5_3),
% 14.69/2.21    inference(avatar_split_clause,[],[f189,f182,f238])).
% 14.69/2.21  fof(f238,plain,(
% 14.69/2.21    spl5_7 <=> r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 14.69/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 14.69/2.21  fof(f189,plain,(
% 14.69/2.21    r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) | spl5_3),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f183,f81])).
% 14.69/2.21  fof(f236,plain,(
% 14.69/2.21    ~spl5_5 | ~spl5_6 | spl5_2),
% 14.69/2.21    inference(avatar_split_clause,[],[f170,f144,f234,f231])).
% 14.69/2.21  fof(f231,plain,(
% 14.69/2.21    spl5_5 <=> r1_tarski(sK2,k1_tarski(sK0))),
% 14.69/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 14.69/2.21  fof(f234,plain,(
% 14.69/2.21    spl5_6 <=> k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) = k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(sK2,k1_tarski(sK0)))))))),
% 14.69/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 14.69/2.21  fof(f170,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(sK2,k1_tarski(sK0))))))) | ~r1_tarski(sK2,k1_tarski(sK0)) | spl5_2),
% 14.69/2.21    inference(forward_demodulation,[],[f169,f91])).
% 14.69/2.21  fof(f169,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),sK2)))))) | ~r1_tarski(sK2,k1_tarski(sK0)) | spl5_2),
% 14.69/2.21    inference(forward_demodulation,[],[f168,f90])).
% 14.69/2.21  fof(f168,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_tarski(sK0),sK2),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),sK2))))) | ~r1_tarski(sK2,k1_tarski(sK0)) | spl5_2),
% 14.69/2.21    inference(forward_demodulation,[],[f152,f90])).
% 14.69/2.21  fof(f152,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),sK2)),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),sK2)))) | ~r1_tarski(sK2,k1_tarski(sK0)) | spl5_2),
% 14.69/2.21    inference(superposition,[],[f145,f93])).
% 14.69/2.21  fof(f188,plain,(
% 14.69/2.21    ~spl5_4 | spl5_1),
% 14.69/2.21    inference(avatar_split_clause,[],[f140,f135,f186])).
% 14.69/2.21  fof(f135,plain,(
% 14.69/2.21    spl5_1 <=> sK0 = sK1),
% 14.69/2.21    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 14.69/2.21  fof(f140,plain,(
% 14.69/2.21    ~r2_hidden(sK0,k1_tarski(sK1)) | spl5_1),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f136,f126])).
% 14.69/2.21  fof(f136,plain,(
% 14.69/2.21    sK0 != sK1 | spl5_1),
% 14.69/2.21    inference(avatar_component_clause,[],[f135])).
% 14.69/2.21  fof(f184,plain,(
% 14.69/2.21    ~spl5_3 | spl5_1),
% 14.69/2.21    inference(avatar_split_clause,[],[f138,f135,f182])).
% 14.69/2.21  fof(f138,plain,(
% 14.69/2.21    ~r2_hidden(sK1,k1_tarski(sK0)) | spl5_1),
% 14.69/2.21    inference(unit_resulting_resolution,[],[f136,f126])).
% 14.69/2.21  fof(f146,plain,(
% 14.69/2.21    ~spl5_2),
% 14.69/2.21    inference(avatar_split_clause,[],[f133,f144])).
% 14.69/2.21  fof(f133,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0)))),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK2,k1_tarski(sK0))))))),
% 14.69/2.21    inference(forward_demodulation,[],[f132,f90])).
% 14.69/2.21  fof(f132,plain,(
% 14.69/2.21    k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(sK2,k1_tarski(sK0))),k3_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(sK2,k1_tarski(sK0)))))),
% 14.69/2.21    inference(forward_demodulation,[],[f131,f94])).
% 14.69/2.21  fof(f131,plain,(
% 14.69/2.21    k5_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(sK2,k1_tarski(sK0))),k3_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(sK2,k1_tarski(sK0))),k1_tarski(sK1))) != k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))))))),
% 14.69/2.21    inference(forward_demodulation,[],[f130,f94])).
% 14.69/2.21  fof(f130,plain,(
% 14.69/2.21    k5_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(sK2,k1_tarski(sK0))),k3_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(sK2,k1_tarski(sK0))),k1_tarski(sK1))) != k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),k1_tarski(sK0)))))),
% 14.69/2.21    inference(forward_demodulation,[],[f129,f90])).
% 14.69/2.21  fof(f129,plain,(
% 14.69/2.21    k5_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(sK2,k1_tarski(sK0))),k3_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(sK2,k1_tarski(sK0))),k1_tarski(sK1))) != k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),k1_tarski(sK0))))),
% 14.69/2.21    inference(forward_demodulation,[],[f103,f90])).
% 14.69/2.21  fof(f103,plain,(
% 14.69/2.21    k5_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(sK2,k1_tarski(sK0))),k3_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k1_tarski(sK0)),k3_xboole_0(sK2,k1_tarski(sK0))),k1_tarski(sK1))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),k1_tarski(sK0)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),k1_tarski(sK0)))),
% 14.69/2.21    inference(definition_unfolding,[],[f59,f73,f75,f75,f73])).
% 14.69/2.21  fof(f75,plain,(
% 14.69/2.21    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 14.69/2.21    inference(cnf_transformation,[],[f16])).
% 14.69/2.21  fof(f16,axiom,(
% 14.69/2.21    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 14.69/2.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 14.69/2.21  fof(f59,plain,(
% 14.69/2.21    k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))),
% 14.69/2.21    inference(cnf_transformation,[],[f38])).
% 14.69/2.21  fof(f38,plain,(
% 14.69/2.21    k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0)) & sK0 != sK1),
% 14.69/2.21    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f37])).
% 14.69/2.21  fof(f37,plain,(
% 14.69/2.21    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) & X0 != X1) => (k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0)) & sK0 != sK1)),
% 14.69/2.21    introduced(choice_axiom,[])).
% 14.69/2.21  fof(f31,plain,(
% 14.69/2.21    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) & X0 != X1)),
% 14.69/2.21    inference(ennf_transformation,[],[f30])).
% 14.69/2.21  fof(f30,negated_conjecture,(
% 14.69/2.21    ~! [X0,X1,X2] : (X0 != X1 => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)))),
% 14.69/2.21    inference(negated_conjecture,[],[f29])).
% 14.69/2.21  fof(f29,conjecture,(
% 14.69/2.21    ! [X0,X1,X2] : (X0 != X1 => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)))),
% 14.69/2.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_zfmisc_1)).
% 14.69/2.21  fof(f137,plain,(
% 14.69/2.21    ~spl5_1),
% 14.69/2.21    inference(avatar_split_clause,[],[f58,f135])).
% 14.69/2.21  fof(f58,plain,(
% 14.69/2.21    sK0 != sK1),
% 14.69/2.21    inference(cnf_transformation,[],[f38])).
% 14.69/2.21  % SZS output end Proof for theBenchmark
% 14.69/2.21  % (18602)------------------------------
% 14.69/2.21  % (18602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.69/2.21  % (18602)Termination reason: Refutation
% 14.69/2.21  
% 14.69/2.21  % (18602)Memory used [KB]: 9594
% 14.69/2.21  % (18602)Time elapsed: 1.463 s
% 14.69/2.21  % (18602)------------------------------
% 14.69/2.21  % (18602)------------------------------
% 14.69/2.22  % (18563)Success in time 1.863 s
%------------------------------------------------------------------------------
